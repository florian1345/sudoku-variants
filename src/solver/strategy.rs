use crate::Sudoku;
use crate::constraint::Constraint;
use crate::error::{SudokuError, SudokuResult};
use crate::solver::{Solution, Solver};
use crate::util::USizeSet;

/// Enriches a [Sudoku](../../struct.Sudoku.html) with additional information
/// about which numbers can go into the cells.. This is analogous to the pencil
/// markings a human player would make. It is used by
/// [Strategies](trait.Strategy.html) to communicate the results of logical
/// reasoning.
///
/// This struct already excludes options which violate the Sudoku's constraint,
/// unless unprocessed changes have been made.
#[derive(Clone)]
pub struct SudokuInfo<C: Constraint + Clone> {
    sudoku: Sudoku<C>,
    cell_options: Vec<USizeSet>,
    up_to_date: bool
}

impl<C: Constraint + Clone> SudokuInfo<C> {

    /// Creates a new Sudok info for a [Sudoku](../../struct.Sudoku.html). The
    /// options for all cells that are empty in the provided Sudoku are all
    /// valid digits, and the options for cells which are filled in the Sudoku
    /// are only the digit in that cell.
    pub fn from_sudoku(sudoku: Sudoku<C>) -> SudokuInfo<C> {
        let size = sudoku.grid().size();
        let mut cell_options = Vec::new();

        for row in 0..size {
            for column in 0..size {
                let cell = sudoku.grid().get_cell(column, row).unwrap();
                let options = match cell {
                    Some(number) =>
                        USizeSet::singleton(1, size, number).unwrap(),
                    None => {
                        let mut options = USizeSet::new(1, size).unwrap();

                        for option in 1..=size {
                            let is_valid = sudoku
                                .is_valid_number(column, row, option)
                                .unwrap();

                            if is_valid {
                                options.insert(option).unwrap();
                            }
                        }

                        options
                    }
                };

                cell_options.push(options);
            }
        }

        SudokuInfo {
            sudoku,
            cell_options,
            up_to_date: true
        }
    }

    fn verified_index(&self, column: usize, row: usize)
            -> SudokuResult<usize> {
        let size = self.size();

        if column >= size || row >= size {
            Err(SudokuError::OutOfBounds)
        }
        else {
            Ok(crate::index(column, row, size))
        }
    }

    /// Gets the content of the cell at the specified position.
    ///
    /// This is syntactic sugar for `x.sudoku().grid().get_cell(...)`.
    ///
    /// # Arguments
    ///
    /// * `column`: The column (x-coordinate) of the desired cell. Must be in
    /// the range `[0, size[`.
    /// * `row`: The row (y-coordinate) of the desired cell. Must be in the
    /// range `[0, size[`.
    ///
    /// # Errors
    ///
    /// If either `column` or `row` are not in the specified range. In that
    /// case, `SudokuError::OutOfBounds` is returned.
    pub fn get_cell(&self, column: usize, row: usize)
            -> SudokuResult<Option<usize>> {
        self.sudoku.grid().get_cell(column, row)
    }

    /// Sets the content of the cell at the specified position to the given
    /// number. If the cell was not empty, the old number will be overwritten.
    ///
    /// In contrast with [enter_cell](#method.enter_cell), this method does not
    /// remove cell options that are invalidated by the new digit. This is done
    /// for performance reasons to allow batching of multiple changes before
    /// updating the options. To ensure the cell options are up-to-date, call
    /// [invalidate](#method.invalidate) after making any changes.
    ///
    /// # Arguments
    ///
    /// * `column`: The column (x-coordinate) of the assigned cell. Must be in
    /// the range `[0, size[`.
    /// * `row`: The row (y-coordinate) of the assigned cell. Must be in the
    /// range `[0, size[`.
    /// * `number`: The number to assign to the specified cell. Must be in the
    /// range `[1, size]`.
    ///
    /// # Errors
    ///
    /// * `SudokuError::OutOfBounds` If either `column` or `row` are not in the
    /// specified range.
    /// * `SudokuError::InvalidNumber` If `number` is not in the specified
    /// range.
    pub fn enter_cell_no_update(&mut self, column: usize, row: usize,
            number: usize) -> SudokuResult<()> {
        self.sudoku.grid_mut().set_cell(column, row, number)?;
        self.up_to_date = false;
        Ok(())
    }

    /// Sets the content of the cell at the specified position to the given
    /// number. If the cell was not empty, the old number will be overwritten.
    ///
    /// In contrast with [enter_cell_no_update](#method.enter_cell_no_update),
    /// this method immediately removes all cell options that are invalidated
    /// by the new digit.
    ///
    /// # Arguments
    ///
    /// * `column`: The column (x-coordinate) of the assigned cell. Must be in
    /// the range `[0, size[`.
    /// * `row`: The row (y-coordinate) of the assigned cell. Must be in the
    /// range `[0, size[`.
    /// * `number`: The number to assign to the specified cell. Must be in the
    /// range `[1, size]`.
    ///
    /// # Errors
    ///
    /// * `SudokuError::OutOfBounds` If either `column` or `row` are not in the
    /// specified range.
    /// * `SudokuError::InvalidNumber` If `number` is not in the specified
    /// range.
    pub fn enter_cell(&mut self, column: usize, row: usize, number: usize)
            -> SudokuResult<()> {
        self.sudoku.grid_mut().set_cell(column, row, number)?;
        self.update();
        Ok(())
    }

    fn update(&mut self) {
        let size = self.size();
        let mut options_to_remove = Vec::new();

        for row in 0..size {
            for column in 0..size {
                let content = self.sudoku.grid().get_cell(column, row)
                    .unwrap();

                if let Some(_) = content {
                    continue;
                }

                // TODO find a way to use get_options without triggering the
                // borrow checker

                let options =
                    &mut self.cell_options[crate::index(column, row, size)];
                options_to_remove.clear();

                for option in options.iter() {
                    let is_valid = self.sudoku
                        .is_valid_number(column, row, option)
                        .unwrap();

                    if !is_valid {
                        options_to_remove.push(option);
                    }
                }

                for &option_to_remove in options_to_remove.iter() {
                    options.remove(option_to_remove).unwrap();
                }
            }
        }

        self.up_to_date = true;
    }

    /// Removes all cell options that have been invalidated by digits entered
    /// using [enter_cell_no_update](#method.enter_cell_no_update) which have
    /// not yet been processed. If there are no pending digits, nothing will be
    /// done.
    pub fn invalidate(&mut self) {
        if !self.up_to_date {
            self.update();
        }
    }

    /// Gets a [USizeSet](../../util/struct.USizeSet.html) of the possible
    /// digits that can be entered into the cell at the given position
    /// according to this grid info.
    ///
    /// Note that, because options are adapted to new digits lazily, this
    /// operation may require changes to this instance, namely if digits were
    /// changed since the last call to `get_options` or `get_options_mut`. This
    /// means a mutable reference to this instance is required.
    ///
    /// # Arguments
    ///
    /// * `column`: The column (x-coordinate) of the desired cell. Must be in
    /// the range `[0, size[`.
    /// * `row`: The row (y-coordinate) of the desired cell. Must be in the
    /// range `[0, size[`.
    ///
    /// # Errors
    ///
    /// If either `column` or `row` are not in the specified range. In that
    /// case, `SudokuError::OutOfBounds` is returned.
    pub fn get_options(&self, column: usize, row: usize)
            -> SudokuResult<&USizeSet> {
        let index = self.verified_index(column, row)?;
        Ok(&self.cell_options[index])
    }

    /// Gets a mutable reference to the
    /// [USizeSet](../../util/struct.USizeSet.html) that tracks the possible
    /// digits that can be entered into the cell at the given position
    /// according to this grid info.
    ///
    /// Note that, because options are adapted to new digits lazily, this
    /// operation may require changes to this instance, namely if digits were
    /// changed since the last call to `get_options` or `get_options_mut`.
    ///
    /// # Arguments
    ///
    /// * `column`: The column (x-coordinate) of the desired cell. Must be in
    /// the range `[0, size[`.
    /// * `row`: The row (y-coordinate) of the desired cell. Must be in the
    /// range `[0, size[`.
    ///
    /// # Errors
    ///
    /// If either `column` or `row` are not in the specified range. In that
    /// case, `SudokuError::OutOfBounds` is returned.
    pub fn get_options_mut(&mut self, column: usize, row: usize)
            -> SudokuResult<&mut USizeSet> {
        let index = self.verified_index(column, row)?;
        Ok(&mut self.cell_options[index])
    }

    /// Gets the total size of the grid for which this instance tracks
    /// information on one axis (horizontally or ertically). Since grids are
    /// always squares, this is guaranteed to be valid for both axes.
    pub fn size(&self) -> usize {
        self.sudoku.grid().size()
    }

    /// Gets a read-only reference to the vector storing the options for every
    /// cell in a [USizeSet](../../util/struct.USizeSet.html). The cells are in
    /// left-to-right, top-to-bottom order, where rows are together.
    pub fn cell_options(&self) -> &Vec<USizeSet> {
        &self.cell_options
    }

    /// Gets the width (number of columns) of one sub-block of the Sudoku. To
    /// ensure a square grid, this is also the number of blocks that compose
    /// the grid vertically.
    ///
    /// This is syntactic sugar for `x.sudoku().grid().block_width()`.
    pub fn block_width(&self) -> usize {
        self.sudoku.grid().block_width()
    }

    /// Gets the height (number of rows) of one sub-block of the Sudoku. To
    /// ensure a square grid, this is also the number of blocks that compose
    /// the grid horizontally.
    ///
    /// This is syntactic sugar for `x.sudoku().grid().block_height()`.
    pub fn block_height(&self) -> usize {
        self.sudoku.grid().block_height()
    }

    /// Assigns the content of another grid info to this one, that is, after
    /// the operation this grid info will equal `other`. The dimensions must be
    /// equivalent.
    ///
    /// # Errors
    ///
    /// If `other` has different dimensions to this instance. In that case,
    /// `SudokuError::InvalidDimensions` is returned.
    pub fn assign(&mut self, other: &SudokuInfo<C>) -> SudokuResult<()> {
        self.sudoku.grid_mut().assign(other.sudoku.grid())?;

        if self.block_width() != other.block_width() ||
                self.block_height() != other.block_height() {
            return Err(SudokuError::InvalidDimensions);
        }

        for i in 0..self.cell_options.len() {
            self.cell_options[i] = other.cell_options[i].clone();
        }

        Ok(())
    }

    /// Gets the [Sudoku](../../struct.Sudoku.html) for which this Sudoku info
    /// stores additional information.
    pub fn sudoku(&self) -> &Sudoku<C> {
        &self.sudoku
    }
}

/// A trait for strategies, which use logical reasoning to restrict the
/// possibilities of a Sudoku.
pub trait Strategy {

    /// Applies this strategy to the given Sudoku. The strategy may rely on and
    /// modify the information in the given `sudoku_info`. This instance is
    /// given to other strategies that participate in the solution and/or
    /// future iterations of the same strategy. It can thus be used to
    /// communicate insights.
    ///
    /// This method shall return `true` if and only if something has changed,
    /// that is, a digit has been entered or an option has been removed.
    fn apply(&self, sudoku_info: &mut SudokuInfo<impl Constraint + Clone>) -> bool;
}

/// A partial [Solver](../trait.Solver.html) which uses a
/// [Strategy](trait.Strategy.html) to solve a Sudoku as well as possible. If
/// it finds a contradiction, it will conclude that the Sudoku is impossible.
/// If it cannot solve it, it will resort to returning `Solution::Ambiguous`.
/// Only if the wrapped strategy is able to solve the Sudoku completely, a
/// `Solution::Unique` variant is returned.
pub struct StrategicSolver<S: Strategy> {
    strategy: S
}

impl<S: Strategy> StrategicSolver<S> {

    /// Creates a new strategic solver that uses the given `strategy` to
    /// attempt to solve Sudoku.
    pub fn new(strategy: S) -> StrategicSolver<S> {
        StrategicSolver { strategy }
    }
}

impl<S: Strategy> Solver for StrategicSolver<S> {
    fn solve(&self, sudoku: &Sudoku<impl Constraint + Clone>) -> Solution {
        let mut sudoku_info = SudokuInfo::from_sudoku(sudoku.clone());

        while !sudoku_info.sudoku().grid().is_full() &&
            self.strategy.apply(&mut sudoku_info) { }

        if !sudoku_info.sudoku().is_valid() {
            Solution::Impossible
        }
        else if sudoku_info.sudoku().grid().is_full() {
            Solution::Unique(sudoku_info.sudoku().grid().clone())
        }
        else if sudoku_info.cell_options().iter().any(|c| c.is_empty()) {
            Solution::Impossible
        }
        else {
            Solution::Ambiguous
        }
    }
}

impl<S: Strategy + Clone> Clone for StrategicSolver<S> {
    fn clone(&self) -> Self {
        StrategicSolver::new(self.strategy.clone())
    }
}

/// A perfect [Solver](../trait.Solver.html) which uses a
/// [Strategy](trait.Strategy.html) to accelerate the solving process. Under
/// the assumption that the strategy is correct, this should yield the same
/// result as a [BacktrackingSolver](../struct.BacktrackingSolver.html).
pub struct StrategicBacktrackingSolver<S: Strategy> {
    strategy: S
}

/// Finds the cell for which there are the fewest options and returns its
/// coordinates in the form `(column, row)`.
fn find_min_options<C: Constraint + Clone>(sudoku_info: &mut SudokuInfo<C>)
        -> (usize, usize) {
    let size = sudoku_info.size();
    let mut min_options_column = 0usize;
    let mut min_options_row = 0usize;
    let mut min_options = size + 1;

    for row in 0..size {
        for column in 0..size {
            let cell = sudoku_info.get_cell(column, row).unwrap();
            let options = sudoku_info.get_options(column, row).unwrap();

            if cell == None && options.len() < min_options {
                min_options_column = column;
                min_options_row = row;
                min_options = options.len();
            }
        }
    }

    (min_options_column, min_options_row)
}

fn to_solution(sudoku: &Sudoku<impl Constraint + Clone>) -> Option<Solution> {
    if sudoku.grid().is_full() {
        if sudoku.is_valid() {
            Some(Solution::Unique(sudoku.grid().clone()))
        }
        else {
            Some(Solution::Impossible)
        }
    }
    else {
        None
    }
}

impl<S: Strategy> StrategicBacktrackingSolver<S> {

    /// Creates a new strategic backtracing solver that uses the given
    /// `strategy`.
    pub fn new(strategy: S) -> StrategicBacktrackingSolver<S> {
        StrategicBacktrackingSolver { strategy }
    }

    fn solve_rec(&self, sudoku_info: &mut SudokuInfo<impl Constraint + Clone>) -> Solution {
        while {
            if let Some(solution) = to_solution(sudoku_info.sudoku()) {
                return solution;
            }

            self.strategy.apply(sudoku_info)
        } { }

        let (min_options_column, min_options_row) =
            find_min_options(sudoku_info);
        let options = sudoku_info
            .get_options(min_options_column, min_options_row)
            .unwrap()
            .iter();
        let mut solution = Solution::Impossible;

        for number in options {
            let mut sudoku_info = sudoku_info.clone();
            sudoku_info
                .enter_cell_no_update(min_options_column, min_options_row, number)
                .unwrap();
            let options_info = sudoku_info
                .get_options_mut(min_options_column, min_options_row)
                .unwrap();
            options_info.clear();
            options_info.insert(number).unwrap();

            let next_solution = self.solve_rec(&mut sudoku_info);
            solution = solution.union(next_solution);

            if solution == Solution::Ambiguous {
                break;
            }
        }

        solution
    }
}

impl<S: Strategy> Solver for StrategicBacktrackingSolver<S> {
    fn solve(&self, sudoku: &Sudoku<impl Constraint + Clone>) -> Solution {
        self.solve_rec(&mut SudokuInfo::from_sudoku(sudoku.clone()))
    }
}

/// A [Strategy](trait.Strategy.html) which detects naked singles, that is,
/// cells which only have one possible value, and enters them into the Sudoku.
#[derive(Clone)]
pub struct NakedSingleStrategy;

impl Strategy for NakedSingleStrategy {

    fn apply(&self, sudoku_info: &mut SudokuInfo<impl Constraint + Clone>)
            -> bool {
        let size = sudoku_info.size();
        let mut changed = false;

        for row in 0..size {
            for column in 0..size {
                let options = sudoku_info.get_options(column, row).unwrap();

                if sudoku_info.get_cell(column, row).unwrap() == None &&
                        options.len() == 1 {
                    let option = options.iter().next().unwrap();
                    sudoku_info.enter_cell_no_update(column, row, option).unwrap();
                    changed = true;
                }
            }
        }

        sudoku_info.invalidate();

        changed
    }
}

/// A [Strategy](trait.Strategy.html) which uses two strategies by first
/// applying one and then the other on the output of the first one. If any
/// child changed the state, this strategy is defined to have changed the state
/// aswell.
pub struct CompositeStrategy<S1: Strategy, S2: Strategy> {
    s1: S1,
    s2: S2
}

impl<S1: Strategy, S2: Strategy> CompositeStrategy<S1, S2> {

    /// Creates a new composite strategy from the two children strategies.
    ///
    /// # Arguments
    ///
    /// * `s1`: The strategy which is applied first.
    /// * `s2`: The strategy which is applied second.
    pub fn new(s1: S1, s2: S2) -> CompositeStrategy<S1, S2> {
        CompositeStrategy {
            s1,
            s2
        }
    }
}

impl<S1: Strategy, S2: Strategy> Strategy for CompositeStrategy<S1, S2> {
    fn apply(&self, sudoku_info: &mut SudokuInfo<impl Constraint + Clone>)
            -> bool {
        self.s1.apply(sudoku_info) | self.s2.apply(sudoku_info)
    }
}

impl<S1: Strategy + Clone, S2: Strategy + Clone> Clone for CompositeStrategy<S1, S2> {
    fn clone(&self) -> Self {
        CompositeStrategy::new(self.s1.clone(), self.s2.clone())
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::{Sudoku, SudokuGrid};
    use crate::constraint::DefaultConstraint;

    fn simple_strategy() -> impl Strategy {
        NakedSingleStrategy
    }

    fn simple_strategy_solver() -> StrategicSolver<impl Strategy> {
        StrategicSolver::new(simple_strategy())
    }

    fn solve_simply<C: Constraint + Clone>(sudoku: &Sudoku<C>) -> Solution {
        simple_strategy_solver().solve(&sudoku)
    }

    #[test]
    fn simple_strategy_solves_uniquely() {
        let sudoku = Sudoku::parse("3x3;\
             , ,1, , ,7,3,6, ,\
            7,2, , ,8, ,5, ,9,\
             ,8, , ,3,1, , , ,\
             , , ,6,7, , ,3,5,\
            9, ,5,8, , , ,7, ,\
            2,6, , ,1, , , ,4,\
            3, , ,1,5, , ,4,6,\
             ,7,4, , ,3, ,5,2,\
            5,1, ,7, ,4,8, , ", DefaultConstraint).unwrap();
        let solution = solve_simply(&sudoku);
        let expected = Solution::Unique(SudokuGrid::parse("3x3;\
            4,5,1,2,9,7,3,6,8,\
            7,2,3,4,8,6,5,1,9,\
            6,8,9,5,3,1,4,2,7,\
            1,4,8,6,7,9,2,3,5,\
            9,3,5,8,4,2,6,7,1,\
            2,6,7,3,1,5,9,8,4,\
            3,9,2,1,5,8,7,4,6,\
            8,7,4,9,6,3,1,5,2,\
            5,1,6,7,2,4,8,9,3").unwrap());

        assert_eq!(expected, solution);
    }

    #[test]
    fn simple_strategy_detects_impossibility() {
        let sudoku = Sudoku::parse("3x3;\
             , , , , , ,1, , ,\
             , , , , , ,2, , ,\
             , , , , , ,3, , ,\
             , , , , , , , , ,\
            1,2,3,4,5,6,7, , ,\
             , , , , , ,4, , ,\
            3,1,2,6,7,9, ,8, ,\
             , , , , , ,6, , ,\
             , , , , , ,9, , ", DefaultConstraint).unwrap();
        let solution = solve_simply(&sudoku);

        assert_eq!(Solution::Impossible, solution);
    }

    fn difficult_sudoku() -> Sudoku<DefaultConstraint> {
        // This Sudoku is taken from the World Puzzle Federation Sudoku GP 2020
        // Round 5 Puzzle 5
        // Puzzle: https://gp.worldpuzzle.org/sites/default/files/Puzzles/2020/2020_SudokuRound5.pdf
        // Solution: https://gp.worldpuzzle.org/sites/default/files/Puzzles/2020/2020_SudokuRound5_SB.pdf
        // The naked single strategy is insufficient to solve this puzzle.

        Sudoku::parse("3x3;\
             ,5, ,3, , , ,7, ,\
            1, , , ,2, ,8, , ,\
             ,2, ,4, ,9, , , ,\
             , ,3,1, , ,7, ,6,\
             ,4, , ,6, , ,5, ,\
            5, ,6, , ,3,4, , ,\
             , , ,8, ,2, ,3, ,\
             , ,7, ,9, , , ,2,\
             ,6, , , ,1, ,8, ", DefaultConstraint).unwrap()
    }

    #[test]
    fn simple_strategy_unable_to_solve() {
        let sudoku = difficult_sudoku();
        let solution = solve_simply(&sudoku);

        assert_eq!(Solution::Ambiguous, solution);
    }

    #[test]
    fn strategic_backtracking_more_powerful() {
        let sudoku = difficult_sudoku();
        let solver = StrategicBacktrackingSolver::new(simple_strategy());
        let solution = solver.solve(&sudoku);
        let expected = Solution::Unique(SudokuGrid::parse("3x3;\
            6,5,4,3,1,8,2,7,9,\
            1,3,9,7,2,6,8,4,5,\
            7,2,8,4,5,9,1,6,3,\
            8,9,3,1,4,5,7,2,6,\
            2,4,1,9,6,7,3,5,8,\
            5,7,6,2,8,3,4,9,1,\
            9,1,5,8,7,2,6,3,4,\
            3,8,7,6,9,4,5,1,2,\
            4,6,2,5,3,1,9,8,7").unwrap());

        assert_eq!(expected, solution);
    }
}
