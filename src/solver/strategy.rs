use crate::{Sudoku, SudokuGrid};
use crate::constraint::Constraint;
use crate::error::{SudokuError, SudokuResult};
use crate::solver::{Solution, Solver};
use crate::util::USizeSet;

/// Contains information about which numbers can go into the cells of a
/// [SudokuGrid](../../struct.SudokuGrid.html). This is analogous to the pencil
/// markings a human player would make. It is used by
/// [Strategies](trait.Strategy.html) to communicate the results of logical
/// reasoning.
///
/// Note that this struct itself does no reasoning, so the data provided by its
/// method is only as good as the data input by strategies.
#[derive(Clone)]
pub struct GridInfo {
    block_width: usize,
    block_height: usize,
    size: usize,
    cell_options: Vec<USizeSet>
}

impl GridInfo {

    /// Creates a new grid info from a
    /// [SudokuGrid](../../struct.SudokuGrid.html). The options for all cells
    /// that are empty in the provided grid are all digits, and the options for
    /// cells which are filled in the grid are only the digit in that cell.
    pub fn from_grid(grid: &SudokuGrid) -> GridInfo {
        let size = grid.size();

        GridInfo {
            block_width: grid.block_width(),
            block_height: grid.block_height(),
            size,
            cell_options: grid.cells().iter()
                .map(|c| match c {
                    Some(number) => USizeSet::singleton(1, size, *number).unwrap(),//hashset! { *number },
                    None => USizeSet::range(1, size).unwrap()
                })
                .collect()
        }
    }

    fn verified_index(&self, column: usize, row: usize)
            -> SudokuResult<usize> {
        let size = self.size;

        if column >= size || row >= size {
            Err(SudokuError::OutOfBounds)
        }
        else {
            Ok(crate::index(column, row, size))
        }
    }

    /// Gets a [USizeSet](../../util/struct.USizeSet.html) of the possible
    /// digits that can be entered into the cell at the given position
    /// according to this grid info.
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
        self.size
    }

    /// Gets a read-only reference to the vector storing the options for every
    /// cell in a [USizeSet](../../util/struct.USizeSet.html). The cells are in
    /// left-to-right, top-to-bottom order, where rows are together.
    pub fn cell_options(&self) -> &Vec<USizeSet> {
        &self.cell_options
    }

    /// Assigns the content of another grid info to this one, that is, after
    /// the operation this grid info will equal `other`. The dimensions must be
    /// equivalent.
    ///
    /// # Errors
    ///
    /// If `other` has different dimensions to this instance. In that case,
    /// `SudokuError::InvalidDimensions` is returned.
    pub fn assign(&mut self, other: &GridInfo) -> SudokuResult<()> {
        if self.block_width != other.block_width ||
                self.block_height != other.block_height {
            return Err(SudokuError::InvalidDimensions);
        }

        for i in 0..self.cell_options.len() {
            self.cell_options[i] = other.cell_options[i].clone();
        }

        Ok(())
    }
}

/// A trait for strategies, which use logical reasoning to restrict the
/// possibilities of a Sudoku.
pub trait Strategy {

    /// Applies this strategy to the given Sudoku. The strategy may rely on and
    /// modify the information in the given `grid_info`. It should not remove
    /// digits from the Sudoku or add options to any cell in the grid info.
    ///
    /// This method shall return `true` if and only if something has changed,
    /// that is, a digit has been entered in the Sudoku or an option has been
    /// removed from the grid info.
    ///
    /// # Arguments
    ///
    /// * `sudoku`: The [Sudoku](../../struct.Sudoku.html) over which this
    /// strategy shall reason. It is mutable so this method can enter digits.
    /// * `grid_info`: A [GridInfo](struct.GridInfo.html) instance that may
    /// store additional insights into the given Sudoku which have been gained
    /// in previous iterations and/or from different strategies. It is mutable
    /// so this method can remove options it can exclude.
    fn apply(&self, sudoku: &mut Sudoku<impl Constraint + Clone>,
        grid_info: &mut GridInfo) -> bool;
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
        let mut sudoku = sudoku.clone();
        let mut grid_info = GridInfo::from_grid(sudoku.grid());

        while !sudoku.grid().is_full() &&
            self.strategy.apply(&mut sudoku, &mut grid_info) { }

        if !sudoku.is_valid() {
            Solution::Impossible
        }
        else if sudoku.grid().is_full() {
            Solution::Unique(sudoku.grid().clone())
        }
        else if grid_info.cell_options().iter().any(|c| c.is_empty()) {
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
fn find_min_options(sudoku: &Sudoku<impl Constraint + Clone>,
        grid_info: &GridInfo) -> (usize, usize) {
    let size = grid_info.size();
    let mut min_options_column = 0usize;
    let mut min_options_row = 0usize;
    let mut min_options = size + 1;

    for row in 0..size {
        for column in 0..size {
            let cell = sudoku.grid().get_cell(column, row).unwrap();
            let options = grid_info.get_options(column, row).unwrap();

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

    fn solve_rec(&self, sudoku: &mut Sudoku<impl Constraint + Clone>,
            grid_info: &mut GridInfo) -> Solution {
        while {
            if let Some(solution) = to_solution(sudoku) {
                return solution;
            }

            self.strategy.apply(sudoku, grid_info)
        } { }

        let (min_options_column, min_options_row) =
            find_min_options(sudoku, grid_info);
        let options = grid_info
            .get_options(min_options_column, min_options_row)
            .unwrap()
            .iter();
        let mut solution = Solution::Impossible;
        //let mut sub_sudoku = sudoku.clone();
        //let mut sub_grid_info = grid_info.clone();

        for number in options {
            let mut sudoku = sudoku.clone();
            sudoku.grid_mut()
                .set_cell(min_options_column, min_options_row, number)
                .unwrap();
            //sub_sudoku.grid_mut().assign(sudoku.grid());
            //sub_sudoku.grid_mut()
            //    .set_cell(min_options_column, min_options_row, number)
            //    .unwrap();

            let mut grid_info = grid_info.clone();
            //sub_grid_info.assign(grid_info);
            let options_info = grid_info
                .get_options_mut(min_options_column, min_options_row)
                .unwrap();
            options_info.clear();
            options_info.insert(number).unwrap();

            let next_solution = self.solve_rec(&mut sudoku, &mut grid_info);
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
        self.solve_rec(&mut sudoku.clone(),
            &mut GridInfo::from_grid(sudoku.grid()))
    }
}

/// A [Strategy](trait.Strategy.html) which simply removes all options that
/// violate the constraint from each cell.
#[derive(Clone)]
pub struct ConstraintEnforcingStrategy;

impl Strategy for ConstraintEnforcingStrategy {

    fn apply(&self, sudoku: &mut Sudoku<impl Constraint + Clone>,
            grid_info: &mut GridInfo) -> bool {
        let size = grid_info.size();
        let mut changed = false;
        let mut options_to_remove = Vec::new();

        for row in 0..size {
            for column in 0..size {
                if let Some(_) = sudoku.grid().get_cell(column, row).unwrap() {
                    continue;
                }

                let options = grid_info.get_options_mut(column, row).unwrap();
                options_to_remove.clear();

                for option in options.iter() {
                    if !sudoku.is_valid_number(column, row, option).unwrap() {
                        options_to_remove.push(option);
                        changed = true;
                    }
                }

                for &option_to_remove in options_to_remove.iter() {
                    options.remove(option_to_remove).unwrap();
                }
            }
        }

        changed
    }
}

/// A [Strategy](trait.Strategy.html) which detects naked singles, that is,
/// cells which only have one possible value, and enters them into the Sudoku.
#[derive(Clone)]
pub struct NakedSingleStrategy;

impl Strategy for NakedSingleStrategy {

    fn apply(&self, sudoku: &mut Sudoku<impl Constraint + Clone>,
            grid_info: &mut GridInfo) -> bool {
        let size = grid_info.size();
        let mut changed = false;

        for row in 0..size {
            for column in 0..size {
                let grid = sudoku.grid_mut();
                let options = grid_info.get_options(column, row).unwrap();

                if grid.get_cell(column, row).unwrap() == None && options.len() == 1 {
                    let option = options.iter().next().unwrap();
                    grid.set_cell(column, row, option).unwrap();
                    changed = true;
                }
            }
        }

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
    fn apply(&self, sudoku: &mut Sudoku<impl Constraint + Clone>, grid_info: &mut GridInfo) -> bool {
        self.s1.apply(sudoku, grid_info) | self.s2.apply(sudoku, grid_info)
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

    use crate::Sudoku;
    use crate::constraint::DefaultConstraint;

    fn simple_strategy() -> impl Strategy {
        CompositeStrategy::new(ConstraintEnforcingStrategy,
            NakedSingleStrategy)
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
