use crate::constraint::Constraint;
use crate::solver::strategy::{Strategy, SudokuInfo};
use crate::util::USizeSet;

use std::collections::HashSet;

/// A [Strategy] which detects naked singles, that is, cells which only have
/// one possible value, and enters them into the Sudoku.
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

#[derive(Clone)]
enum Location {
    None,
    One(usize, usize),
    Multiple
}

impl std::fmt::Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Location::None => f.write_str("None"),
            Location::One(a, b) => f.write_str(format!("One({}, {})", a, b).as_str()),
            Location::Multiple => f.write_str("Multiple")
        }
    }
}

impl Location {
    fn union(&self, column: usize, row: usize) -> Location {
        match self {
            Location::None => Location::One(column, row),
            Location::One(_, _) => Location::Multiple,
            Location::Multiple => Location::Multiple
        }
    }
}

/// A [Strategy] which detects situations in which a digit can only go in one
/// cell of a group.
///
/// As a visualization, the cell marked with X in the following example is the
/// only one in its block that can be a 2 (using classic Sudoku rules).
///
/// ```text
/// ╔═══╤═══╦═══╤═══╗
/// ║   │   ║   │ 2 ║
/// ╟───┼───╫───┼───╢
/// ║ X │ 1 ║   │   ║
/// ╠═══╪═══╬═══╪═══╣
/// ║   │   ║   │   ║
/// ╟───┼───╫───┼───╢
/// ║   │   ║   │   ║
/// ╚═══╧═══╩═══╧═══╝
/// ```
#[derive(Clone)]
pub struct OnlyCellStrategy;

impl Strategy for OnlyCellStrategy {

    fn apply(&self, sudoku_info: &mut SudokuInfo<impl Constraint + Clone>)
            -> bool {
        let size = sudoku_info.size();
        let grid = sudoku_info.sudoku().grid();
        let groups = sudoku_info.sudoku().constraint().get_groups(grid);
        let mut changed = false;

        for group in groups {
            if group.len() < size {
                // For smaller groups, there is no guarantee that all digits
                // are present.
                continue;
            }

            let mut locations = vec![Location::None; size + 1];

            for (column, row) in group {
                if let Some(_) = sudoku_info.get_cell(column, row).unwrap() {
                    continue;
                }

                let options = sudoku_info.get_options(column, row).unwrap();

                for option in options.iter() {
                    let location = &locations[option];
                    locations[option] = location.union(column, row);
                }
            }

            for (number, location) in locations.into_iter().enumerate() {
                if let Location::One(column, row) = location {
                    sudoku_info.enqueue_enter_cell(column, row, number)
                        .unwrap();
                    changed = true;
                }
            }
        }

        sudoku_info.invalidate();
        changed
    }
}

/// A [Strategy] which searches groups for tuples, that is, 2 or more cells
/// that in total have as many options as there are cells in the tuple. It then
/// excludes all of these options from all cells in the group which are not a
/// part of the tuple.
///
/// As an example, consider the following configuration (with standard Sudoku
/// rules):
///
/// ```text
/// ╔═══╤═══╤═══╦═══╤═══╤═══╦═══╤═══╤═══╗
/// ║ A │ A │ A ║ 4 │ 5 │ 6 ║ 7 │ 8 │ 9 ║
/// ╟───┼───┼───╫───┼───┼───╫───┼───┼───╢
/// ║ B │ B │ B ║ 1 │ 2 │ 3 ║ 4 │ 5 │ 6 ║
/// ╟───┼───┼───╫───┼───┼───╫───┼───┼───╢
/// ║   │   │ X ║   │   │   ║   │   │   ║
/// ╠═══╪═══╪═══╬═══╪═══╪═══╬═══╪═══╪═══╣
/// ║   │   │ 4 ║   │   │   ║   │   │   ║
/// ╟───┼───┼───╫───┼───┼───╫───┼───┼───╢
/// ║   │   │ 5 ║   │   │   ║   │   │   ║
/// ╟───┼───┼───╫───┼───┼───╫───┼───┼───╢
/// ║   │   │   ║   │   │   ║   │   │   ║
/// ╠═══╪═══╪═══╬═══╪═══╪═══╬═══╪═══╪═══╣
/// ║   │   │   ║   │   │   ║   │   │   ║
/// ╟───┼───┼───╫───┼───┼───╫───┼───┼───╢
/// ║   │   │   ║   │   │   ║   │   │   ║
/// ╟───┼───┼───╫───┼───┼───╫───┼───┼───╢
/// ║   │   │   ║   │   │   ║   │   │   ║
/// ╚═══╧═══╧═══╩═══╧═══╧═══╩═══╧═══╧═══╝
/// ```
///
/// Because the first row already contains the digits 4-9, the cells marked
/// with A must contain the digits 1-3, meaning they are a triple (3-tuple).
/// Similarly, the cells marked with B must contain the digits 7-9. This
/// excludes the options 1-3 and 7-9 from the cell marked with X. The 4 and 5
/// in the third column then fix it to 6.
///
/// When creating a tuple strategy using [TupleStrategy::new], the maximum size
/// of tuples that are considered can be defined.
#[derive(Clone)]
pub struct TupleStrategy<F: Fn(usize) -> usize> {
    max_size_computer: F
}

impl<F: Fn(usize) -> usize> TupleStrategy<F> {

    /// Creates a new tuple strategy that considers tuples up to the size
    /// defined by `max_size_computer`. This closure receives the size of the
    /// grid and outputs the maximum size of tuples that this strategy shall
    /// consider.
    pub fn new(max_size_computer: F) -> TupleStrategy<F> {
        TupleStrategy {
            max_size_computer
        }
    }
}

#[derive(Clone)]
struct Tuple {
    cells: HashSet<(usize, usize)>,
    options: USizeSet
}

impl Tuple {
    fn new(size: usize) -> Tuple {
        Tuple {
            cells: HashSet::new(),
            options: USizeSet::new(1, size).unwrap()
        }
    }

    fn add_cell(&mut self, options: &USizeSet, column: usize, row: usize) {
        self.cells.insert((column, row));
        self.options |= options;
    }

    fn is_full(&self) -> bool {
        // Note: |options| < |cells| can only be the case if the Sudoku is
        // impossible.
        // TODO add a shortcut for returning impossible if a tuple with too
        // many cells is detected

        let options_len = self.options.len();
        options_len >= 2 && options_len <= self.cells.len()
    }
}

fn find_tuples_rec(sudoku_info: &SudokuInfo<impl Constraint + Clone>,
        group_rest: &[(usize, usize)], max_size: usize, mut curr_tuple: Tuple,
        accumulator: &mut Vec<Tuple>) {
    if curr_tuple.options.len() > max_size {
        return;
    }

    if curr_tuple.is_full() {
        accumulator.push(curr_tuple);
        return;
    }

    if let Some((next_column, next_row)) = group_rest.iter().cloned().next() {
        let next_options =
            sudoku_info.get_options(next_column, next_row).unwrap();
        let next_rest = &group_rest[1..];

        if next_options.len() > 1 {
            find_tuples_rec(sudoku_info, next_rest, max_size,
                curr_tuple.clone(), accumulator);
            curr_tuple.add_cell(next_options, next_column, next_row);
            find_tuples_rec(sudoku_info, next_rest, max_size, curr_tuple,
                accumulator);
        }
        else {
            find_tuples_rec(sudoku_info, next_rest, max_size, curr_tuple,
                accumulator);
        }
    }
}

fn find_tuples(sudoku_info: &SudokuInfo<impl Constraint + Clone>,
        group: &Vec<(usize, usize)>, max_size: usize) -> Vec<Tuple> {
    let mut result = Vec::new();
    find_tuples_rec(&sudoku_info, group, max_size,
        Tuple::new(sudoku_info.size()), &mut result);
    result
}

impl<F: Fn(usize) -> usize> Strategy for TupleStrategy<F> {

    fn apply(&self, sudoku_info: &mut SudokuInfo<impl Constraint + Clone>)
            -> bool {
        let mut changed = false;
        let grid = sudoku_info.sudoku().grid();
        let groups = sudoku_info.sudoku().constraint().get_groups(grid);
        let max_size = (self.max_size_computer)(sudoku_info.size());

        for group in groups {
            let tuples = find_tuples(&sudoku_info, &group, max_size);
            
            for tuple in tuples {
                for (column, row) in group.iter().cloned() {
                    if sudoku_info.get_cell(column, row).unwrap() == None &&
                            !tuple.cells.contains(&(column, row)) {
                        let mut cell_options =
                            sudoku_info.get_options_mut(column, row).unwrap();
                        let before_len = cell_options.len();
                        cell_options -= &tuple.options;
                        changed |= before_len != cell_options.len();
                    }
                }
            }
        }

        changed
    }
}

/// A [Strategy] which looks for cells with few options (up to a specified
/// maximum) and tries all of them. It then uses a wrapped strategy to find
/// deductions in all paths. If any of those deductions hold for all options,
/// they are stored in the metadata.
///
/// As an example, consider the following situation.
///
/// ```text
/// ╔═══╤═══╤═══╦═══╤═══╤═══╦═══╤═══╤═══╗
/// ║ 1 │ A │ 2 ║ 3 │ 4 │ 5 ║ 6 │ B │ 7 ║
/// ╟───┼───┼───╫───┼───┼───╫───┼───┼───╢
/// ║   │   │   ║   │   │   ║   │   │   ║
/// ╟───┼───┼───╫───┼───┼───╫───┼───┼───╢
/// ║   │   │   ║   │   │   ║   │   │   ║
/// ╠═══╪═══╪═══╬═══╪═══╪═══╬═══╪═══╪═══╣
/// ║ 2 │ 3 │ C ║   │   │   ║   │ Z │   ║
/// ╟───┼───┼───╫───┼───┼───╫───┼───┼───╢
/// ║ 4 │   │ 1 ║   │   │   ║   │   │   ║
/// ╟───┼───┼───╫───┼───┼───╫───┼───┼───╢
/// ║ 5 │ 6 │ 7 ║   │   │   ║   │   │   ║
/// ╠═══╪═══╪═══╬═══╪═══╪═══╬═══╪═══╪═══╣
/// ║   │   │   ║   │   │   ║   │   │   ║
/// ╟───┼───┼───╫───┼───┼───╫───┼───┼───╢
/// ║   │   │   ║   │   │   ║   │   │   ║
/// ╟───┼───┼───╫───┼───┼───╫───┼───┼───╢
/// ║   │   │   ║   │   │   ║   │   │   ║
/// ╚═══╧═══╧═══╩═══╧═══╧═══╩═══╧═══╧═══╝
/// ```
///
/// In this case, if A is an 8, then B must be a 9 by the [OnlyCellStrategy],
/// so Z cannot be a 9. If A is a 9, then C must be a 9 by the same strategy,
/// and consequently Z cannot be a 9 aswell. So, this strategy with an options
/// bound of at least 2 (since A can be 8 or 9), an [OnlyCellStrategy] as the
/// continuation strategy, and at least 1 application, can conclude that Z
/// cannot be a 9.
#[derive(Clone)]
pub struct BoundedOptionsBacktrackingStrategy<S: Strategy> {
    max_options: usize,
    max_applications: Option<usize>,
    continuation_strategy: S
}

impl<S: Strategy> BoundedOptionsBacktrackingStrategy<S> {

    /// Creates a new bounded options backtracking strategy where the number of
    /// applications of the continuation strategy is limited.
    ///
    /// # Arguments
    ///
    /// * `max_options`: The maximum number of options that may be present in a
    /// cell for this strategy to consider all of them.
    /// * `max_applications`: The maximum number of times the continuation
    /// strategy may be applied for each considered option before no further
    /// inference is done.
    /// * `continuation_strategy`: The [Strategy] with which each considered
    /// option is developed to find any inferences.
    pub fn new_limited_applications(max_options: usize,
            max_applications: usize, continuation_strategy: S)
            -> BoundedOptionsBacktrackingStrategy<S> {
        BoundedOptionsBacktrackingStrategy {
            max_options,
            max_applications: Some(max_applications),
            continuation_strategy
        }
    }

    /// Creates a new bounded options backtracking strategy where the number of
    /// applications of the continuation strategy is *not* limited.
    ///
    /// # Arguments
    ///
    /// * `max_options`: The maximum number of options that may be present in a
    /// cell for this strategy to consider all of them.
    /// * `continuation_strategy`: The [Strategy] with which each considered
    /// option is developed to find any inferences.
    pub fn new_unlimited_applications(max_options: usize,
            continuation_strategy: S)
            -> BoundedOptionsBacktrackingStrategy<S> {
        BoundedOptionsBacktrackingStrategy {
            max_options,
            max_applications: None,
            continuation_strategy
        }
    }

    fn apply_continuation(&self, sudoku_info: &mut SudokuInfo<impl Constraint + Clone>) {
        match self.max_applications {
            None => {
                while self.continuation_strategy.apply(sudoku_info) { }
            },
            Some(max) => {
                for _ in 0..max {
                    if !self.continuation_strategy.apply(sudoku_info) {
                        break;
                    }
                }
            }
        }
    }
}

impl<S: Strategy> Strategy for BoundedOptionsBacktrackingStrategy<S> {
    fn apply(&self, sudoku_info: &mut SudokuInfo<impl Constraint + Clone>)
            -> bool {
        let size = sudoku_info.size();
        let before_state = sudoku_info.clone();

        for column in 0..size {
            for row in 0..size {
                if let Some(_) = sudoku_info.get_cell(column, row).unwrap() {
                    continue;
                }

                let options = sudoku_info.get_options(column, row).unwrap();

                if options.len() > self.max_options {
                    continue;
                }

                let mut results = Vec::new();

                for option in options.iter() {
                    let mut sudoku_info = sudoku_info.clone();
                    sudoku_info.enter_cell(column, row, option).unwrap();
                    self.apply_continuation(&mut sudoku_info);
                    results.push(sudoku_info);
                }

                if results.len() == 0 {
                    continue;
                }

                let mut results_iter = results.into_iter();
                let first = results_iter.next().unwrap();
                let union = results_iter.fold(first,
                    |mut acc, x| {
                        acc.union_assign(&x).unwrap();
                        acc
                    });
                sudoku_info.intersect_assign(&union).unwrap();
            }
        }

        sudoku_info != &before_state
    }
}

// TODO BoundedCellsBacktrackingStrategy

/// A [Strategy]] which does nothing. This is to be used in backtracking
/// strategies to define that no further logic shall be applied after trying an
/// option.
#[derive(Clone)]
pub struct NoStrategy;

impl Strategy for NoStrategy {
    fn apply(&self, _: &mut SudokuInfo<impl Constraint + Clone>) -> bool {
        false
    }
}

/// A [Strategy] which uses two strategies by first applying one and then the
/// other on the output of the first one. If any child changed the state, this
/// strategy is defined to have changed the state aswell.
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
    use crate::solver::{Solution, Solver};
    use crate::solver::strategy::SudokuInfo;
    use crate::solver::strategy::solvers::*;

    fn naked_single_strategy_solver() -> StrategicSolver<impl Strategy> {
        StrategicSolver::new(NakedSingleStrategy)
    }

    fn only_cell_strategy_solver() -> StrategicSolver<impl Strategy> {
        StrategicSolver::new(OnlyCellStrategy)
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
    fn naked_single_strategy_solves_uniquely() {
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
        let solution = naked_single_strategy_solver().solve(&sudoku);
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
    fn naked_single_strategy_detects_impossibility() {
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
        let solution = naked_single_strategy_solver().solve(&sudoku);

        assert_eq!(Solution::Impossible, solution);
    }

    #[test]
    fn naked_single_strategy_unable_to_solve() {
        let sudoku = difficult_sudoku();
        let solution = naked_single_strategy_solver().solve(&sudoku);

        assert_eq!(Solution::Ambiguous, solution);
    }

    #[test]
    fn only_cell_strategy_solves_uniquely() {
        let sudoku = Sudoku::parse("3x3;\
             ,1, ,2, , ,7, ,9,\
             , ,6, ,8, ,3, , ,\
            8,2, , ,1,3, ,4,6,\
            4, ,5, ,7, ,6, ,1,\
            2,7,1,6, , , ,5, ,\
             ,9, , ,3, , , , ,\
             ,4, , ,5,8, ,6,7,\
            5, ,3,9,4, , ,2,8,\
            9,8, , , ,6,4,3, ", DefaultConstraint).unwrap();
        let solution = only_cell_strategy_solver().solve(&sudoku);
        let expected = Solution::Unique(SudokuGrid::parse("3x3;\
            3,1,4,2,6,5,7,8,9,\
            7,5,6,4,8,9,3,1,2,\
            8,2,9,7,1,3,5,4,6,\
            4,3,5,8,7,2,6,9,1,\
            2,7,1,6,9,4,8,5,3,\
            6,9,8,5,3,1,2,7,4,\
            1,4,2,3,5,8,9,6,7,\
            5,6,3,9,4,7,1,2,8,\
            9,8,7,1,2,6,4,3,5").unwrap());

        assert_eq!(expected, solution);
    }

    fn test_strategy_stronger_and_sound<C, W, S>(sudoku: Sudoku<C>,
        weak_strategy: W, strong_strategy: S, test_column: usize,
        test_row: usize, test_number: usize)
    where
        C: Constraint + Clone,
        W: Strategy,
        S: Strategy
    {
        let mut sudoku_info = SudokuInfo::from_sudoku(sudoku);

        while weak_strategy.apply(&mut sudoku_info) { }
        assert_eq!(None, sudoku_info.get_cell(test_column, test_row).unwrap());

        while strong_strategy.apply(&mut sudoku_info) { }
        assert_eq!(Some(test_number),
            sudoku_info.get_cell(test_column, test_row).unwrap());

        assert!(sudoku_info.sudoku().is_valid());
    }

    #[test]
    fn tuple_strategy_helps_naked_single_strategy() {
        // In this Sudoku, the cell in column 2, row 2 must be a 6, but that
        // can only be recognized once the options 1, 2, 7, and 8 have been
        // excluded by the tuple strategy.
        // Only tuples of size 2 need to be considered.

        let sudoku = Sudoku::parse("3x3;\
             , ,3,4,5,6,7,8,9,\
             , ,9,1,2,3,4,5,6,\
             , , , , , , , , ,\
             , ,4, , , , , , ,\
             , ,5, , , , , , ,\
             , , , , , , , , ,\
             , , , , , , , , ,\
             , , , , , , , , ,\
             , , , , , , , , ", DefaultConstraint).unwrap();
        let weak_strategy = NakedSingleStrategy;
        let strong_strategy = CompositeStrategy::new(
            TupleStrategy::new(|_| 2), NakedSingleStrategy);
        
        test_strategy_stronger_and_sound(sudoku, weak_strategy,
            strong_strategy, 2, 2, 6);
    }

    #[test]
    fn tuple_strategy_does_not_consider_too_large_tuples() {
        // This Sudoku is equivalent to the one above, but missing the 3 and 9
        // in column 2. This means that tuples of size 3 are necessary to
        // deduce the 6.

        let sudoku = Sudoku::parse("3x3;\
             , , ,4,5,6,7,8,9,\
             , , ,1,2,3,4,5,6,\
             , , , , , , , , ,\
             , ,4, , , , , , ,\
             , ,5, , , , , , ,\
             , , , , , , , , ,\
             , , , , , , , , ,\
             , , , , , , , , ,\
             , , , , , , , , ", DefaultConstraint).unwrap();
        let weak_strategy = CompositeStrategy::new(
            TupleStrategy::new(|_| 2), NakedSingleStrategy);
        let strong_strategy = CompositeStrategy::new(
            TupleStrategy::new(|_| 3), NakedSingleStrategy);
        
        test_strategy_stronger_and_sound(sudoku, weak_strategy,
            strong_strategy, 2, 2, 6);
    }

    #[test]
    fn strategic_backtracking_more_powerful() {
        let sudoku = difficult_sudoku();
        let solver = StrategicBacktrackingSolver::new(NakedSingleStrategy);
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

    #[test]
    fn bounded_options_backtracking_deduces_impossible_option() {
        let sudoku = Sudoku::parse("3x3;\
            1, ,2,3,4,5,6, ,7,\
             , , , , , , , , ,\
             , , , , , , , , ,\
            2,3, , , , , , , ,\
            4, ,1, , , , , , ,\
            5,6,7, , , , , , ,\
             , , , , , , , , ,\
             , , , , , , , , ,\
             , , , , , , , , ", DefaultConstraint).unwrap();
        let strategy =
            BoundedOptionsBacktrackingStrategy::new_limited_applications(2, 1,
                OnlyCellStrategy);
        let mut sudoku_info = SudokuInfo::from_sudoku(sudoku);
        
        assert!(strategy.apply(&mut sudoku_info));
        assert!(!sudoku_info.get_options(7, 3).unwrap().contains(8));
        assert!(!sudoku_info.get_options(7, 3).unwrap().contains(9));
    }

    #[test]
    fn bounded_options_backtracking_respects_application_limit() {
        let sudoku = Sudoku::parse("3x3;\
            1, ,2,3,4,5,6, ,7,\
             , , , , , , , , ,\
             , , , , , , , , ,\
            2,1, , , , , , , ,\
            3, ,6, , , , , , ,\
            4,5,7, , , , , , ,\
             , , , , , , , , ,\
             , , , , , , , , ,\
             , , , , , , , , ", DefaultConstraint).unwrap();
        let weak_strategy =
            BoundedOptionsBacktrackingStrategy::new_limited_applications(2, 1,
                NakedSingleStrategy);
        let strong_strategy =
            BoundedOptionsBacktrackingStrategy::new_limited_applications(2, 2,
                NakedSingleStrategy);
        let mut sudoku_info = SudokuInfo::from_sudoku(sudoku.clone());

        assert!(weak_strategy.apply(&mut sudoku_info));
        assert!(sudoku_info.get_options(7, 3).unwrap().contains(8));
        assert!(sudoku_info.get_options(7, 3).unwrap().contains(9));
        
        let mut sudoku_info = SudokuInfo::from_sudoku(sudoku);

        assert!(strong_strategy.apply(&mut sudoku_info));
        assert!(!sudoku_info.get_options(7, 3).unwrap().contains(8));
        assert!(!sudoku_info.get_options(7, 3).unwrap().contains(9));
    }

    #[test]
    fn bounded_options_backtracking_respects_option_limit() {
        let sudoku = Sudoku::parse("3x3;\
            1, ,2,3, ,4,5, ,6,\
             , , , , , , , , ,\
             , , ,7, , ,8, , ,\
            2, , ,3, , , , , ,\
            3, ,1,4, ,5, , , ,\
            4, ,5,2, ,1, , , ,\
             , , , , , , , , ,\
             , , , , , , , , ,\
             , , , , , , , , ", DefaultConstraint).unwrap();
        let weak_strategy =
            BoundedOptionsBacktrackingStrategy::new_unlimited_applications(2,
                OnlyCellStrategy);
        let strong_strategy =
            BoundedOptionsBacktrackingStrategy::new_unlimited_applications(3,
                OnlyCellStrategy);
        let mut sudoku_info = SudokuInfo::from_sudoku(sudoku.clone());
        
        assert!(weak_strategy.apply(&mut sudoku_info));
        assert!(sudoku_info.get_options(7, 3).unwrap().contains(9));
                
        let mut sudoku_info = SudokuInfo::from_sudoku(sudoku);
        
        assert!(strong_strategy.apply(&mut sudoku_info));
        assert!(!sudoku_info.get_options(7, 3).unwrap().contains(9));
    }

    // TODO BoundedCellsBacktrackingStrategy tests
}
