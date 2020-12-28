use crate::Sudoku;
use crate::constraint::Constraint;
use crate::solver::{Solution, Solver};
use crate::solver::strategy::{Strategy, SudokuInfo};

/// A partial [Solver] which uses a [Strategy] to solve a Sudoku as well as
/// possible. If it finds a contradiction, it will conclude that the Sudoku is
/// impossible. If it cannot solve it, it will resort to returning
/// `Solution::Ambiguous`. Only if the wrapped strategy is able to solve the
/// Sudoku completely, a `Solution::Unique` variant is returned.
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

/// A perfect [Solver] which uses a [Strategy] to accelerate the solving
/// process. Under the assumption that the strategy is correct, this should
/// yield the same result as a
/// [BacktrackingSolver](crate::solver::BacktrackingSolver). Note that using a
/// complicated strategy can also reduce performance if its utility is too low.
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
