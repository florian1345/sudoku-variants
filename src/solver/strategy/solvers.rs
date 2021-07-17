//! This module defines different [Solver]s related to strategies, in
//! particular the partial [StrategicSolver] and the perfect
//! [StrategicBacktrackingSolver]. All of them are re-exported in
//! [crate::solver::strategy], so you should not have to `use` anything from
//! this module directly.

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
    fn solve<C>(&self, sudoku: &Sudoku<C>) -> Solution
    where
        C: Constraint + Clone + 'static
    {
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

impl<S: Strategy + Clone> Clone for StrategicBacktrackingSolver<S> {
    fn clone(&self) -> StrategicBacktrackingSolver<S> {
        StrategicBacktrackingSolver {
            strategy: self.strategy.clone()
        }
    }
}

/// Finds the cell for which there are the fewest options and returns its
/// coordinates in the form `(column, row)`.
fn find_min_options<C: Constraint + Clone>(sudoku_info: &SudokuInfo<C>)
        -> (usize, usize, usize) {
    let size = sudoku_info.size();
    let mut min_options_column = 0usize;
    let mut min_options_row = 0usize;
    let mut min_options = size + 1;

    for row in 0..size {
        for column in 0..size {
            let cell = sudoku_info.get_cell(column, row).unwrap();
            let options = sudoku_info.get_options(column, row).unwrap();

            if cell.is_none() && options.len() < min_options {
                min_options_column = column;
                min_options_row = row;
                min_options = options.len();
            }
        }
    }

    (min_options_column, min_options_row, min_options)
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

    #[inline]
    fn solve_rec_step<C>(&self, sudoku_info: &mut SudokuInfo<C>,
        column: usize, row: usize, number: usize) -> Solution
    where
        C: Constraint + Clone + 'static
    {
        sudoku_info.enter_cell(column, row, number)
            .unwrap();
        self.solve_rec(sudoku_info)
    }

    fn solve_rec<C>(&self, sudoku_info: &mut SudokuInfo<C>) -> Solution
    where
        C: Constraint + Clone + 'static
    {
        while {
            if let Some(solution) = to_solution(sudoku_info.sudoku()) {
                return solution;
            }

            self.strategy.apply(sudoku_info)
        } { }

        let (column, row, min_options) =
            find_min_options(sudoku_info);

        if min_options == 0 {
            return Solution::Impossible;
        }

        let mut options = sudoku_info
            .get_options(column, row)
            .unwrap()
            .iter();

        if min_options == 1 {
            let number = options.next().unwrap();
            sudoku_info.enter_cell(column, row, number)
                .unwrap();
            return self.solve_rec(sudoku_info);
        }

        let mut solution = Solution::Impossible;
        let mut i = 1usize;

        while i < min_options {
            let number = options.next().unwrap();
            let next_solution = self.solve_rec_step(
                &mut sudoku_info.clone(), column, row, number);
            solution = solution.union(next_solution);

            if solution == Solution::Ambiguous {
                break;
            }

            i += 1;
        }

        let number = options.next().unwrap();
        let next_solution =
            self.solve_rec_step(sudoku_info, column, row, number);
        solution = solution.union(next_solution);

        solution
    }
}

impl<S: Strategy> Solver for StrategicBacktrackingSolver<S> {
    fn solve<C>(&self, sudoku: &Sudoku<C>) -> Solution
    where
        C: Constraint + Clone + 'static
    {
        self.solve_rec(&mut SudokuInfo::from_sudoku(sudoku.clone()))
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::SudokuGrid;
    use crate::constraint::{
        AdjacentConsecutiveConstraint,
        CompositeConstraint,
        DefaultConstraint,
        DiagonalsConstraint,
        KingsMoveConstraint,
        KnightsMoveConstraint
    };
    use crate::solver::strategy::{
        BoundedOptionsBacktrackingStrategy,
        BoundedCellsBacktrackingStrategy,
        CompositeStrategy,
        NakedSingleStrategy,
        OnlyCellStrategy,
        TupleStrategy
    };

    fn naked_single_strategy_solver() -> StrategicSolver<impl Strategy> {
        StrategicSolver::new(NakedSingleStrategy)
    }

    fn only_cell_strategy_solver() -> StrategicSolver<impl Strategy> {
        StrategicSolver::new(OnlyCellStrategy)
    }
    
    fn complex_composite_strategy_solver() -> StrategicSolver<impl Strategy> {
        let strategy = CompositeStrategy::new(NakedSingleStrategy,
            CompositeStrategy::new(OnlyCellStrategy,
                CompositeStrategy::new(TupleStrategy::new(|_| 7),
                    CompositeStrategy::new(
                        BoundedOptionsBacktrackingStrategy::new(|_| 2,
                            |_| Some(1), OnlyCellStrategy),
                        BoundedCellsBacktrackingStrategy::new(|_| 2,
                            |_| Some(1), OnlyCellStrategy)))));
        StrategicSolver::new(strategy)
    }

    fn complex_tuple_strategy_solver() -> StrategicSolver<impl Strategy> {
        StrategicSolver::new((
            NakedSingleStrategy,
            OnlyCellStrategy,
            TupleStrategy::new(|_| 7),
            BoundedOptionsBacktrackingStrategy::new(|_| 2, |_| Some(1), OnlyCellStrategy),
            BoundedCellsBacktrackingStrategy::new(|_| 2, |_| Some(1), OnlyCellStrategy),
        ))
    }

    fn complex_strategic_backtracking_solver()
            -> StrategicBacktrackingSolver<impl Strategy> {
        // This solver is used in the benchmark, where an error was found.

        StrategicBacktrackingSolver::new(CompositeStrategy::new(
            CompositeStrategy::new(
                NakedSingleStrategy, OnlyCellStrategy),
            CompositeStrategy::new(
                TupleStrategy::new(|size| size - 2),
                CompositeStrategy::new(
                    BoundedCellsBacktrackingStrategy::new(|size| size - 2,
                        |_| Some(1), OnlyCellStrategy),
                    BoundedOptionsBacktrackingStrategy::new(|_| 2,
                        |_| Some(1), CompositeStrategy::new(
                            NakedSingleStrategy, OnlyCellStrategy
                        )
                    )
                )
            )
        ))
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

    fn assert_can_solve_difficult_sudoku(solver: impl Solver) {
        let sudoku = difficult_sudoku();
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

    #[test]
    fn strategic_backtracking_more_powerful() {
        let solver = StrategicBacktrackingSolver::new(NakedSingleStrategy);
        assert_can_solve_difficult_sudoku(solver);
    }

    #[test]
    fn complex_composite_strategy_solves_difficult_sudoku() {
        let solver = complex_composite_strategy_solver();
        assert_can_solve_difficult_sudoku(solver);
    }
    
    #[test]
    fn complex_tuple_strategy_solves_difficult_sudoku() {
        let solver = complex_tuple_strategy_solver();
        assert_can_solve_difficult_sudoku(solver);
    }

    #[test]
    fn complex_strategic_backtracking_is_sound_default() {
        let sudoku = Sudoku::parse("3x3;
             , , , , ,7,3, , ,\
             ,1,2, , , ,5,4, ,\
             , ,3,4, , , ,1, ,\
             , ,5,6, , , ,8, ,\
             , , , , , , , , ,\
            7, , , , ,2,4, , ,\
            6,4,1, , , ,8, , ,\
            5,3, , , ,6,7, , ,\
             , , , , ,9, , , ", DefaultConstraint).unwrap();
        let solution = complex_strategic_backtracking_solver().solve(&sudoku);
        let expected = Solution::Unique(SudokuGrid::parse("3x3;
            4,5,6,2,1,7,3,9,8,\
            8,1,2,9,6,3,5,4,7,\
            9,7,3,4,5,8,6,1,2,\
            1,2,5,6,7,4,9,8,3,\
            3,6,4,8,9,1,2,7,5,\
            7,9,8,5,3,2,4,6,1,\
            6,4,1,7,2,5,8,3,9,\
            5,3,9,1,8,6,7,2,4,\
            2,8,7,3,4,9,1,5,6").unwrap());

        assert_eq!(expected, solution);
    }

    #[test]
    fn complex_strategic_backtracking_is_sound_diagonals() {
        let sudoku = Sudoku::parse("3x3;
             , , , ,3, , , , ,\
             , , ,7, ,6, , , ,\
             , ,4, , , ,2, , ,\
             ,4, , , , , ,1, ,\
            1, , , , , , , ,6,\
             ,2, , , , , ,7, ,\
             , ,9, , , ,5, , ,\
             , , ,2, ,1, , , ,\
             , , , ,7, , , , ",
            CompositeConstraint::new(DefaultConstraint, DiagonalsConstraint))
            .unwrap();
        let solution = complex_strategic_backtracking_solver().solve(&sudoku);
        let expected = Solution::Unique(SudokuGrid::parse("3x3;
            7,9,6,5,3,2,1,8,4,\
            8,1,2,7,4,6,3,5,9,\
            5,3,4,9,1,8,2,6,7,\
            9,4,3,6,2,7,8,1,5,\
            1,5,7,3,8,4,9,2,6,\
            6,2,8,1,5,9,4,7,3,\
            2,7,9,8,6,3,5,4,1,\
            4,6,5,2,9,1,7,3,8,\
            3,8,1,4,7,5,6,9,2").unwrap());

        assert_eq!(expected, solution);
    }

    #[test]
    fn complex_strategic_backtracking_is_sound_knights_move() {
        let sudoku = Sudoku::parse("3x3;
            5,3, , , , , ,8,7,\
            1, , , , , , , ,9,\
             , , ,7, ,2, , , ,\
             , , , , ,4,7, , ,\
             , , , , , , , , ,\
             , ,4,6, , , , , ,\
             , , ,3, ,8, , , ,\
            7, , , , , , , ,2,\
            9,4, , , , , ,3,5",
            CompositeConstraint::new(DefaultConstraint, KnightsMoveConstraint))
            .unwrap();
        let solution = complex_strategic_backtracking_solver().solve(&sudoku);
        let expected = Solution::Unique(SudokuGrid::parse("3x3;
            5,3,2,4,9,1,6,8,7,\
            1,8,7,5,3,6,2,4,9,\
            4,9,6,7,8,2,5,1,3,\
            3,6,9,8,2,4,7,5,1,\
            8,7,5,9,1,3,4,2,6,\
            2,1,4,6,7,5,3,9,8,\
            6,2,1,3,5,8,9,7,4,\
            7,5,3,1,4,9,8,6,2,\
            9,4,8,2,6,7,1,3,5").unwrap());

        assert_eq!(expected, solution);
    }

    #[test]
    fn complex_strategic_backtracking_is_sound_kings_move() {
        let sudoku = Sudoku::parse("3x3;
             ,8, , , , , ,9, ,\
            3,2, , , , , ,5,4,\
             , , ,2, ,5, , , ,\
             , ,7,8, ,6,4, , ,\
             , , , , , , , , ,\
             , ,6,3, ,1,9, , ,\
             , , ,7, ,8, , , ,\
            4,7, , , , , ,6,5,\
             ,9, , , , , ,1, ",
            CompositeConstraint::new(DefaultConstraint, KingsMoveConstraint))
            .unwrap();
        let solution = complex_strategic_backtracking_solver().solve(&sudoku);
        let expected = Solution::Unique(SudokuGrid::parse("3x3;
            7,8,5,6,4,3,1,9,2,\
            3,2,1,9,8,7,6,5,4,\
            9,6,4,2,1,5,8,7,3,\
            5,3,7,8,9,6,4,2,1,\
            8,1,9,4,7,2,5,3,6,\
            2,4,6,3,5,1,9,8,7,\
            1,5,2,7,6,8,3,4,9,\
            4,7,8,1,3,9,2,6,5,\
            6,9,3,5,2,4,7,1,8").unwrap());

        assert_eq!(expected, solution);
    }

    #[test]
    fn complex_strategic_backtracking_is_sound_adjacent_consecutive() {
        let sudoku = Sudoku::parse("3x3;
             , , , , , , , , ,\
             , , , ,4, , , , ,\
             , ,7, ,6, ,5, , ,\
             , , , ,1, , , , ,\
             ,9,4,8, ,5,2,6, ,\
             , , , ,9, , , , ,\
             , ,1, ,2, ,4, , ,\
             , , , ,8, , , , ,\
             , , , , , , , , ",
            CompositeConstraint::new(DefaultConstraint, 
                AdjacentConsecutiveConstraint))
            .unwrap();
        let solution = complex_strategic_backtracking_solver().solve(&sudoku);
        let expected = Solution::Unique(SudokuGrid::parse("3x3;
            2,4,9,5,7,3,8,1,6,
            6,1,5,2,4,8,3,7,9,
            8,3,7,9,6,1,5,2,4,
            3,5,2,6,1,7,9,4,8,
            7,9,4,8,3,5,2,6,1,
            1,6,8,4,9,2,7,3,5,
            5,8,1,7,2,6,4,9,3,
            9,2,6,3,8,4,1,5,7,
            4,7,3,1,5,9,6,8,2").unwrap());

        assert_eq!(expected, solution);
    }
}
