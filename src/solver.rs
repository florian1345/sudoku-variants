//! This module contains the logic for solving Sudoku.
//!
//! Most importantly, this module contains the definition of the
//! [Solver](trait.Solver.html) trait and the
//! [BacktrackingSolver](struct.BacktrackingSolver.html) as a generally usable
//! implementation.

use crate::{Sudoku, SudokuGrid};
use crate::constraint::Constraint;

/// An enumeration of the different ways a Sudoku can be solveable. Note that
/// this may be relative to the solver, since an imperfect solver may be unable
/// to continue at some point, yielding `Solution::Ambiguous`, where the Sudoku
/// is actually uniquely solveable or impossible.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Solution {

    /// Indicates that the Sudoku is not solveable at all.
    Impossible,

    /// Indicates that the Sudoku has a unique solution, which is wrapped in
    /// this instance.
    Unique(SudokuGrid),

    /// Indicates that the Sudoku has multiple solutions or, at least, that the
    /// solver was unable to find a unique one or prove it is impossible.
    Ambiguous
}

impl Solution {

    /// Computes the union of two solutions. This is defined as follows:
    ///
    /// * If one solution is `Solution::Impossible`, the other one is returned.
    /// * If one solution is `Solution::Ambiguous` then the result is also
    /// ambiguous
    /// * If both solutions are `Solution::Unique` with solution grids `g1` and
    /// `g2`, then the result is `Solution::Unique(g1)` if `g1 == g2` and
    /// `Solution::Ambiguous` otherwise.
    pub fn union(self, other: Solution) -> Solution {
        match self {
            Solution::Impossible => other,
            Solution::Unique(g) =>
                match other {
                    Solution::Impossible => Solution::Unique(g),
                    Solution::Unique(other_g) =>
                        if g == other_g {
                            Solution::Unique(g)
                        }
                        else {
                            Solution::Ambiguous
                        }
                    Solution::Ambiguous => Solution::Ambiguous
                }
            Solution::Ambiguous => Solution::Ambiguous
        }
    }
}

/// A trait for structs which have the ability to solve Sudoku. Not all
/// implementers must be able to find a unique solution to every uniquely
/// solveable Sudoku, some solvers may be less powerful, similar to a less
/// experienced human solver. This may make sense to check whether some Sudoku
/// is solveable using some strategy.
pub trait Solver {

    /// Solves, or attempts to solve, the provided Sudoku. If the solver cannot
    /// prove that a Sudoku is impossible or uniquely solveable (either
    /// because it isn't or the solver is not powerful enough), they shall
    /// return `Solution::Ambiguous`.
    fn solve(&self, sudoku: &Sudoku<impl Constraint + Clone>) -> Solution;
}

/// A perfect [Solver](trait.Solver.html) which solves Sudoku by recursively
/// testing all valid numbers for each cell. This means two things:
///
/// * Its worst-case runtime is exponential, i.e. it may be very slow if the
/// Sudoku has many missing digits.
/// * It can provide the correct [Solution](enum.Solution.html) for any Sudoku
/// with any constraint.
pub struct BacktrackingSolver;

impl BacktrackingSolver {
    fn solve_rec(sudoku: &mut Sudoku<impl Constraint + Clone>, column: usize,
            row: usize) -> Solution {
        let size = sudoku.grid().size();
        let last_cell = row == size;

        if last_cell {
            return Solution::Unique(sudoku.grid().clone());
        }

        let next_column = (column + 1) % size;
        let next_row = if next_column == 0 { row + 1 } else { row };

        if let Some(_) = sudoku.grid().get_cell(column, row).unwrap() {
            BacktrackingSolver::solve_rec(sudoku, next_column, next_row)
        }
        else {
            let mut solution = Solution::Impossible;

            for number in 1..=size {
                if sudoku.is_valid_number(column, row, number).unwrap() {
                    sudoku.grid_mut().set_cell(column, row, number).unwrap();
                    let next_solution =
                        BacktrackingSolver::solve_rec(sudoku, next_column,
                            next_row);
                    sudoku.grid_mut().clear_cell(column, row).unwrap();
                    solution = solution.union(next_solution);

                    if solution == Solution::Ambiguous {
                        break;
                    }
                }
            }

            solution
        }
    }

    fn solve(sudoku: &mut Sudoku<impl Constraint + Clone>) -> Solution {
        BacktrackingSolver::solve_rec(sudoku, 0, 0)
    }
}

impl Solver for BacktrackingSolver {
    fn solve(&self, sudoku: &Sudoku<impl Constraint + Clone>) -> Solution {
        let mut clone = sudoku.clone();
        BacktrackingSolver::solve(&mut clone)
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::constraint::{
        AdjacentConsecutiveConstraint,
        CompositeConstraint,
        DefaultConstraint,
        DiagonalsConstraint,
        DiagonallyAdjacentConstraint,
        KingsMoveConstraint,
        KnightsMoveConstraint
    };

    fn test_solves_correctly<C>(puzzle: &str, solution: &str, constraint: C)
    where
        C: Constraint + Clone
    {
        let sudoku = Sudoku::parse(puzzle, constraint).unwrap();
        let solver = BacktrackingSolver;
        let found_solution = solver.solve(&sudoku);
        
        if let Solution::Unique(grid) = found_solution {
            let expected_grid = SudokuGrid::parse(solution).unwrap();
            assert_eq!(expected_grid, grid, "Solver gave wrong grid.");
        }
        else {
            panic!("Solveable sudoku marked as impossible or ambiguous.");
        }
    }

    // The example Sudoku are taken from the World Puzzle Federation Sudoku Grand Prix:

    // Classic + Diagonals: GP 2020 Round 8 (Puzzles 2 + 6)
    // Puzzles: https://gp.worldpuzzle.org/sites/default/files/Puzzles/2020/2020_SudokuRound8.pdf
    // Solutions: https://gp.worldpuzzle.org/sites/default/files/Puzzles/2020/2020_SudokuRound8_SB.pdf

    // No Knights Move: GP 2018 Round 1 (Puzzle 8)
    // Puzzle: https://gp.worldpuzzle.org/sites/default/files/Puzzles/2018/2018_SudokuRound1.pdf
    // Solution: https://gp.worldpuzzle.org/sites/default/files/Puzzles/2018/2018_SudokuRound1_SB.pdf

    // No Kings Move: GP 2017 Round 1 (Puzzle 11)
    // Puzzle: https://gp.worldpuzzle.org/sites/default/files/Puzzles/2017/2017_SudokuRound1.pdf
    // Solution: https://gp.worldpuzzle.org/sites/default/files/Puzzles/2017/2017_SudokuRound1_SB.pdf

    // No Adjacent Consecutive: GP 2019 Round 1 (Puzzle 7)
    // Puzzle: https://gp.worldpuzzle.org/sites/default/files/Puzzles/2019/2019_SudokuRound1.pdf
    // Solution: https://gp.worldpuzzle.org/sites/default/files/Puzzles/2019/2019_SudokuRound1_SB.pdf

    #[test]
    fn backtracking_solves_classic_sudoku() {
        let puzzle = "3x3;\
             , , , ,8,1, , , ,\
             , ,2, , ,7,8, , ,\
             ,5,3, , , ,1,7, ,\
            3,7, , , , , , , ,\
            6, , , , , , , ,3,\
             , , , , , , ,2,4,\
             ,6,9, , , ,2,3, ,\
             , ,5,9, , ,4, , ,\
             , , ,6,5, , , , ";
        let solution = "3x3;\
            7,4,6,2,8,1,3,5,9,\
            9,1,2,5,3,7,8,4,6,\
            8,5,3,4,9,6,1,7,2,\
            3,7,4,1,2,5,6,9,8,\
            6,2,8,7,4,9,5,1,3,\
            5,9,1,3,6,8,7,2,4,\
            1,6,9,8,7,4,2,3,5,\
            2,8,5,9,1,3,4,6,7,\
            4,3,7,6,5,2,9,8,1";
        test_solves_correctly(puzzle, solution, DefaultConstraint);
    }

    #[test]
    fn backtracking_solves_diagonals_sudoku() {
        let puzzle = "3x3;\
             ,1,2,3,4,5,6,7, ,\
             , , , , , , , , ,\
             , , , , , , , , ,\
            7, , , , , , , ,5,\
            2, , , , , , , ,1,\
            9, , , , , , , ,3,\
             , , , , , , , , ,\
             , , , , , , , , ,\
             ,3,4,5,6,7,8,9, ";
        let solution = "3x3;\
            8,1,2,3,4,5,6,7,9,\
            3,7,5,6,8,9,1,2,4,\
            4,9,6,1,7,2,3,5,8,\
            7,4,1,9,3,6,2,8,5,\
            2,6,3,7,5,8,9,4,1,\
            9,5,8,4,2,1,7,6,3,\
            5,2,7,8,9,3,4,1,6,\
            6,8,9,2,1,4,5,3,7,\
            1,3,4,5,6,7,8,9,2";
        test_solves_correctly(puzzle, solution,
            CompositeConstraint::new(DefaultConstraint, DiagonalsConstraint));
    }

    #[test]
    fn backtracking_solves_knights_move_sudoku() {
        let puzzle = "3x3;\
             ,8, ,1, ,5, , , ,\
            4, ,7, ,9, , , , ,\
             ,1, ,8, , , , , ,\
            1, ,8, , , , , ,5,\
             ,7, , , , , ,8, ,\
            5, , , , , ,3, ,4,\
             , , , , ,8, ,4, ,\
             , , , ,3, ,8, ,6,\
             , , ,5, ,4, ,3, ";
        let solution = "3x3;\
            2,8,3,1,4,5,6,9,7,\
            4,5,7,3,9,6,1,2,8,\
            9,1,6,8,2,7,4,5,3,\
            1,3,8,4,7,2,9,6,5,\
            6,7,4,9,5,3,2,8,1,\
            5,2,9,6,8,1,3,7,4,\
            3,9,1,7,6,8,5,4,2,\
            7,4,5,2,3,9,8,1,6,\
            8,6,2,5,1,4,7,3,9";
        test_solves_correctly(puzzle, solution, CompositeConstraint::new(
            DefaultConstraint, KnightsMoveConstraint));
    }

    #[test]
    fn backtracking_solves_kings_move_sudoku() {
        let puzzle = "3x3;\
             , , , ,2,1, , , ,\
             ,6,1, , , , ,3, ,\
             , , , , ,4, ,7, ,\
            3, ,7, , , , , , ,\
            2, , , ,5, , , ,7,\
             , , , , , ,5, ,8,\
             ,8, ,1, , , , , ,\
             ,3, , , , ,6,4, ,\
             , , ,7,6, , , , ";
        let solution = "3x3;\
            5,7,3,9,2,1,4,8,6,\
            4,6,1,5,8,7,2,3,9,\
            8,2,9,6,3,4,1,7,5,\
            3,5,7,2,1,8,9,6,4,\
            2,9,8,4,5,6,3,1,7,\
            1,4,6,3,7,9,5,2,8,\
            6,8,5,1,4,2,7,9,3,\
            7,3,2,8,9,5,6,4,1,\
            9,1,4,7,6,3,8,5,2";

        // Since the default constraint is enforced, KingsMoveConstraint and
        // DiagonallyAdjacentConstraint should yield the same result.

        test_solves_correctly(puzzle, solution,
            CompositeConstraint::new(DefaultConstraint, KingsMoveConstraint));
        test_solves_correctly(puzzle, solution, CompositeConstraint::new(
            DefaultConstraint, DiagonallyAdjacentConstraint));
    }

    #[test]
    fn backtracking_solves_adjacent_consecutive_sudoku() {
        let puzzle = "3x3;\
             , , , , , , , ,7,\
             , ,3,8, , , , , ,\
             ,4,6, , , , , , ,\
             ,7, , ,2, , , , ,\
             , , ,9,4,7, , , ,\
             , , , ,8, , ,5, ,\
             , , , , , , ,9, ,\
             , , , , ,4,6,2, ,\
            5, , , , , , , , ";
        let solution = "3x3;\
            2,5,8,4,1,6,9,3,7,\
            7,1,3,8,5,9,2,6,4,\
            9,4,6,3,7,2,5,8,1,\
            3,7,1,6,2,5,8,4,9,\
            8,2,5,9,4,7,3,1,6,\
            4,6,9,1,8,3,7,5,2,\
            6,8,2,7,3,1,4,9,5,\
            1,3,7,5,9,4,6,2,8,\
            5,9,4,2,6,8,1,7,3";
        test_solves_correctly(puzzle, solution,CompositeConstraint::new(
            DefaultConstraint, AdjacentConsecutiveConstraint));
    }
}
