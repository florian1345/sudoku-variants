//! This module contains [Strategy] implementations specific to the
//! [KillerConstraint]. They are re-exported in the
//! [specific](crate::solver::strategy::specific) module, so they do not have
//! to be referenced from this module directly.

use crate::constraint::{
    Constraint,
    KillerCage,
    KillerConstraint,
    Subconstraint
};
use crate::solver::strategy::{Strategy, SudokuInfo};
use crate::solver::strategy::specific::sum;
use crate::util::USizeSet;

/// A [Strategy] specifically for the [KillerConstraint], which, for each cage,
/// enumerates the possibilities and eliminates all options which are not used
/// in at least one possibility.
///
/// As an example, consider the following Killer cage (in a Sudoku with the
/// [DefaultConstraint](crate::constraint::DefaultConstraint) as well as the
/// [KillerConstraint]):
///
/// ```text
/// ╔═══════╤═══════╦═══════╤═══════╗
/// ║╭8─────┼───────╫──────╮│       ║
/// ║│  X   │   Y   ║   Y  ││       ║
/// ║╰──────┼───────╫──────╯│       ║
/// ╟───────┼───────╫───────┼───────╢
/// ║       │       ║       │       ║
/// ║       │       ║       │       ║
/// ║       │       ║       │       ║
/// ╠═══════╪═══════╬═══════╪═══════╣
/// ║       │       ║       │       ║
/// ║       │   4   ║       │       ║
/// ║       │       ║       │       ║
/// ╟───────┼───────╫───────┼───────╢
/// ║       │       ║       │       ║
/// ║       │       ║   4   │       ║
/// ║       │       ║       │       ║
/// ╚═══════╧═══════╩═══════╧═══════╝
/// ```
///
/// This strategy would be able to deduce that the cell marked with `X` cannot
/// be a 1. This is because that would require a 4 in either of the cells
/// marked with Y, which is not possible due to the 4s in the lower two rows.
pub struct KillerCagePossibilitiesStrategy;

fn process_cage<C>(cage: &KillerCage, sudoku_info: &mut SudokuInfo<C>) -> bool
where
    C: Constraint + Clone + 'static
{
    let size = sudoku_info.size();
    let mut numbers = USizeSet::new(1, size).unwrap();
    let mut sum = 0;
    let mut missing_options = Vec::new();
    let mut missing_cells = Vec::new();

    for &(column, row) in cage.group() {
        if let Some(n) = sudoku_info.get_cell(column, row).unwrap() {
            numbers.insert(n).unwrap();
            sum += n;
        }
        else {
            missing_options.push(
                sudoku_info.get_options(column, row).unwrap());
            missing_cells.push((column, row));
        }
    }

    if missing_cells.is_empty() {
        return false;
    }

    let new_options =
        sum::find_options_unique(missing_options.into_iter(), sum, cage.sum());
    let mut changed = false;

    for (new_options, &(column, row))
    in new_options.iter().zip(missing_cells.iter()) {
        let options =
            sudoku_info.get_options_mut(column, row).unwrap();
        changed |= options.intersect_assign(new_options).unwrap();
    }

    changed
}

impl Strategy for KillerCagePossibilitiesStrategy {
    fn apply<C>(&self, sudoku_info: &mut SudokuInfo<C>) -> bool
    where
        C: Constraint + Clone + 'static
    {
        let c = sudoku_info.sudoku().constraint();

        if let Some(killer) = c.get_subconstraint::<KillerConstraint>() {
            let mut changed = false;
            let cages = killer.cages().clone();

            for cage in cages {
                changed |= process_cage(&cage, sudoku_info);
            }

            changed
        }
        else {
            panic!("KillerCageSumStrategy deployed on non-killer Sudoku.")
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::{Sudoku, SudokuGrid};
    use crate::constraint::{
        CompositeConstraint,
        DefaultConstraint,
        KillerCage,
        KillerConstraint
    };
    use crate::solver::{Solution, Solver};
    use crate::solver::strategy::{
        CompositeStrategy,
        NakedSingleStrategy,
        OnlyCellStrategy,
        StrategicBacktrackingSolver,
        SudokuInfo,
        TupleStrategy
    };

    type DefaultKillerConstraint =
        CompositeConstraint<DefaultConstraint, KillerConstraint>;

    fn killer_example() -> Sudoku<DefaultKillerConstraint> {
        let grid = SudokuGrid::parse("2x2;
             , , , ,\
             , , , ,\
             ,4, , ,\
             , ,4, ").unwrap();
        let mut killer_constraint = KillerConstraint::new();
        let cage = KillerCage::new(vec![(0, 0), (1, 0), (2, 0)], 8).unwrap();
        killer_constraint.add_cage(cage).unwrap();
        let constraint =
            CompositeConstraint::new(DefaultConstraint, killer_constraint);
        Sudoku::new_with_grid(grid, constraint)
    }

    fn applied_killer_example() -> SudokuInfo<DefaultKillerConstraint> {
        let mut sudoku_info = SudokuInfo::from_sudoku(killer_example());
        assert!(KillerCagePossibilitiesStrategy.apply(&mut sudoku_info));
        sudoku_info
    }

    #[test]
    fn killer_cage_possibilities_strategy_excludes_due_to_sum() {
        let sudoku_info = applied_killer_example();
        assert!(!sudoku_info.get_options(0, 0).unwrap().contains(1));
    }

    #[test]
    fn killer_cage_possibilities_strategy_excludes_due_to_repeat() {
        let sudoku_info = applied_killer_example();
        assert!(!sudoku_info.get_options(0, 0).unwrap().contains(3));
    }

    fn big_killer_example() -> Sudoku<DefaultKillerConstraint> {
        // This Sudoku is taken from the World Puzzle Federation Sudoku GP 2020
        // Round 8 Puzzle 10
        // Puzzle: https://gp.worldpuzzle.org/sites/default/files/Puzzles/2020/2020_SudokuRound8.pdf
        // Solution: https://gp.worldpuzzle.org/sites/default/files/Puzzles/2020/2020_SudokuRound8_SB.pdf

        let grid = SudokuGrid::parse("3x3;
             , , , ,4, , , , ,\
             , , , , , , , , ,\
             , , , , , , , , ,\
             , , , , , , , , ,\
            5, , , , , , , ,7,\
             , , , , , , , , ,\
             , , , , , , , , ,\
             , , , , , , , , ,\
             , , , ,1, , , , ").unwrap();
        let mut killer_constraint = KillerConstraint::new();
        killer_constraint.add_cage(
            KillerCage::new(
                vec![(0, 0), (1, 0), (2, 0), (3, 0), (0, 1), (0, 2), (0, 3)],
                35).unwrap()
        ).unwrap();
        killer_constraint.add_cage(
            KillerCage::new(
                vec![(5, 0), (6, 0), (7, 0), (8, 0), (8, 1), (8, 2), (8, 3)],
                33).unwrap()
        ).unwrap();
        killer_constraint.add_cage(
            KillerCage::new(vec![(1, 1), (1, 2)], 9).unwrap()
        ).unwrap();
        killer_constraint.add_cage(
            KillerCage::new(vec![(2, 1), (2, 2)], 15).unwrap()
        ).unwrap();
        killer_constraint.add_cage(
            KillerCage::new(vec![(3, 1), (3, 2), (4, 2)], 14).unwrap()
        ).unwrap();
        killer_constraint.add_cage(
            KillerCage::new(vec![(4, 1), (5, 1), (5, 2)], 13).unwrap()
        ).unwrap();
        killer_constraint.add_cage(
            KillerCage::new(vec![(6, 1), (7, 1)], 12).unwrap()
        ).unwrap();
        killer_constraint.add_cage(
            KillerCage::new(vec![(6, 2), (7, 2)], 14).unwrap()
        ).unwrap();
        killer_constraint.add_cage(
            KillerCage::new(vec![(1, 3), (2, 3), (1, 4)], 13).unwrap()
        ).unwrap();
        killer_constraint.add_cage(
            KillerCage::new(vec![(6, 3), (7, 3), (6, 4)], 14).unwrap()
        ).unwrap();
        killer_constraint.add_cage(
            KillerCage::new(vec![(2, 4), (1, 5), (2, 5)], 12).unwrap()
        ).unwrap();
        killer_constraint.add_cage(
            KillerCage::new(vec![(7, 4), (6, 5), (7, 5)], 11).unwrap()
        ).unwrap();
        killer_constraint.add_cage(
            KillerCage::new(
                vec![(0, 5), (0, 6), (0, 7), (0, 8), (1, 8), (2, 8), (3, 8)],
                35).unwrap()
        ).unwrap();
        killer_constraint.add_cage(
            KillerCage::new(
                vec![(8, 5), (8, 6), (8, 7), (5, 8), (6, 8), (7, 8), (8, 8)],
                30).unwrap()
        ).unwrap();
        killer_constraint.add_cage(
            KillerCage::new(vec![(1, 6), (2, 6)], 13).unwrap()
        ).unwrap();
        killer_constraint.add_cage(
            KillerCage::new(vec![(3, 6), (3, 7), (4, 7)], 13).unwrap()
        ).unwrap();
        killer_constraint.add_cage(
            KillerCage::new(vec![(4, 6), (5, 6), (5, 7)], 17).unwrap()
        ).unwrap();
        killer_constraint.add_cage(
            KillerCage::new(vec![(6, 6), (6, 7)], 13).unwrap()
        ).unwrap();
        killer_constraint.add_cage(
            KillerCage::new(vec![(7, 6), (7, 7)], 16).unwrap()
        ).unwrap();
        killer_constraint.add_cage(
            KillerCage::new(vec![(1, 7), (2, 7)], 11).unwrap()
        ).unwrap();
        let constraint = CompositeConstraint::new(DefaultConstraint,
            killer_constraint);
        Sudoku::new_with_grid(grid, constraint)
    }

    fn big_killer_example_solution() -> SudokuGrid {
        SudokuGrid::parse("3x3;
            7,5,3,8,4,6,1,2,9,\
            4,8,6,2,9,1,7,5,3,\
            2,1,9,7,5,3,6,8,4,\
            6,4,7,3,2,5,9,1,8,\
            5,2,1,9,6,8,4,3,7,\
            9,3,8,1,7,4,2,6,5,\
            3,9,4,6,8,2,5,7,1,\
            1,6,5,4,3,7,8,9,2,\
            8,7,2,5,1,9,3,4,6").unwrap()
    }

    fn test_big_killer_solver<S: Solver>(solver: S) {
        let solution = solver.solve(&big_killer_example());
        let expected = big_killer_example_solution();
        assert_eq!(Solution::Unique(expected), solution);
    }

    #[test]
    fn killer_cage_possibilities_strategic_backtracking_is_sound() {
        let solver =
            StrategicBacktrackingSolver::new(KillerCagePossibilitiesStrategy);
        test_big_killer_solver(solver);
    }

    #[test]
    fn complex_killer_strategic_backtracking_is_sound() {
        let solver =
            StrategicBacktrackingSolver::new(CompositeStrategy::new(
                CompositeStrategy::new(
                    OnlyCellStrategy,
                    NakedSingleStrategy
                ),
                CompositeStrategy::new(
                    KillerCagePossibilitiesStrategy,
                    TupleStrategy::new(|_| 3)
                )
            ));
        test_big_killer_solver(solver);
    }
}
