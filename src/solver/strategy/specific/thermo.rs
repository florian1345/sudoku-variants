//! This module contains [Strategy] implementations specific to the
//! [ThermoConstraint]. They are re-exported in the
//! [specific](crate::solver::strategy::specific) module, so they do not have
//! to be referenced from this module directly.

use crate::constraint::{
    Constraint,
    Subconstraint,
    ThermoConstraint,
    Thermometer
};
use crate::solver::strategy::{Strategy, SudokuInfo};

/// A [Strategy] which follows thermometers from bulb to end, tracking the
/// minimum numbers along the way (adding 1 for empty cells as a conservative
/// estimate) and eliminates all lower options.
#[derive(Clone)]
pub struct ForwardThermometerFollowingStrategy;

fn apply_for_thermometers<C>(sudoku_info: &mut SudokuInfo<C>,
    processor: impl Fn(&mut SudokuInfo<C>, &Thermometer) -> bool) -> bool
where
    C: Constraint + Clone + 'static
{
    let c = sudoku_info.sudoku().constraint();

    if let Some(thermo) = c.get_subconstraint::<ThermoConstraint>() {
        let mut changed = false;
        let thermometers = thermo.thermometers().clone();

        for thermometer in thermometers {
            changed |= processor(sudoku_info, &thermometer);
        }

        changed
    }
    else {
        panic!("Thermo-specific strategy deployed on non-thermo Sudoku.")
    }
}

fn process_thermometer_forward<C>(sudoku_info: &mut SudokuInfo<C>,
    thermometer: &Thermometer) -> bool
where
    C: Constraint + Clone
{
    let mut min = 1;
    let mut changed = false;

    for &(column, row) in thermometer.cells() {
        let options = sudoku_info.get_options_mut(column, row).unwrap();
        let to_remove = options.iter()
            .filter(|&n| n < min)
            .collect::<Vec<_>>();

        for option in to_remove {
            options.remove(option).unwrap();
            changed = true;
        }

        min = match options.min() {
            Some(n) => n + 1,
            None => usize::MAX
        };
    }

    changed
}

impl Strategy for ForwardThermometerFollowingStrategy {
    fn apply<C>(&self, sudoku_info: &mut SudokuInfo<C>) -> bool
    where
        C: Constraint + Clone + 'static
    {
        apply_for_thermometers(sudoku_info, process_thermometer_forward)
    }
}

/// A [Strategy] which follows thermometers from end to bulb, tracking the
/// maximum numbers along the way (subtracting 1 for empty cells as a
/// conservative estimate) and eliminates all higher options.
#[derive(Clone)]
pub struct BackwardThermometerFollowingStrategy;

// TODO avoid code duplication with forward

fn process_thermometer_backward<C>(sudoku_info: &mut SudokuInfo<C>,
    thermometer: &Thermometer) -> bool
where
    C: Constraint + Clone
{
    let mut max = sudoku_info.size();
    let mut changed = false;

    for &(column, row) in thermometer.cells().iter().rev() {
        let options = sudoku_info.get_options_mut(column, row).unwrap();
        let to_remove = options.iter()
            .filter(|&n| n > max)
            .collect::<Vec<_>>();

        for option in to_remove {
            options.remove(option).unwrap();
            changed = true;
        }

        max = match options.max() {
            Some(n) => n - 1,
            None => 0
        };
    }

    changed
}

impl Strategy for BackwardThermometerFollowingStrategy {
    fn apply<C>(&self, sudoku_info: &mut SudokuInfo<C>) -> bool
    where
        C: Constraint + Clone + 'static
    {
        apply_for_thermometers(sudoku_info, process_thermometer_backward)
    }
}

/// A [Strategy] which deploys the [ForwardThermometerFollowingStrategy] and
/// the [BackwardThermometerFollowingStrategy] for convenience.
#[derive(Clone)]
pub struct ThermometerFollowingStrategy;

impl Strategy for ThermometerFollowingStrategy {
    fn apply<C>(&self, sudoku_info: &mut SudokuInfo<C>) -> bool
    where
        C: Constraint + Clone + 'static
    {
        ForwardThermometerFollowingStrategy.apply(sudoku_info) ||
            BackwardThermometerFollowingStrategy.apply(sudoku_info)
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::{Sudoku, SudokuGrid};
    use crate::constraint::{
        CompositeConstraint,
        DefaultConstraint,
        ThermoConstraint
    };
    use crate::solver::{Solution, Solver};
    use crate::solver::strategy::{
        CompositeStrategy,
        NakedSingleStrategy,
        OnlyCellStrategy,
        StrategicBacktrackingSolver,
        TupleStrategy
    };

    type DefaultThermoConstraint =
        CompositeConstraint<DefaultConstraint, ThermoConstraint>;

    fn thermo_example(grid_code: &str) -> Sudoku<DefaultThermoConstraint> {
        let grid = SudokuGrid::parse(grid_code).unwrap();
        let mut thermo_constraint = ThermoConstraint::new();
        thermo_constraint.add_thermometer(
            Thermometer::new(vec![(1, 0), (1, 1), (1, 2)]).unwrap()
        ).unwrap();
        let constraint =
            CompositeConstraint::new(DefaultConstraint, thermo_constraint);
        Sudoku::new_with_grid(grid, constraint)
    }

    #[test]
    fn forward_following() {
        let sudoku = thermo_example("2x2;
             , , , ,\
             , ,2, ,\
             , , , ,\
             , , , ");
        let mut sudoku_info = SudokuInfo::from_sudoku(sudoku);

        assert!(ForwardThermometerFollowingStrategy.apply(&mut sudoku_info));
        assert!(!sudoku_info.get_options(1, 1).unwrap().contains(1));
        assert!(!sudoku_info.get_options(1, 2).unwrap().contains(3));
    }

    #[test]
    fn backward_following() {
        let sudoku = thermo_example("2x2;
             , , , ,\
             , ,3, ,\
             , , , ,\
             , , , ");
        let mut sudoku_info = SudokuInfo::from_sudoku(sudoku);

        assert!(BackwardThermometerFollowingStrategy.apply(&mut sudoku_info));
        assert!(!sudoku_info.get_options(1, 1).unwrap().contains(4));
        assert!(!sudoku_info.get_options(1, 0).unwrap().contains(2));
    }

    fn big_thermo_example() -> Sudoku<DefaultThermoConstraint> {
        // This Sudoku is taken from the World Puzzle Federation Sudoku GP 2020
        // Round 6 Puzzle 8
        // Puzzle: https://gp.worldpuzzle.org/sites/default/files/Puzzles/2019/2019_SudokuRound6.pdf
        // Solution: https://gp.worldpuzzle.org/sites/default/files/Puzzles/2019/2019_SudokuRound6_SB.pdf

        let grid = SudokuGrid::parse("3x3;
             ,6,4,5, ,7,3,2, ,\
            3, , , , , , , , ,\
            2, , , , , , , , ,\
            7, , , , , , , , ,\
             , , , ,6, , , , ,\
             , , , , , , , ,9,\
             , , , , , , , ,4,\
             , , , , , , , ,2,\
             ,8,2,9, ,4,7,1, ").unwrap();
        let mut thermo_constraint = ThermoConstraint::new();
        thermo_constraint.add_thermometer(
            Thermometer::new(vec![(1, 1), (1, 2), (1, 3)]).unwrap()
        ).unwrap();
        thermo_constraint.add_thermometer(
            Thermometer::new(vec![(2, 1), (3, 1), (3, 2)]).unwrap()
        ).unwrap();
        thermo_constraint.add_thermometer(
            Thermometer::new(vec![(6, 1), (7, 1), (7, 2)]).unwrap()
        ).unwrap();
        thermo_constraint.add_thermometer(
            Thermometer::new(vec![(6, 2), (5, 2), (5, 1)]).unwrap()
        ).unwrap();
        thermo_constraint.add_thermometer(
            Thermometer::new(vec![(3, 3), (2, 3), (2, 2)]).unwrap()
        ).unwrap();
        thermo_constraint.add_thermometer(
            Thermometer::new(vec![(5, 3), (6, 3), (7, 3)]).unwrap()
        ).unwrap();
        thermo_constraint.add_thermometer(
            Thermometer::new(vec![(1, 4), (2, 4), (3, 4)]).unwrap()
        ).unwrap();
        thermo_constraint.add_thermometer(
            Thermometer::new(vec![(7, 4), (6, 4), (5, 4)]).unwrap()
        ).unwrap();
        thermo_constraint.add_thermometer(
            Thermometer::new(vec![(8, 4), (8, 3), (8, 2)]).unwrap()
        ).unwrap();
        thermo_constraint.add_thermometer(
            Thermometer::new(vec![(1, 5), (2, 5), (2, 6)]).unwrap()
        ).unwrap();
        thermo_constraint.add_thermometer(
            Thermometer::new(vec![(0, 6), (0, 5), (0, 4)]).unwrap()
        ).unwrap();
        thermo_constraint.add_thermometer(
            Thermometer::new(vec![(1, 6), (1, 7), (2, 7)]).unwrap()
        ).unwrap();
        thermo_constraint.add_thermometer(
            Thermometer::new(vec![(5, 6), (5, 5), (6, 5)]).unwrap()
        ).unwrap();
        thermo_constraint.add_thermometer(
            Thermometer::new(vec![(3, 7), (3, 6), (3, 5)]).unwrap()
        ).unwrap();
        thermo_constraint.add_thermometer(
            Thermometer::new(vec![(5, 7), (6, 7), (6, 6)]).unwrap()
        ).unwrap();
        thermo_constraint.add_thermometer(
            Thermometer::new(vec![(7, 7), (7, 6), (7, 5)]).unwrap()
        ).unwrap();
        let constraint =
            CompositeConstraint::new(DefaultConstraint, thermo_constraint);
        Sudoku::new_with_grid(grid, constraint)
    }

    fn big_thermo_solution() -> SudokuGrid {
        SudokuGrid::parse("3x3;
            9,6,4,5,1,7,3,2,8,
            3,5,1,2,9,8,4,6,7,
            2,7,8,3,4,6,1,9,5,
            7,9,6,4,5,1,2,8,3,
            8,2,3,7,6,9,5,4,1,
            4,1,5,8,2,3,6,7,9,
            1,3,7,6,8,2,9,5,4,
            6,4,9,1,7,5,8,3,2,
            5,8,2,9,3,4,7,1,6").unwrap()
    }

    fn test_big_thermo_solver<S: Solver>(solver: S) {
        let solution = solver.solve(&big_thermo_example());
        let expected = big_thermo_solution();
        assert_eq!(Solution::Unique(expected), solution);
    }

    #[test]
    fn thermometer_following_strategic_backtracking_is_sound() {
        let solver =
            StrategicBacktrackingSolver::new(ThermometerFollowingStrategy);
        test_big_thermo_solver(solver);
    }

    #[test]
    fn complex_thermometer_following_strategic_backtracking_is_sound() {
        let solver =
            StrategicBacktrackingSolver::new(CompositeStrategy::new(
                CompositeStrategy::new(
                    OnlyCellStrategy,
                    NakedSingleStrategy
                ),
                CompositeStrategy::new(
                    ThermometerFollowingStrategy,
                    TupleStrategy::new(|_| 3)
                )
            ));
        test_big_thermo_solver(solver);
    }
}
