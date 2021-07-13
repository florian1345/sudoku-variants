//! This module contains [Strategy] implementations specific to the
//! [SandwichConstraint]. They are re-exported in the
//! [specific](crate::solver::strategy::specific) module, so they do not have
//! to be referenced from this module directly.

use crate::set;
use crate::constraint::{
    ColumnConstraint,
    Constraint,
    RowConstraint,
    SandwichConstraint,
    Subconstraint
};
use crate::solver::strategy::{SudokuInfo, Strategy};
use crate::solver::strategy::specific::sum;
use crate::util::USizeSet;

use std::iter::{Skip, Take};
use std::slice::Iter;

/// A [Strategy] which looks at the options of the cells in a row/column with
/// annotated sandwich sum and uses them to deduce, where the sandwich "buns",
/// i.e. the bounding cells (1 and 9 in standard sandwich Sudoku) can be. It
/// then rules out the bun-digits in the cells it deduced cannot be buns, and
/// rules out all other digits, if it can uniquely determine the positions of
/// the buns.
///
/// As an example, consider the situation below.
///
/// ```text
///       2
/// ╔═══╤═══╦═══╤═══╗
/// ║   │ X ║   │   ║
/// ╟───┼───╫───┼───╢
/// ║   │   ║ 2 │   ║
/// ╠═══╪═══╬═══╪═══╣
/// ║   │ X ║   │   ║
/// ╟───┼───╫───┼───╢
/// ║   │   ║   │   ║
/// ╚═══╧═══╩═══╧═══╝
/// ```
///
/// Here, this strategy will be able to deduce that the cells with X cannot be
/// buns. For the upper one, this would require the cell below it to be a 2,
/// which would violate the row-constraint. For the lower one, there is no
/// space for another bun below it in sufficient distance, and the sandwich
/// cannot go up for the same reason discussed earlier. So, the strategy will
/// rule out the cells marked with X for buns. This leaves two remaining cells,
/// which will be marked as buns by this strategy.
pub struct SandwichBunPlacementStrategy;

fn bun(size: usize) -> USizeSet {
    set!(1, size; 1, size)
}

fn is_bun(options: &USizeSet, size: usize) -> bool {
    (options - &bun(size)).is_empty()
}

fn is_non_bun(options: &USizeSet, size: usize) -> bool {
    (options & &bun(size)).is_empty()
}

fn make_bun<C: Constraint + Clone>(sudoku_info: &mut SudokuInfo<C>,
        (column, row): (usize, usize)) -> bool {
    let size = sudoku_info.size();
    let options = sudoku_info.get_options_mut(column, row).unwrap();
    options.intersect_assign(&bun(size)).unwrap()
}

fn make_non_bun<C: Constraint + Clone>(sudoku_info: &mut SudokuInfo<C>,
        (column, row): (usize, usize)) -> bool {
    let size = sudoku_info.size();
    let options = sudoku_info.get_options_mut(column, row).unwrap();
    options.difference_assign(&bun(size)).unwrap()
}

fn sort(a: usize, b: usize) -> (usize, usize) {
    if a < b {
        (a, b)
    }
    else {
        (b, a)
    }
}

fn check_sum<'a, I, F>(sandwich: I, bun_1: usize, bun_2: usize, sum_checker: F,
    required_sum: usize) -> bool
where
    I: ExactSizeIterator<Item = &'a USizeSet>,
    F: Fn(Skip<Take<I>>, usize, usize) -> bool
{
    let inner_slice = sandwich.take(bun_2).skip(bun_1 + 1);
    sum_checker(inner_slice, 0, required_sum)
}

fn to_inner_options<C: Constraint + Clone>(sudoku_info: &SudokuInfo<C>,
        line: &[(usize, usize)]) -> Vec<USizeSet> {
    let size = sudoku_info.size();
    line.iter()
        .cloned()
        .map(|(column, row)|
            sudoku_info.get_options(column, row).unwrap() - &bun(size))
        .collect()
}

fn find_buns<C: Constraint + Clone>(sudoku_info: &SudokuInfo<C>,
        line: &[(usize, usize)]) -> (USizeSet, USizeSet) {
    let size = sudoku_info.size();
    let mut buns = USizeSet::new(0, size - 1).unwrap();
    let mut non_buns = USizeSet::new(0, size - 1).unwrap();

    for i in 0..size {
        let (column, row) = line[i];
        let options = sudoku_info.get_options(column, row).unwrap();

        if is_bun(options, size) {
            buns.insert(i).unwrap();
        }
        else if is_non_bun(options, size) {
            non_buns.insert(i).unwrap();
        }
    }

    (buns, non_buns)
}

/// Attempts to find cells in which there are definitely buns or definitely not
/// buns. Returns true if and only if some cell was changed.
///
/// # Arguments
///
/// * `sudoku_info`: The sudoku info structure to find options of cells.
/// * `line`: A vector of the coordinates of the form `(column, row)` of the
/// cells which are part of the row in which to search for sandwiches.
/// * `sum_checker`: A function which takes an iterator of options, a current
/// sum and a required sum, and outputs whether the sum can be reached. Useful
/// values are the `is_possible_<x>` functions in the `sum` module.
/// * `required_sum`: The sum that is required for the sandwich.
fn place_buns_in_sandwich<C, F>(sudoku_info: &mut SudokuInfo<C>,
    line: Vec<(usize, usize)>, sum_checker: F, required_sum: usize) -> bool
where
    C: Constraint + Clone,
    for<'a> F: Fn(Skip<Take<Iter<'a, USizeSet>>>, usize, usize) -> bool
{
    let size = sudoku_info.size();
    let (buns, mut non_buns) = find_buns(sudoku_info, &line);
    let mut changed = false;

    match buns.len() {
        0 => {
            // 0 buns => scan for possible pairs of buns.
            let mut possible_buns = USizeSet::new(0, size - 1).unwrap();
            let line_options = to_inner_options(sudoku_info, &line);

            for bun_1 in 0..size {
                if non_buns.contains(bun_1) {
                    continue;
                }

                for bun_2 in (bun_1 + 1)..size {
                    if non_buns.contains(bun_2) {
                        continue;
                    }

                    if check_sum(line_options.iter(), bun_1, bun_2,
                            &sum_checker, required_sum) {
                        possible_buns.insert(bun_1).unwrap();
                        possible_buns.insert(bun_2).unwrap();
                    }
                }
            }

            // If only two places for buns were found, they must be buns.
            if possible_buns.len() == 2 {
                for bun in possible_buns.iter() {
                    changed |= make_bun(sudoku_info, line[bun]);
                }
            }

            // All other places must be non-buns.
            possible_buns.complement_assign();

            for non_bun in possible_buns.iter() {
                changed |= make_non_bun(sudoku_info, line[non_bun]);
            }
        },
        1 => {
            // 1 bun => scan for possible other buns.
            let bun_index = buns.iter().next().unwrap();
            let line_options = to_inner_options(sudoku_info, &line);
            let mut new_non_buns = Vec::new();

            for index in 0..size {
                if index == bun_index || non_buns.contains(index) {
                    continue;
                }

                let (bun_1, bun_2) = sort(bun_index, index);

                if !check_sum(line_options.iter(), bun_1, bun_2, &sum_checker,
                        required_sum) {
                    new_non_buns.push(index);
                }
            }

            for non_bun in new_non_buns {
                changed |= make_non_bun(sudoku_info, line[non_bun]);
                non_buns.insert(non_bun).unwrap();
            }

            // If only two places for buns remain, they must be buns.
            if non_buns.len() == size - 2 {
                non_buns.complement_assign();

                for index in non_buns.iter() {
                    changed |= make_bun(sudoku_info, line[index]);
                }

                // Drop non_buns so we don't accidentally use it later
                let _ = non_buns;
            }
        },
        _ => {
            // 2 buns => make all other cells non-buns.
            for (index, &location) in line.iter().enumerate() {
                if !buns.contains(index) && !non_buns.contains(index) {
                    changed |= make_non_bun(sudoku_info, location);
                }
            }
        }
    }

    changed
}

fn do_in_lines<O, L>(size: usize, sandwiches: Vec<Option<usize>>,
    mut line_operation: O, line_getter: L) -> bool
where
    O: FnMut(Vec<(usize, usize)>, usize) -> bool,
    L: Fn(usize, usize) -> Vec<(usize, usize)>
{
    let mut changed = false;

    for (line, sum) in sandwiches.into_iter().enumerate() {
        if let Some(sum) = sum {
            let line = line_getter(line, size);
            changed |= line_operation(line, sum);
        }
    }

    changed
}

fn place_buns_in_lines<C, S, L>(sudoku_info: &mut SudokuInfo<C>,
    sandwiches: Vec<Option<usize>>, sum_checker: S, line_getter: L) -> bool
where
    C: Constraint + Clone + 'static,
    for<'a> S: Fn(Skip<Take<Iter<'a, USizeSet>>>, usize, usize) -> bool,
    L: Fn(usize, usize) -> Vec<(usize, usize)>
{
    do_in_lines(
        sudoku_info.size(),
        sandwiches,
        |l, s| place_buns_in_sandwich(sudoku_info, l, &sum_checker, s),
        line_getter)
}

fn place_buns_in_columns<C, F>(sudoku_info: &mut SudokuInfo<C>, sum_checker: F)
    -> bool
where
    C: Constraint + Clone + 'static,
    for<'a> F: Fn(Skip<Take<Iter<'a, USizeSet>>>, usize, usize) -> bool
{
    let constraint = sudoku_info.sudoku().constraint()
        .get_subconstraint::<SandwichConstraint>().unwrap();
    let sandwiches = constraint.column_sandwiches().clone();
    place_buns_in_lines(sudoku_info, sandwiches, sum_checker,
        |column, size| (0..size).map(|row| (column, row)).collect())
}

fn place_buns_in_rows<C, F>(sudoku_info: &mut SudokuInfo<C>, sum_checker: F)
    -> bool
where
    C: Constraint + Clone + 'static,
    for<'a> F: Fn(Skip<Take<Iter<'a, USizeSet>>>, usize, usize) -> bool
{
    let constraint = sudoku_info.sudoku().constraint()
        .get_subconstraint::<SandwichConstraint>().unwrap();
    let sandwiches = constraint.row_sandwiches().clone();
    place_buns_in_lines(sudoku_info, sandwiches, sum_checker,
        |row, size| (0..size).map(|column| (column, row)).collect())
}

impl Strategy for SandwichBunPlacementStrategy {
    fn apply<C>(&self, sudoku_info: &mut SudokuInfo<C>) -> bool
    where
        C: Constraint + Clone + 'static
    {
        let has_column_constraint = sudoku_info.sudoku().constraint()
            .has_subconstraint::<ColumnConstraint>();
        let has_row_constraint = sudoku_info.sudoku().constraint()
            .has_subconstraint::<RowConstraint>();
        let mut changed = false;

        if has_column_constraint {
            changed |= place_buns_in_columns(sudoku_info,
                |missing, current_sum, required_sum| {
                    sum::is_possible_unique(missing, current_sum, required_sum)
                });
        }
        else {
            changed |= place_buns_in_columns(sudoku_info,
                |missing, current_sum, required_sum| {
                    sum::is_possible_repeat(missing, current_sum, required_sum)
                });
        }

        if has_row_constraint {
            changed |= place_buns_in_rows(sudoku_info,
                |missing, current_sum, required_sum| {
                    sum::is_possible_unique(missing, current_sum, required_sum)
                });
        }
        else {
            changed |= place_buns_in_rows(sudoku_info,
                |missing, current_sum, required_sum| {
                    sum::is_possible_repeat(missing, current_sum, required_sum)
                });
        }

        changed
    }
}

/// Finds possible options how the given sandwich sum can be produced in the
/// sandwich in the given line and changes the cell options accordingly. This
/// is only relevant if the line contains exactly two buns. Returns true if and
/// only if some cell was changed.
///
/// # Arguments
///
/// * `sudoku_info`: The sudoku info structure to find options of cells.
/// * `line`: A vector of the coordinates of the form `(column, row)` of the
/// cells which are part of the line in which the potential sandwich lies.
/// * `sum_evaluator`: A function which takes an iterator over options, a
/// current sum and a required sum, and outputs a vector of the reduced options
/// after considering all options of how to compose the sum.
/// * `required_sum`: The sum that is required for the sandwich.
fn evaluate_sum_in_sandwich<C, F>(sudoku_info: &mut SudokuInfo<C>,
    line: Vec<(usize, usize)>, sum_evaluator: F, required_sum: usize) -> bool
where
    C: Constraint + Clone,
    for<'a> F: Fn(Iter<'a, USizeSet>, usize, usize) -> Vec<USizeSet>
{
    let (buns, _) = find_buns(sudoku_info, &line);

    if buns.len() != 2 {
        return false;
    }

    let mut buns_iter = buns.iter();
    let bun_1 = buns_iter.next().unwrap();
    let bun_2 = buns_iter.next().unwrap();
    let inner_cells = &line[(bun_1 + 1)..bun_2];
    let inner_options = to_inner_options(sudoku_info, inner_cells);
    let new_options = sum_evaluator(inner_options.iter(), 0, required_sum);
    let new_options = inner_cells.iter().zip(new_options.iter());
    let mut changed = false;

    for (&(column, row), new_options) in new_options {
        let options = sudoku_info.get_options_mut(column, row).unwrap();
        changed |= options.intersect_assign(new_options).unwrap();
    }

    changed
}

fn evaluate_sum_in_lines<C, S, L>(sudoku_info: &mut SudokuInfo<C>,
    sandwiches: Vec<Option<usize>>, sum_evaluator: S, line_getter: L)
    -> bool
where
    C: Constraint + Clone + 'static,
    for<'a> S: Fn(Iter<'a, USizeSet>, usize, usize) -> Vec<USizeSet>,
    L: Fn(usize, usize) -> Vec<(usize, usize)>
{
    do_in_lines(
        sudoku_info.size(),
        sandwiches,
        |l, s| evaluate_sum_in_sandwich(sudoku_info, l, &sum_evaluator, s),
        line_getter)
}

fn evaluate_sum_in_columns<C, F>(sudoku_info: &mut SudokuInfo<C>,
    sum_evaluator: F) -> bool
where
    C: Constraint + Clone + 'static,
    for<'a> F: Fn(Iter<'a, USizeSet>, usize, usize) -> Vec<USizeSet>,
{
    let constraint = sudoku_info.sudoku().constraint()
        .get_subconstraint::<SandwichConstraint>().unwrap();
    let sandwiches = constraint.column_sandwiches().clone();
    evaluate_sum_in_lines(sudoku_info, sandwiches, sum_evaluator,
        |column, size| (0..size).map(|row| (column, row)).collect())
}

fn evaluate_sum_in_rows<C, F>(sudoku_info: &mut SudokuInfo<C>,
    sum_evaluator: F) -> bool
where
    C: Constraint + Clone + 'static,
    for<'a> F: Fn(Iter<'a, USizeSet>, usize, usize) -> Vec<USizeSet>,
{
    let constraint = sudoku_info.sudoku().constraint()
        .get_subconstraint::<SandwichConstraint>().unwrap();
    let sandwiches = constraint.row_sandwiches().clone();
    evaluate_sum_in_lines(sudoku_info, sandwiches, sum_evaluator,
        |row, size| (0..size).map(|column| (column, row)).collect())
}

/// A strategy which looks for known sandwiches, i.e. for rows and columns in
/// which two "buns", i.e. cells which can only be 1 or the highest number on
/// the grid, exist. It then considers all the possibilities on how the sum
/// could be produced by the cells inside the sandwich and removes all options
/// which do not participate in at least one possibility.
///
/// As an example, consider the situation below.
///
/// ```text
///                   9
/// ╔═══╤═══╤═══╦═══╤═══╤═══╦═══╤═══╤═══╗
/// ║   │   │   ║ 6 │   │   ║   │   │   ║
/// ╟───┼───┼───╫───┼───┼───╫───┼───┼───╢
/// ║   │   │   ║   │ X │   ║   │   │   ║
/// ╟───┼───┼───╫───┼───┼───╫───┼───┼───╢
/// ║   │ 3 │   ║   │ Y │   ║   │   │   ║
/// ╠═══╪═══╪═══╬═══╪═══╪═══╬═══╪═══╪═══╣
/// ║   │   │   ║   │   │   ║   │   │   ║
/// ╟───┼───┼───╫───┼───┼───╫───┼───┼───╢
/// ║   │   │   ║   │ X │   ║   │   │   ║
/// ╟───┼───┼───╫───┼───┼───╫───┼───┼───╢
/// ║   │   │   ║   │   │   ║   │   │   ║
/// ╠═══╪═══╪═══╬═══╪═══╪═══╬═══╪═══╪═══╣
/// ║   │   │   ║   │   │   ║   │   │   ║
/// ╟───┼───┼───╫───┼───┼───╫───┼───┼───╢
/// ║   │   │   ║   │ 2 │   ║   │   │   ║
/// ╟───┼───┼───╫───┼───┼───╫───┼───┼───╢
/// ║   │   │   ║   │   │   ║   │   │   ║
/// ╚═══╧═══╧═══╩═══╧═══╧═══╩═══╧═══╧═══╝
/// ```
///
/// Assume the cells marked with X have been found to be buns. Further assume
/// that classic Sudoku constraints apply. Then, the different options of how
/// to compose the sum of 9 are 2 and 7, 3 and 6, as well as 4 and 5. This
/// strategy would be able to deduce that the sum cannot be 2 and 7, since 2
/// must not be inside the sandwich, and tht it can also not be 3 and 6, since
/// the cell marked with Y can be neither. Therefore, this strategy would leave
/// only the options 4 and 5 in the cells inside the sandwich.
pub struct SandwichPossibilitiesStrategy;

impl Strategy for SandwichPossibilitiesStrategy {
    fn apply<C>(&self, sudoku_info: &mut SudokuInfo<C>) -> bool
    where
        C: Constraint + Clone + 'static
    {
        // TODO somehow avoid code duplication with the bun placement strategy

        let has_column_constraint = sudoku_info.sudoku().constraint()
            .has_subconstraint::<ColumnConstraint>();
        let has_row_constraint = sudoku_info.sudoku().constraint()
            .has_subconstraint::<RowConstraint>();
        let mut changed = false;

        if has_column_constraint {
            changed |= evaluate_sum_in_columns(sudoku_info,
                |missing, current_sum, required_sum| {
                    sum::find_options_unique(missing, current_sum, required_sum)
                });
        }
        else {
            changed |= evaluate_sum_in_columns(sudoku_info,
                |missing, current_sum, required_sum| {
                    sum::find_options_repeat(missing, current_sum, required_sum)
                });
        }

        if has_row_constraint {
            changed |= evaluate_sum_in_rows(sudoku_info,
                |missing, current_sum, required_sum| {
                    sum::find_options_unique(missing, current_sum, required_sum)
                });
        }
        else {
            changed |= evaluate_sum_in_rows(sudoku_info,
                |missing, current_sum, required_sum| {
                    sum::find_options_repeat(missing, current_sum, required_sum)
                });
        }

        changed
    }
}

#[cfg(test)]
mod tests {

    use crate::{Sudoku, SudokuGrid};
    use crate::constraint::{
        CompositeConstraint,
        Constraint,
        DefaultConstraint,
        SandwichConstraint
    };
    use crate::solver::{Solution, Solver};
    use crate::solver::strategy::{
        CompositeStrategy,
        StrategicBacktrackingSolver,
        Strategy,
        SudokuInfo
    };
    use crate::set;
    use crate::util::USizeSet;

    use super::*;

    fn assert_bun_status<C, P>(sudoku_info: &SudokuInfo<C>, column: usize,
        row: usize, predicate: P)
    where
        C: Constraint + Clone,
        P: Fn(&USizeSet, &USizeSet) -> bool
    {
        let size = sudoku_info.size();
        let bun_options = set!(1, size; 1, size);
        let options = sudoku_info.get_options(column, row).unwrap();

        assert!(predicate(options, &bun_options));
    }

    fn assert_is_bun<C>(sudoku_info: &SudokuInfo<C>, column: usize, row: usize)
    where
        C: Constraint + Clone
    {
        assert_bun_status(sudoku_info, column, row,
            |a, b| a.is_subset(b).unwrap())
    }

    fn assert_is_not_bun<C>(sudoku_info: &SudokuInfo<C>, column: usize,
        row: usize)
    where
        C: Constraint + Clone
    {
        assert_bun_status(sudoku_info, column, row,
            |a, b| a.is_disjoint(b).unwrap())
    }

    fn assert_can_be_bun<C>(sudoku_info: &SudokuInfo<C>, column: usize,
        row: usize)
    where
        C: Constraint + Clone
    {
        assert_bun_status(sudoku_info, column, row,
            |a, b| !a.is_disjoint(b).unwrap())
    }

    #[test]
    fn sandwich_bun_placement_strategy_enforces_neighboring_on_sum_0() {
        let grid = SudokuGrid::parse("2x2;
             ,1, , ,\
             , , , ,\
             , , , ,\
             , , , ").unwrap();
        let mut constraint = SandwichConstraint::new(4);
        constraint.set_column_sandwich(1, 0).unwrap();
        let sudoku = Sudoku::new_with_grid(grid,
            CompositeConstraint::new(DefaultConstraint, constraint));
        let mut sudoku_info = SudokuInfo::from_sudoku(sudoku);

        assert!(SandwichBunPlacementStrategy.apply(&mut sudoku_info));
        assert_eq!(&set!(1, 4; 4), sudoku_info.get_options(1, 1).unwrap());
    }

    #[test]
    fn sandwich_bun_placement_strategy_enforces_minimal_gap() {
        let grid = SudokuGrid::parse("3x3;
             , , , , , , , , ,\
            1, , , , , , , , ,\
             , , , , , , , , ,\
             , , , , , , , , ,\
             , , , , , , , , ,\
             , , , , , , , , ,\
             , , , , , , , , ,\
             , , , , , , , , ,\
             , , , , , , , , ").unwrap();
        let mut constraint = SandwichConstraint::new(9);
        constraint.set_row_sandwich(1, 9).unwrap();
        let sudoku = Sudoku::new_with_grid(grid,
            CompositeConstraint::new(DefaultConstraint, constraint));
        let mut sudoku_info = SudokuInfo::from_sudoku(sudoku);

        assert!(SandwichBunPlacementStrategy.apply(&mut sudoku_info));

        assert_is_not_bun(&mut sudoku_info, 1, 1);
        assert_is_not_bun(&mut sudoku_info, 2, 1);
        assert_can_be_bun(&mut sudoku_info, 3, 1);
        assert_can_be_bun(&mut sudoku_info, 4, 1);
        assert_is_not_bun(&mut sudoku_info, 5, 1);
    }

    #[test]
    fn sandwich_bun_placement_strategy_enforces_opposite_on_max_sum() {
        let grid = SudokuGrid::parse("3x2;
             , ,6, , , ,\
             , , , , , ,\
             , , , , , ,\
             , , , , , ,\
             , , , , , ,\
             , , , , , ").unwrap();
        let mut constraint = SandwichConstraint::new(6);
        constraint.set_column_sandwich(2, 14).unwrap();
        let sudoku = Sudoku::new_with_grid(grid,
            CompositeConstraint::new(DefaultConstraint, constraint));
        let mut sudoku_info = SudokuInfo::from_sudoku(sudoku);

        assert!(SandwichBunPlacementStrategy.apply(&mut sudoku_info));

        assert_is_not_bun(&mut sudoku_info, 2, 1);
        assert_is_not_bun(&mut sudoku_info, 2, 2);
        assert_is_not_bun(&mut sudoku_info, 2, 3);
        assert_is_not_bun(&mut sudoku_info, 2, 4);
        assert_is_bun(&mut sudoku_info, 2, 5);
    }

    #[test]
    fn sandwich_bun_placement_strategy_rules_out_center_on_sufficient_sum() {
        let grid = SudokuGrid::new(3, 3).unwrap();
        let mut constraint = SandwichConstraint::new(9);
        constraint.set_row_sandwich(4, 27).unwrap();
        constraint.set_column_sandwich(7, 22).unwrap();
        let sudoku = Sudoku::new_with_grid(grid,
            CompositeConstraint::new(DefaultConstraint, constraint));
        let mut sudoku_info = SudokuInfo::from_sudoku(sudoku);

        assert!(SandwichBunPlacementStrategy.apply(&mut sudoku_info));

        assert_can_be_bun(&mut sudoku_info, 2, 4);
        assert_is_not_bun(&mut sudoku_info, 3, 4);
        assert_is_not_bun(&mut sudoku_info, 4, 4);
        assert_is_not_bun(&mut sudoku_info, 5, 4);
        assert_can_be_bun(&mut sudoku_info, 6, 4);
        
        assert_can_be_bun(&mut sudoku_info, 7, 3);
        assert_is_not_bun(&mut sudoku_info, 7, 4);
        assert_can_be_bun(&mut sudoku_info, 7, 5);
    }

    #[test]
    fn sandwich_bun_placement_strategy_selectively_considers_repeats() {
        let grid = SudokuGrid::parse("3x2;\
             , , , , , ,\
             , , , , , ,\
             , ,1, , , ,\
             , , , , , ,\
             , , , , , ,\
             , , , , , ").unwrap();
        let mut constraint = SandwichConstraint::new(6);
        constraint.set_row_sandwich(2, 4).unwrap();
        constraint.set_column_sandwich(2, 4).unwrap();
        let row_sudoku = Sudoku::new_with_grid(grid.clone(),
            CompositeConstraint::new(RowConstraint, constraint.clone()));
        let mut row_sudoku_info = SudokuInfo::from_sudoku(row_sudoku);
        let column_sudoku = Sudoku::new_with_grid(grid,
            CompositeConstraint::new(ColumnConstraint, constraint));
        let mut column_sudoku_info = SudokuInfo::from_sudoku(column_sudoku);
        
        assert!(SandwichBunPlacementStrategy.apply(&mut row_sudoku_info));
        assert!(SandwichBunPlacementStrategy.apply(&mut column_sudoku_info));
        
        assert_is_not_bun(&mut row_sudoku_info, 5, 2);
        assert_can_be_bun(&mut row_sudoku_info, 2, 5);
        assert_can_be_bun(&mut column_sudoku_info, 5, 2);
        assert_is_not_bun(&mut column_sudoku_info, 2, 5);
    }

    #[test]
    fn sandwich_possibilities_strategy_doc_example() {
        let grid = SudokuGrid::parse("3x3;
             , , ,6, , , , , ,\
             , , , ,1, , , , ,\
             ,3, , , , , , , ,\
             , , , , , , , , ,\
             , , , ,9, , , , ,\
             , , , , , , , , ,\
             , , , , , , , , ,\
             , , , ,2, , , , ,\
             , , , , , , , , ").unwrap();
        let mut constraint = SandwichConstraint::new(9);
        constraint.set_column_sandwich(4, 9).unwrap();
        let sudoku = Sudoku::new_with_grid(grid,
            CompositeConstraint::new(DefaultConstraint, constraint));
        let mut sudoku_info = SudokuInfo::from_sudoku(sudoku);

        assert!(SandwichPossibilitiesStrategy.apply(&mut sudoku_info));
        assert_eq!(&set!(1, 9; 4, 5), sudoku_info.get_options(4, 2).unwrap());
        assert_eq!(&set!(1, 9; 4, 5), sudoku_info.get_options(4, 3).unwrap());
    }

    #[test]
    fn sandwich_possibilities_strategy_selectively_considers_repeats() {
        let grid = SudokuGrid::parse("3x2;\
             , , , , , ,\
             , , , , , ,\
             , ,1, , ,6,\
             , , , , , ,\
             , , , , , ,\
             , ,6, , , ").unwrap();
        let mut constraint = SandwichConstraint::new(6);
        constraint.set_row_sandwich(2, 6).unwrap();
        constraint.set_column_sandwich(2, 6).unwrap();
        let row_sudoku = Sudoku::new_with_grid(grid.clone(),
            CompositeConstraint::new(RowConstraint, constraint.clone()));
        let mut row_sudoku_info = SudokuInfo::from_sudoku(row_sudoku);
        let column_sudoku = Sudoku::new_with_grid(grid,
            CompositeConstraint::new(ColumnConstraint, constraint));
        let mut column_sudoku_info = SudokuInfo::from_sudoku(column_sudoku);
        
        assert!(SandwichPossibilitiesStrategy.apply(&mut row_sudoku_info));
        assert!(SandwichPossibilitiesStrategy.apply(&mut column_sudoku_info));
        
        assert_eq!(&set!(1, 6; 2, 4),
            row_sudoku_info.get_options(3, 2).unwrap());
        assert_eq!(&set!(1, 6; 2, 3, 4),
            row_sudoku_info.get_options(2, 3).unwrap());
        assert_eq!(&set!(1, 6; 2, 3, 4),
            column_sudoku_info.get_options(3, 2).unwrap());
        assert_eq!(&set!(1, 6; 2, 4),
            column_sudoku_info.get_options(2, 3).unwrap());
    }

    fn example_sandwich_sudoku() -> Sudoku<impl Constraint + Clone + 'static> {
        let grid = SudokuGrid::parse("3x3;
             , , , , , , , , ,\
             , , , , , , , , ,\
             , , , , , , , , ,\
             , , , ,3,1, , ,7,\
             , , , , , , , , ,\
             , , , , ,6, , , ,\
             , , , , , , , , ,\
             ,5, , , , , ,8, ,\
             , ,2, , , , , , ").unwrap();
        let mut constraint = SandwichConstraint::new(9);
        let column_sandwiches = vec![33, 0, 25, 9, 35, 0, 22, 0, 10];
        let row_sandwiches = vec![7, 7, 11, 14, 5, 0, 0, 0, 16];

        for (c, s) in column_sandwiches.into_iter().enumerate() {
            constraint.set_column_sandwich(c, s).unwrap();
        }

        for (r, s) in row_sandwiches.into_iter().enumerate() {
            constraint.set_row_sandwich(r, s).unwrap();
        }

        Sudoku::new_with_grid(grid,
            CompositeConstraint::new(DefaultConstraint, constraint))
    }

    fn example_sandwich_solution() -> Solution {
        Solution::Unique(SudokuGrid::parse("3x3;
            2,4,8,3,1,7,9,5,6,\
            9,7,1,4,6,5,3,2,8,\
            5,6,3,8,2,9,4,7,1,\
            8,9,6,5,3,1,2,4,7,\
            7,1,5,9,4,2,8,6,3,\
            3,2,4,7,8,6,5,1,9,\
            6,3,7,2,5,8,1,9,4,\
            4,5,9,1,7,3,6,8,2,\
            1,8,2,6,9,4,7,3,5").unwrap())
    }

    fn sandwich_strategic_backtracking_solver()
            -> StrategicBacktrackingSolver<impl Strategy> {
        StrategicBacktrackingSolver::new(
            CompositeStrategy::new(
                SandwichBunPlacementStrategy, 
                SandwichPossibilitiesStrategy))
    }

    #[test]
    fn sandwich_strategic_backtracking_sound_for_default_sandwich_sudoku() {
        let sudoku = example_sandwich_sudoku();
        let solver = sandwich_strategic_backtracking_solver();
        let solution = solver.solve(&sudoku);
        let expected = example_sandwich_solution();

        assert_eq!(expected, solution);
    }
}
