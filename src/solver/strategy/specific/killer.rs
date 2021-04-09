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

/// Recursively enters all options to build the required sum from the remaining
/// cells into `new_options`.
///
/// # Arguments
///
/// * `missing`: A [USizeSet] for each missing cell containing its options.
/// * `current_sum`: The sum accumulated so far from the previous cells, i.e.
/// all cells that were already filled and all that have been inserted.
/// * `required_sum`: The sum annotated at the cage.
/// * `new_options`: A vector which contains one [USizeSet] for each remaining
/// cell (same indices as `missing`). In this set all found options for that
/// specific cell should be entered.
/// * `numbers`: A [USizeSet] that contains all numbers that were already
/// inserted into previous cells in the cage. Filled cells are not considered
/// here, since those should not occur in the options in the first place.
/// * `index`: The index of the cell to process at this recursion depth.
fn find_options_rec(missing: &[&USizeSet], current_sum: usize,
        required_sum: usize, new_options: &mut Vec<USizeSet>,
        numbers: &mut USizeSet, index: usize) -> bool {
    if index == missing.len() - 1 {
        let required = required_sum - current_sum;

        if missing[index].contains(required) && !numbers.contains(required) {
            new_options[index].insert(required).unwrap();
            return true;
        }

        return false;
    }

    let mut result = false;

    for option in missing[index].iter() {
        let next_sum = current_sum + option;

        if next_sum >= required_sum {
            // Options are in ascending order, so following options will only
            // be worse.
            break;
        }

        if numbers.contains(option) {
            continue;
        }

        numbers.insert(option).unwrap();

        if find_options_rec(missing, next_sum, required_sum, new_options,
                numbers, index + 1) {
            new_options[index].insert(option).unwrap();
            result = true;
        }

        numbers.remove(option).unwrap();
    }

    result
}

fn find_options(missing: &[&USizeSet], current_sum: usize, required_sum: usize,
        size: usize) -> Vec<USizeSet> {
    let mut new_options = vec![USizeSet::new(1, size).unwrap(); missing.len()];
    let mut numbers = USizeSet::new(1, size).unwrap();
    find_options_rec(missing, current_sum, required_sum, &mut new_options,
        &mut numbers, 0);
    new_options
}

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
        find_options(&missing_options, sum, cage.sum(), sudoku_info.size());
    let mut changed = false;

    for (new_options, &(column, row)) in new_options.iter().zip(missing_cells.iter()) {
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
    use crate::solver::strategy::SudokuInfo;

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
}
