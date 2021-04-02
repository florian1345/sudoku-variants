//! This module contains the implementation of the [KillerConstraint] as well
//! as all auxiliary data structures. The most used structs are re-exported in
//! the [constraint](crate::constraint) module, so you should not have to
//! reference this module directly (except if you want dive deeper into the
//! mechanics).

use crate::SudokuGrid;
use crate::constraint::{Constraint, Group, ReductionError};
use crate::error::SudokuResult;
use crate::util::{self, USizeSet};

use std::collections::{HashMap, HashSet};

/// A single cage in a Killer Sudoku, which contains some cells and annotates
/// the sum of digits in these cells. Additionally, it requires that no digits
/// repeat in this cage.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct KillerCage {
    group: Group,
    sum: usize
}

impl KillerCage {

    /// Creates a new Killer cage with the given group and sum.
    ///
    /// # Arguments
    ///
    /// * `group`: The [Group](crate::constraint::Group) of cells contained in
    /// this cage. May not be empty or contain duplicates.
    /// * `sum`: The annotated sum of the cage.
    ///
    /// # Errors
    ///
    /// `KillerError::EmptyCage` if the group is empty and
    /// `KillerError::DuplicateCells` if it contains the same cell more than
    /// once.
    pub fn new(group: Group, sum: usize) -> Result<KillerCage, KillerError> {
        if group.is_empty() {
            return Err(KillerError::EmptyCage);
        }

        if util::contains_duplicate(group.iter()) {
            return Err(KillerError::DuplicateCells);
        }

        Ok(KillerCage {
            group,
            sum
        })
    }

    /// Gets the [Group](crate::constraint::Group) of cells contained in this
    /// cage.
    pub fn group(&self) -> &Group {
        &self.group
    }

    /// Gets the annotated sum of the cage.
    pub fn sum(&self) -> usize {
        self.sum
    }

    /// Joins this cage with another, that is, appends the other cage's cells
    /// to this one's and adds the sum.
    ///
    /// It is expected that both cages are disjunct, i.e. do not share cells,
    /// otherwise the result will be wrong.
    pub fn join(&mut self, mut other: KillerCage) {
        self.group.append(&mut other.group);
        self.sum += other.sum;
    }

    /// Computes the union of this cage and another, that is, returns a new
    /// cage with the cells contained both in this and the other cage and the
    /// sum of their totals.
    ///
    /// It is expected that both cages are disjunct, i.e. do not share cells,
    /// otherwise the result will be wrong.
    pub fn union(&self, other: &KillerCage) -> KillerCage {
        let mut res = self.clone();
        let other = other.clone();
        res.join(other);
        res
    }

    fn any_cell(&self) -> (usize, usize) {
        self.group[0]
    }
}

/// An enumeration of the errors that can occur when handling the
/// [KillerConstraint] and related structs.
#[derive(Debug, Eq, PartialEq)]
pub enum KillerError {

    /// Indicates that a cage was added to a [KillerConstraint] that contains a
    /// cell which was already part of a different cage.
    CollidingCages,

    /// Indicates that a [KillerCage] was created without any cells.
    EmptyCage,

    /// Indicates that a [KillerCage] was created where a cell was contained
    /// twice.
    DuplicateCells
}

/// A reducible [Constraint](crate:constraint::Constraint) which adds
/// [KillerCage]s to the grid, which contain some cells and annotate some sum.
/// The constraint requires that the sum of all digits in a cage is equal to
/// the annotated number. Additionally, digits may not repeat in a cage.
///
/// As an example, the following Sudoku contains three cages. The top one is
/// satisfied, the middle one is violated because the sum is too high, and the
/// bottom one is violated because it contains repeated digits. Since a Killer
/// constraint requires all cages to be satisfied, the constraint itself would
/// be violated in this situation.
///
/// ```text
/// ╔═══════╤═══════╤═══════╦═══════╤═══════╤═══════╦═══════╤═══════╤═══════╗
/// ║╭14────┼───────┼──────╮║       │       │       ║       │       │       ║
/// ║│  5   │   4   │   3  │║       │       │       ║       │       │       ║
/// ║╰──────┼╮     ╭┼──────╯║       │       │       ║       │       │       ║
/// ╟───────┼┼─────┼┼───────╫───────┼───────┼───────╫───────┼───────┼───────╢
/// ║       ││     ││       ║       │       │       ║       │       │       ║
/// ║       ││  2  ││       ║       │       │       ║       │       │       ║
/// ║       │╰─────╯│       ║       │       │       ║       │       │       ║
/// ╟───────┼───────┼───────╫───────┼───────┼───────╫───────┼───────┼───────╢
/// ║       │       │╭30────╫──────╮│       │       ║       │       │       ║
/// ║       │       ││  9   ║   4  ││       │       ║       │       │       ║
/// ║       │       ││      ║      ││       │       ║       │       │       ║
/// ╠═══════╪═══════╪╪══════╬══════╪╪═══════╪═══════╬═══════╪═══════╪═══════╣
/// ║       │       ││      ║      ││       │       ║       │       │       ║
/// ║       │       ││  1   ║   3  ││       │       ║       │       │       ║
/// ║       │       ││      ║      ││       │       ║       │       │       ║
/// ╟───────┼───────┼┼──────╫──────┼┼───────┼───────╫───────┼───────┼───────╢
/// ║       │       ││      ║      ││       │       ║       │       │       ║
/// ║       │       ││  2   ║   7  ││       │       ║       │       │       ║
/// ║       │       │╰──────╫──────╯│       │       ║       │       │       ║
/// ╟───────┼───────┼───────╫───────┼───────┼───────╫───────┼───────┼───────╢
/// ║       │       │       ║       │╭25────┼───────╫──────╮│       │       ║
/// ║       │       │       ║       ││  6   │   1   ║   3  ││       │       ║
/// ║       │       │       ║       │╰──────┼╮      ║      ││       │       ║
/// ╠═══════╪═══════╪═══════╬═══════╪═══════╪╪══════╬══════╪╪═══════╪═══════╣
/// ║       │       │       ║       │       ││      ║      ││       │       ║
/// ║       │       │       ║       │       ││  3   ║   4  ││       │       ║
/// ║       │       │       ║       │       │╰──────╫╮     ││       │       ║
/// ╟───────┼───────┼───────╫───────┼───────┼───────╫┼─────┼┼───────┼───────╢
/// ║       │       │       ║       │       │       ║│     ││       │       ║
/// ║       │       │       ║       │       │       ║│  8  ││       │       ║
/// ║       │       │       ║       │       │       ║╰─────╯│       │       ║
/// ╟───────┼───────┼───────╫───────┼───────┼───────╫───────┼───────┼───────╢
/// ║       │       │       ║       │       │       ║       │       │       ║
/// ║       │       │       ║       │       │       ║       │       │       ║
/// ║       │       │       ║       │       │       ║       │       │       ║
/// ╚═══════╧═══════╧═══════╩═══════╧═══════╧═══════╩═══════╧═══════╧═══════╝
/// ```
#[derive(Clone)]
pub struct KillerConstraint {
    cages: Vec<KillerCage>,
    cell_assignment: HashMap<(usize, usize), usize>
}

impl KillerConstraint {

    /// Creates a new Killer constraint without any cages.
    pub fn new() -> KillerConstraint {
        KillerConstraint {
            cages: Vec::new(),
            cell_assignment: HashMap::new()
        }
    }

    /// Creates a new Killer constraint which contains one cage for every
    /// filled cell in the given grid whose sum is equal to the digit in that
    /// specific cell.
    pub fn new_singletons(grid: &SudokuGrid) -> KillerConstraint {
        let mut constraint = KillerConstraint::new();
        let size = grid.size();

        for column in 0..size {
            for row in 0..size {
                if let Some(number) = grid.get_cell(column, row).unwrap() {
                    let cage = KillerCage::new(vec![(column, row)], number)
                        .unwrap();
                    constraint.add_cage_unchecked(cage);
                }
            }
        }

        constraint
    }

    /// Returns the index of the cage that the cell at the given location is
    /// part of. If the cell is not contained in any cage, `None` is returned.
    pub fn cage_index_at(&self, column: usize, row: usize) -> Option<usize> {
        self.cell_assignment.get(&(column, row)).cloned()
    }

    /// Returns the cage that the cell at the given location is part of. If the
    /// cell is not contained in any cage, `None` is returned.
    pub fn cage_at(&self, column: usize, row: usize) -> Option<&KillerCage> {
        self.cage_index_at(column, row)
            .and_then(|i| self.cages.get(i))
    }

    /// Returns the [KillerCage]s enforced by this Killer constraint.
    pub fn cages(&self) -> &Vec<KillerCage> {
        &self.cages
    }

    /// Removes the cage with the given index (relating to the vector returned
    /// by [KillerConstraint::cages]) from this Killer constraint. The removed
    /// cage is returned. This method panics if the `index` is out of bounds.
    pub fn remove_cage(&mut self, index: usize) -> KillerCage {
        let cage = self.cages.remove(index);

        for cell in cage.group() {
            self.cell_assignment.remove(cell);
        }

        for (_, cage_index) in self.cell_assignment.iter_mut() {
            if *cage_index > index {
                *cage_index -= 1;
            }
        }

        cage
    }

    /// Adds the given cage to this Killer constraint. The given cage must be
    /// disjunct from any other cages in this constraint.
    ///
    /// # Errors
    ///
    /// `KillerError::CollidingCages` if the given cage contains a cell that is
    /// already assigned to a different cage.
    pub fn add_cage(&mut self, cage: KillerCage) -> Result<(), KillerError> {
        if cage.group().iter().any(|c| self.cell_assignment.contains_key(c)) {
            return Err(KillerError::CollidingCages);
        }

        self.add_cage_unchecked(cage);
        Ok(())
    }

    fn add_cage_unchecked(&mut self, cage: KillerCage) {
        let index = self.cages.len();

        for cell in cage.group() {
            self.cell_assignment.insert(*cell, index);
        }

        self.cages.push(cage);
    }

    fn cage_index_for_reduction(&self, (column, row): &(usize, usize))
            -> Result<usize, ReductionError> {
        self.cage_index_at(*column, *row)
            .ok_or_else(|| ReductionError::InvalidReduction)
    }

    fn adjacent_cages(&self)
            -> impl Iterator<Item = (&KillerCage, &KillerCage)> {
        let mut cages = HashSet::new();

        for (index, cage) in self.cages.iter().enumerate() {
            for &(column, row) in cage.group() {
                // TODO remove duplication somehow

                if let Some(&other) = self.cell_assignment.get(&(column + 1, row)) {
                    if index != other {
                        cages.insert((index, other));
                    }
                }

                if let Some(&other) = self.cell_assignment.get(&(column, row + 1)) {
                    if index != other {
                        cages.insert((index, other));
                    }
                }
            }
        }

        cages.into_iter()
            .map(move |(i, j)| (&self.cages[i], &self.cages[j]))
    }
}

/// The reduction type of the [KillerConstraint]. That is, instances of this
/// type encode possible reductions that can be applied to a Killer constraint.
///
/// This is mostly an implementation detail that is public due to the public
/// implementation of [Constraint](crate::constraint::Constraint).
pub enum KillerReduction {

    /// Merges two cages into one as identified by a representative cell for
    /// each one.
    MergeCages {

        /// The coordinates of the form `(column, row)` of a cell in the first
        /// cage to merge.
        cage_1_cell: (usize, usize),

        /// The coordinates of the form `(column, row)` of a cell in the second
        /// cage to merge.
        cage_2_cell: (usize, usize)
    },

    /// Removes a cage identified by a reprecentative cell.
    RemoveCage {

        /// The column index of a cell in the cage to remove.
        column: usize,

        /// The row index of a cell in the cage to remove.
        row: usize
    }
}

/// Returns the sum of all digits and the number of missing cells in the group.
fn eval_cage(cage: &KillerCage, grid: &SudokuGrid)
        -> SudokuResult<(usize, usize)> {
    let mut sum = 0;
    let mut missing = 0;

    for &(column, row) in cage.group() {
        if let Some(n) = grid.get_cell(column, row)? {
            sum += n;
        }
        else {
            missing += 1;
        }
    }

    Ok((sum, missing))
}

fn sum_valid(sum: usize, missing: usize, size: usize, cage: &KillerCage)
        -> bool {
    let missing_min_sum = missing * (missing + 1) / 2;
    let missing_max_sum = missing * size -
        missing * missing.overflowing_sub(1).0 / 2;

    if sum + missing_min_sum > cage.sum() {
        false
    }
    else if sum + missing_max_sum < cage.sum() {
        false
    }
    else {
        true
    }
}

fn contains_duplicate_number(cage: &KillerCage, grid: &SudokuGrid) -> bool {
    let mut numbers = USizeSet::new(1, grid.size()).unwrap();

    for &(column, row) in cage.group() {
        if let Some(number) = grid.get_cell(column, row).unwrap() {
            if !numbers.insert(number).unwrap() {
                return true;
            }
        }
    }

    false
}

fn is_valid(cage: &KillerCage, grid: &SudokuGrid) -> bool {
    if contains_duplicate_number(cage, grid) {
        return false;
    }

    let (sum, missing) = eval_cage(cage, grid).unwrap();
    sum_valid(sum, missing, grid.size(), cage)
}

impl Constraint for KillerConstraint {

    type Reduction = KillerReduction;
    type RevertInfo = Vec<KillerCage>;

    fn check(&self, grid: &SudokuGrid) -> bool {
        for cage in self.cages.iter() {
            if !is_valid(cage, grid) {
                return false;
            }
        }

        true
    }

    fn check_cell(&self, grid: &SudokuGrid, column: usize, row: usize)
            -> bool {
        if let Some(cage) = self.cage_at(column, row) {
            is_valid(cage, grid)
        }
        else {
            true
        }
    }

    fn check_number(&self, grid: &SudokuGrid, column: usize, row: usize,
            number: usize) -> bool {
        if let Some(cage) = self.cage_at(column, row) {
            let (mut sum, mut missing) = eval_cage(cage, grid).unwrap();
            let content = grid.get_cell(column, row).unwrap();

            if let Some(content) = content {
                sum -= content;
            }
            else {
                missing -= 1;
            }

            sum += number;

            if !sum_valid(sum, missing, grid.size(), cage) {
                return false;
            }

            let mut numbers = USizeSet::new(1, grid.size()).unwrap();

            for &(cell_column, cell_row) in cage.group() {
                let number = if cell_column == column && cell_row == row {
                    Some(number)
                }
                else {
                    grid.get_cell(cell_column, cell_row).unwrap()
                };

                if let Some(number) = number {
                    if !numbers.insert(number).unwrap() {
                        return false;
                    }
                }
            }
        }

        true
    }

    fn get_groups(&self, _: &SudokuGrid) -> Vec<Group> {
        self.cages.iter()
            .map(KillerCage::group)
            .cloned()
            .collect()
    }

    fn list_reductions(&self, _: &SudokuGrid) -> Vec<KillerReduction> {
        let mut reductions = Vec::new();

        for (cage_1, cage_2) in self.adjacent_cages() {
            reductions.push(KillerReduction::MergeCages {
                cage_1_cell: cage_1.any_cell(),
                cage_2_cell: cage_2.any_cell()
            })
        }

        for cage in self.cages() {
            let (column, row) = cage.any_cell();

            reductions.push(KillerReduction::RemoveCage {
                column,
                row
            })
        }

        reductions
    }

    fn reduce(&mut self, solution: &SudokuGrid, reduction: &KillerReduction)
            -> Result<Vec<KillerCage>, ReductionError> {
        match reduction {
            KillerReduction::MergeCages { cage_1_cell, cage_2_cell } => {
                let cage_1_idx =
                    self.cage_index_for_reduction(cage_1_cell)?;
                let cage_2_idx =
                    self.cage_index_for_reduction(cage_2_cell)?;

                if cage_1_idx == cage_2_idx {
                    return Err(ReductionError::InvalidReduction);
                }

                let union =
                    self.cages[cage_1_idx].union(&self.cages[cage_2_idx]);

                if contains_duplicate_number(&union, solution) {
                    return Err(ReductionError::InvalidReduction);
                }

                // Higher index needs to be removed first to avoid OBOE
                let (cage_1_idx, cage_2_idx) = if cage_1_idx > cage_2_idx {
                    (cage_1_idx, cage_2_idx)
                }
                else {
                    (cage_2_idx, cage_1_idx)
                };
                let cage_1 = self.remove_cage(cage_1_idx);
                let cage_2 = self.remove_cage(cage_2_idx);
                self.add_cage(union).unwrap();
                Ok(vec![cage_1, cage_2])
            },
            &KillerReduction::RemoveCage { column, row } => {
                let cage_idx = self.cage_index_for_reduction(&(column, row))?;
                let cage = self.remove_cage(cage_idx);
                Ok(vec![cage])
            }
        }
    }

    fn revert(&mut self, _: &SudokuGrid, reduction: &KillerReduction,
            revert_info: Vec<KillerCage>) {
        if let KillerReduction::MergeCages { .. } = reduction {
            // We use that revert(...) is called immediately after reduce(...),
            // thus ensuring the new cage is still the first one
            self.remove_cage(self.cages().len() - 1);
        }

        for cage in revert_info {
            self.add_cage_unchecked(cage);
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn valid_killer_cage() {
        let cage = KillerCage::new(vec![(0, 0), (0, 1)], 10).unwrap();

        assert_eq!(&vec![(0, 0), (0, 1)], cage.group());
        assert_eq!(10, cage.sum());
    }

    #[test]
    fn invalid_killer_cage() {
        assert_eq!(Err(KillerError::EmptyCage),
            KillerCage::new(Vec::new(), 0));
        assert_eq!(Err(KillerError::DuplicateCells),
            KillerCage::new(vec![(0, 0), (0, 1), (0, 0)], 10));
    }

    #[test]
    fn killer_cage_union() {
        let cage_1 = KillerCage::new(vec![(0, 0), (0, 1)], 15).unwrap();
        let cage_2 = KillerCage::new(vec![(1, 0), (1, 1)], 6).unwrap();
        let union = cage_1.union(&cage_2);

        assert_eq!(4, union.group().len());
        assert!(union.group().contains(&(0, 0)));
        assert!(union.group().contains(&(0, 1)));
        assert!(union.group().contains(&(1, 0)));
        assert!(union.group().contains(&(1, 1)));
        assert_eq!(21, union.sum());
    }

    fn valid_constraint() -> KillerConstraint {
        let mut constraint = KillerConstraint::new();
        constraint.add_cage(KillerCage::new(vec![(0, 0), (0, 1)], 15).unwrap())
            .unwrap();
        constraint.add_cage(KillerCage::new(vec![(1, 0), (1, 1)], 6).unwrap())
            .unwrap();
        constraint
    }

    #[test]
    fn valid_cage_addition() {
        valid_constraint();
    }

    #[test]
    fn invalid_cage_addition() {
        let mut constraint = KillerConstraint::new();
        constraint.add_cage(KillerCage::new(vec![(0, 0), (0, 1)], 15).unwrap())
            .unwrap();

        assert_eq!(Err(KillerError::CollidingCages),
            constraint.add_cage(
                KillerCage::new(vec![(1, 0), (0, 1)], 6).unwrap()));
    }

    #[test]
    fn cage_removal() {
        let mut constraint = valid_constraint();
        constraint.add_cage(KillerCage::new(vec![(2, 0), (2, 1)], 10).unwrap())
            .unwrap();

        assert_eq!(3, constraint.cages().len());
        assert!(constraint.cage_at(1, 1).is_some());
        assert!(constraint.cage_at(2, 1).is_some());

        constraint.remove_cage(1);

        assert_eq!(2, constraint.cages().len());
        assert!(constraint.cage_at(1, 1).is_none());
        assert!(constraint.cage_at(2, 1).is_some());
        assert_eq!(1, constraint.cage_index_at(2, 1).unwrap());
    }

    #[test]
    fn singleton_constraint() {
        let grid = SudokuGrid::parse("2x2;
             , ,2, ,\
            1, , ,3,\
             ,4, ,1,\
             , ,3, ").unwrap();
        let constraint = KillerConstraint::new_singletons(&grid);

        assert_eq!(6, constraint.cages().len());

        let expected_cages = vec![
            (2, 0, 2),
            (0, 1, 1),
            (3, 1, 3),
            (1, 2, 4),
            (3, 2, 1),
            (2, 3, 3)
        ];

        for (column, row, sum) in expected_cages {
            assert!(constraint.cages().contains(
                &KillerCage::new(vec![(column, row)], sum).unwrap()));
        }
    }

    fn is_merge(reduction: &KillerReduction, constraint: &KillerConstraint,
            index_1: usize, index_2: usize) -> bool {
        match reduction {
            &KillerReduction::MergeCages { cage_1_cell, cage_2_cell } => {
                let (cage_1_column, cage_1_row) = cage_1_cell;
                let cage_1_index =
                    constraint.cage_index_at(cage_1_column, cage_1_row)
                        .unwrap();
                let (cage_2_column, cage_2_row) = cage_2_cell;
                let cage_2_index =
                    constraint.cage_index_at(cage_2_column, cage_2_row)
                        .unwrap();
                cage_1_index == index_1 && cage_2_index == index_2 ||
                    cage_1_index == index_2 && cage_2_index == index_1
            },
            &KillerReduction::RemoveCage { .. } => false
        }
    }

    fn is_remove(reduction: &KillerReduction, constraint: &KillerConstraint,
            index: usize) -> bool {
        match reduction {
            &KillerReduction::MergeCages { .. } => false,
            &KillerReduction::RemoveCage { column, row } => {
                let cage_index = constraint.cage_index_at(column, row)
                    .unwrap();
                cage_index == index
            }
        }
    }

    #[test]
    fn correct_reduction_list() {
        // Cage layout:
        // 
        // ╔═══╤═══╦═══╤═══╗
        // ║ 0 │ 1 ║   │   ║
        // ╟───┼───╫───┼───╢
        // ║ 0 │ 1 ║   │   ║
        // ╠═══╪═══╬═══╪═══╣
        // ║ 2 │ 2 ║ 3 │ 3 ║
        // ╟───┼───╫───┼───╢
        // ║   │   ║   │   ║
        // ╚═══╧═══╩═══╧═══╝

        let mut constraint = valid_constraint();
        constraint.add_cage(KillerCage::new(vec![(0, 2), (1, 2)], 5).unwrap())
            .unwrap();
        constraint.add_cage(KillerCage::new(vec![(2, 2), (3, 2)], 12).unwrap())
            .unwrap();
        let reductions =
            constraint.list_reductions(&SudokuGrid::new(2, 2).unwrap());

        assert_eq!(8, reductions.len());
        assert!(reductions.iter().any(|r| is_merge(r, &constraint, 0, 1)));
        assert!(reductions.iter().any(|r| is_merge(r, &constraint, 0, 2)));
        assert!(reductions.iter().any(|r| is_merge(r, &constraint, 1, 2)));
        assert!(reductions.iter().any(|r| is_merge(r, &constraint, 2, 3)));

        for i in 0..4 {
            assert!(reductions.iter().any(|r| is_remove(r, &constraint, i)));
        }
    }

    fn complex_constraint_do() -> Result<KillerConstraint, KillerError> {
        // Cage layout:
        // 
        // ╔═══╤═══╦═══╤═══╗
        // ║ 0 │ 0 ║ 0 │   ║
        // ╟───┼───╫───┼───╢
        // ║   │ 1 ║ 1 │   ║
        // ╠═══╪═══╬═══╪═══╣
        // ║   │   ║ 1 │   ║
        // ╟───┼───╫───┼───╢
        // ║   │   ║ 2 │ 2 ║
        // ╚═══╧═══╩═══╧═══╝
        // 
        // Sums:
        //
        // 0 : 7
        // 1 : 9
        // 2 : 5

        let mut c = KillerConstraint::new();
        c.add_cage(KillerCage::new(vec![(0, 0), (1, 0), (2, 0)], 7)?)?;
        c.add_cage(KillerCage::new(vec![(1, 1), (2, 1), (2, 2)], 9)?)?;
        c.add_cage(KillerCage::new(vec![(2, 3), (3, 3)], 5)?)?;
        Ok(c)
    }

    fn complex_constraint() -> KillerConstraint {
        complex_constraint_do().unwrap()
    }

    #[test]
    fn killer_constraint_satisfied_empty() {
        let constraint = complex_constraint();
        let grid = SudokuGrid::parse("2x2;
             , , , ,\
             , , , ,\
             , , , ,\
             , , , ").unwrap();

        assert!(constraint.check(&grid));
    }

    #[test]
    fn killer_constraint_satisfied_full() {
        let constraint = complex_constraint();
        let mut grid = SudokuGrid::parse("2x2;
            1,4,2,1,\
            1,2,4,1,\
            1,1,3,1,\
            1,1,1,4").unwrap();

        assert!(constraint.check(&grid));
        assert!(constraint.check_cell(&grid, 0, 0));
        assert!(constraint.check_cell(&grid, 2, 1));
        assert!(constraint.check_cell(&grid, 1, 3));

        grid.clear_cell(0, 0).unwrap();
        grid.set_cell(1, 1, 4).unwrap();

        assert!(constraint.check_number(&grid, 0, 0, 1));
        assert!(constraint.check_number(&grid, 1, 1, 2));
    }

    #[test]
    fn killer_constraint_satisfied_partial() {
        let constraint = complex_constraint();
        let grid = SudokuGrid::parse("2x2;
            1, ,2, ,\
             ,4, , ,\
             , , , ,\
             , ,2, ").unwrap();

        assert!(constraint.check(&grid));
        assert!(constraint.check_cell(&grid, 0, 0));
        assert!(constraint.check_cell(&grid, 2, 1));
        assert!(constraint.check_number(&grid, 1, 1, 4));
        assert!(constraint.check_number(&grid, 2, 3, 1));
    }

    #[test]
    fn killer_constraint_violated_sum_full() {
        let constraint = complex_constraint();
        let grid = SudokuGrid::parse("2x2;
            3,4,2,1,\
            1,2,4,1,\
            1,1,3,1,\
            1,1,1,4").unwrap();

        assert!(!constraint.check(&grid));
        assert!(!constraint.check_cell(&grid, 1, 0));
        assert!(constraint.check_cell(&grid, 2, 1));
        assert!(!constraint.check_number(&grid, 1, 0, 1));
        assert!(!constraint.check_number(&grid, 1, 1, 1));
        assert!(!constraint.check_number(&grid, 2, 3, 2));
    }

    #[test]
    fn killer_constraint_violated_sum_partial() {
        let constraint = complex_constraint();
        let grid = SudokuGrid::parse("2x2;
             , ,3, ,\
             , ,1, ,\
             , , , ,\
             , , ,4").unwrap();

        assert!(!constraint.check(&grid));
        assert!(constraint.check_cell(&grid, 2, 0));
        assert!(!constraint.check_cell(&grid, 1, 1));
        assert!(!constraint.check_number(&grid, 1, 0, 4));
        assert!(!constraint.check_number(&grid, 1, 1, 3));
    }

    #[test]
    fn killer_constraint_violated_repeat_full() {
        let constraint = complex_constraint();
        let mut grid = SudokuGrid::parse("2x2;
            2,3,2,1,\
            1,2,4,1,\
            1,1,3,1,\
            1,1,1,4").unwrap();

        assert!(!constraint.check(&grid));
        assert!(!constraint.check_cell(&grid, 0, 0));
        assert!(constraint.check_cell(&grid, 1, 1));

        grid.set_cell(0, 0, 1).unwrap();
        grid.set_cell(1, 0, 3).unwrap();

        assert!(!constraint.check_number(&grid, 2, 0, 3));
    }

    #[test]
    fn killer_constraint_violated_repeat_partial() {
        let constraint = complex_constraint();
        let grid = SudokuGrid::parse("2x2;
            3, ,3, ,\
             , , , ,\
             , ,3, ,\
             , , ,1").unwrap();

        assert!(!constraint.check(&grid));
        assert!(!constraint.check_cell(&grid, 0, 0));
        assert!(constraint.check_cell(&grid, 1, 1));
        assert!(!constraint.check_number(&grid, 1, 1, 3));
    }

    fn mergeable_constraint_do() -> Result<KillerConstraint, KillerError> {
        // Cage layout:
        //
        // ╔═══╤═══╤═══╦═══╤═══╤═══╗
        // ║   │ 0 │ 0 ║   │   │   ║
        // ╟───┼───┼───╫───┼───┼───╢
        // ║   │   │ 0 ║ 1 │ 1 │   ║
        // ╠═══╪═══╪═══╬═══╪═══╪═══╣
        // ║   │   │   ║   │   │   ║
        // ╟───┼───┼───╫───┼───┼───╢
        // ║   │   │ 2 ║ 2 │ 2 │   ║
        // ╠═══╪═══╪═══╬═══╪═══╪═══╣
        // ║   │   │   ║   │ 2 │   ║
        // ╟───┼───┼───╫───┼───┼───╢
        // ║ 3 │ 3 │ 3 ║   │   │   ║
        // ╚═══╧═══╧═══╩═══╧═══╧═══╝
        //
        // Sums:
        //
        // 0 : 9
        // 1 : 7
        // 2 : 16
        // 3 : 6

        let mut c = KillerConstraint::new();
        c.add_cage(KillerCage::new(vec![(1, 0), (2, 0), (2, 1)], 9)?)?;
        c.add_cage(KillerCage::new(vec![(3, 1), (4, 1)], 7)?)?;
        c.add_cage(
            KillerCage::new(vec![(2, 3), (3, 3), (4, 3), (4, 4)], 16)?)?;
        c.add_cage(KillerCage::new(vec![(0, 5), (1, 5), (2, 5)], 6)?)?;
        Ok(c)
    }

    fn mergeable_constraint() -> KillerConstraint {
        mergeable_constraint_do().unwrap()
    }

    fn mergeable_constraint_solution() -> SudokuGrid {
        SudokuGrid::parse("3x2;
            1,2,3,1,1,1,\
            1,1,4,1,6,1,\
            1,1,1,1,1,1,\
            1,1,2,3,5,1,\
            1,1,1,1,6,1,\
            1,2,3,1,1,1").unwrap()
    }

    fn reduced_constraint(reduction: &KillerReduction)
            -> (KillerConstraint, Vec<KillerCage>, SudokuGrid) {
        let mut constraint = mergeable_constraint();
        let solution = mergeable_constraint_solution();
        
        if let Ok(revert_info) = constraint.reduce(&solution, reduction) {
            (constraint, revert_info, solution)
        }
        else {
            panic!("Valid reduction considered invalid.")
        }
    }

    fn merged_constraint()
            -> (KillerConstraint, Vec<KillerCage>, KillerReduction,
                SudokuGrid) {
        let reduction = KillerReduction::MergeCages {
            cage_1_cell: (1, 0),
            cage_2_cell: (3, 1)
        };
        let (constraint, revert_info, solution) =
            reduced_constraint(&reduction);
        (constraint, revert_info, reduction, solution)
    }

    #[test]
    fn merge_applied_correctly() {
        let (constraint, _, _, _) = merged_constraint();

        assert_eq!(3, constraint.cages().len());
        assert_eq!(0, constraint.cage_index_at(2, 3).unwrap());
        assert_eq!(1, constraint.cage_index_at(0, 5).unwrap());
        assert_eq!(2, constraint.cage_index_at(1, 0).unwrap());
        assert_eq!(2, constraint.cage_index_at(3, 1).unwrap());

        let merged_cage = constraint.cage_at(1, 0).unwrap();

        assert_eq!(5, merged_cage.group().len());
        assert_eq!(16, merged_cage.sum());
    }

    #[test]
    fn merge_reverted_correctly() {
        let (mut constraint, revert_info, reduction, solution) =
            merged_constraint();
        constraint.revert(&solution, &reduction, revert_info);

        assert_eq!(4, constraint.cages().len());
        assert_eq!(0, constraint.cage_index_at(2, 3).unwrap());
        assert_eq!(1, constraint.cage_index_at(0, 5).unwrap());

        let cage_1 = constraint.cage_at(1, 0).unwrap();
        let cage_2 = constraint.cage_at(3, 1).unwrap();

        assert_eq!(3, cage_1.group().len());
        assert_eq!(2, cage_2.group().len());
        assert_eq!(9, cage_1.sum());
        assert_eq!(7, cage_2.sum());
    }

    fn removed_constraint()
            -> (KillerConstraint, Vec<KillerCage>, KillerReduction,
                SudokuGrid) {
        let reduction = KillerReduction::RemoveCage {
            column: 3,
            row: 1
        };
        let (constraint, revert_info, solution) =
            reduced_constraint(&reduction);
        (constraint, revert_info, reduction, solution)
    }

    #[test]
    fn remove_applied_correctly() {
        let (constraint, _, _, _) = removed_constraint();

        assert_eq!(3, constraint.cages().len());
        assert_eq!(0, constraint.cage_index_at(1, 0).unwrap());
        assert_eq!(1, constraint.cage_index_at(2, 3).unwrap());
        assert_eq!(2, constraint.cage_index_at(0, 5).unwrap());
        assert_eq!(None, constraint.cage_index_at(3, 1));
    }

    #[test]
    fn remove_reverted_correctly() {
        let (mut constraint, revert_info, reduction, solution) =
            removed_constraint();
        constraint.revert(&solution, &reduction, revert_info);

        assert_eq!(4, constraint.cages().len());
        assert_eq!(0, constraint.cage_index_at(1, 0).unwrap());
        assert_eq!(1, constraint.cage_index_at(2, 3).unwrap());
        assert_eq!(2, constraint.cage_index_at(0, 5).unwrap());
        assert_eq!(3, constraint.cage_index_at(3, 1).unwrap());

        let restored_cage = constraint.cage_at(3, 1).unwrap();

        assert_eq!(2, restored_cage.group().len());
        assert_eq!(7, restored_cage.sum());
    }
}
