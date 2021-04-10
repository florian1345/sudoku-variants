//! This module contains the implementation of the [ThermoConstraint] as well
//! as all auxiliary data structures. It is re-exported in the
//! [constraint](crate::constraint), so you should not have to reference this
//! module directly.

use crate::SudokuGrid;
use crate::constraint::{Constraint, Group, ReductionError};
use crate::util;

use serde::{Deserialize, Serialize};

use std::collections::{HashMap, HashSet};
use std::convert::TryFrom;
use std::fmt::{self, Display, Formatter};
use std::iter;

/// An enumeration of the different errors that can occur when handling
/// [ThermoConstraint]s and related structs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ThermoError {

    /// Indicates that a [Thermometer] was added to a [ThermoConstraint] which
    /// collides with another one (except for two bulbs being on the same cell,
    /// which is allowed).
    CollidingThermometers,

    /// Indicates that a [Thermometer] contains a cycle, i.e. the same cell
    /// twice.
    CyclicThermometer,

    /// Indicates that the cells in a [Thermometer] are not connected in the
    /// order they were provided.
    DisconnectedThermometer,

    /// Indicates that a [Thermometer] was added to a [ThermoConstraint] which
    /// was fully contained in some other thermometer, making it redundant, or
    /// which made some other thermometer redundant.
    RedundantThermometer,

    /// Indicates that a [Thermometer] contained too little cells (2 are
    /// required).
    ThermometerTooShort
}

impl Display for ThermoError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            ThermoError::CollidingThermometers =>
                write!(f, "colliding thermometers"),
            ThermoError::CyclicThermometer =>
                write!(f, "cyclic thermometer"),
            ThermoError::DisconnectedThermometer =>
                write!(f, "disconnected thermometer"),
            ThermoError::RedundantThermometer =>
                write!(f, "redundant thermometer"),
            ThermoError::ThermometerTooShort =>
                write!(f, "thermometer too short"),
        }
    }
}

/// Represents a single thermometer on a [ThermoConstraint] on which numbers
/// must strictly increase.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(into = "Vec<(usize, usize)>")]
#[serde(try_from = "Vec<(usize, usize)>")]
pub struct Thermometer {
    cells: Vec<(usize, usize)>
}

impl Thermometer {

    /// Creates a new thermometer with the given cells. They are provided in
    /// the format `(column, row)`, with the first cell representing the bulb
    /// and the rest going in increasing order along the thermometer. The cells
    /// must be connected (orthogonally or diagonally) in the order they are
    /// provided. Additionally, they must be non-cyclic, i.e. the thermometer
    /// never returns to a cell previously contained, and there must be at
    /// least 2 cells - one bulb and at least one more. If any of these
    /// conditions is not satisfied, an appropriate [ThermoError] is returned.
    pub fn new(cells: Vec<(usize, usize)>)
            -> Result<Thermometer, ThermoError> {
        if util::contains_duplicate(cells.iter()) {
            return Err(ThermoError::CyclicThermometer);
        }

        if cells.len() < 2 {
            return Err(ThermoError::ThermometerTooShort);
        }

        let mut iter = cells.iter();
        let &(mut prev_column, mut prev_row) = iter.next().unwrap();

        for &(column, row) in iter {
            if util::abs_diff(column, prev_column) > 1 ||
                    util::abs_diff(row, prev_row) > 1 {
                return Err(ThermoError::DisconnectedThermometer);
            }

            prev_column = column;
            prev_row = row;
        }

        Ok(Thermometer {
            cells
        })
    }

    /// Gets the number of cells along this thermometer, including the bulb.
    pub fn len(&self) -> usize {
        self.cells.len()
    }

    /// Gets the cells of the thermometer in increasing order, starting from
    /// the bulb.
    pub fn cells(&self) -> &Vec<(usize, usize)> {
        &self.cells
    }

    fn shorten(&mut self) -> bool {
        if self.len() > 2 {
            self.cells.pop();
            true
        }
        else {
            false
        }
    }

    fn add_cell_unchecked(&mut self, column: usize, row: usize) {
        self.cells.push((column, row))
    }
}

impl From<Thermometer> for Vec<(usize, usize)> {
    fn from(thermometer: Thermometer) -> Vec<(usize, usize)> {
        thermometer.cells
    }
}

impl TryFrom<Vec<(usize, usize)>> for Thermometer {
    type Error = ThermoError;

    fn try_from(cells: Vec<(usize, usize)>)
            -> Result<Thermometer, ThermoError> {
        Thermometer::new(cells)
    }
}

/// A reducible [Constraint] which adds [Thermometer] to the grid. Along each
/// thermometer the numbers must strictly increase from bulb to end.
///
/// As an example, the Sudoku below contains two thermometers. The top one is
/// satisfied and the bottom one is violated. A thermo constraint is satisfied
/// if and only if all thermometers are satisfied, so the example grid violates
/// the thermo constraint.
///
/// ```text
/// ╔═══════╤═══════╦═══════╤═══════╗
/// ║  ▒▒▒  │       ║       │       ║
/// ║ ▒▒1▒▒▒│▒▒▒2   ║       │       ║
/// ║  ▒▒▒  │   ▒   ║       │       ║
/// ╟───────┼───────╫───────┼───────╢
/// ║       │   ▒   ║       │       ║
/// ║       │   3▒▒▒║▒▒▒4   │       ║
/// ║       │       ║       │       ║
/// ╠═══════╪═══════╬═══════╪═══════╣
/// ║       │       ║       │  ▒▒▒  ║
/// ║       │       ║       │ ▒▒1▒▒ ║
/// ║       │       ║       │  ▒▒▒  ║
/// ╟───────┼───────╫───────┼───────╢
/// ║       │       ║       │   ▒   ║
/// ║       │       ║   2▒▒▒│▒▒▒3   ║
/// ║       │       ║       │       ║
/// ╚═══════╧═══════╩═══════╧═══════╝
/// ```
#[derive(Clone, Deserialize, Serialize)]
#[serde(into = "Vec<Thermometer>")]
#[serde(try_from = "Vec<Thermometer>")]
pub struct ThermoConstraint {
    thermometers: Vec<Thermometer>,
    cell_assignment: HashMap<(usize, usize), HashSet<usize>>
}

impl ThermoConstraint {

    /// Creates a new thermo constraint without any thermometers.
    pub fn new() -> ThermoConstraint {
        ThermoConstraint {
            thermometers: Vec::new(),
            cell_assignment: HashMap::new()
        }
    }

    /// Verifies the given [Thermometer] for addition to this constraint. First
    /// it checks whether the thermometer collides with any other currently
    /// contained in this constraint. Two thermometers are said to collide if a
    /// bulb and non-bulb cell overlap or the same cell has different
    /// predecessors in different thermometers. Additionally, this method
    /// verifies whether the given thermometer is redundant, i.e. there is
    /// another which fully contains it. It also must not make any other
    /// thermometer redundant.
    pub fn verify(&self, thermometer: &Thermometer) -> Result<(), ThermoError> {
        let mut cells = thermometer.cells().iter();
        let empty = HashSet::new();
        let bulb = cells.next().unwrap();
        let bulb_sharer_indices = self.cell_assignment.get(bulb)
            .unwrap_or_else(|| &empty);
        let bulb_sharers: Vec<&Thermometer> = bulb_sharer_indices.iter()
            .map(|&i| &self.thermometers[i])
            .collect();

        for bulb_sharer in bulb_sharers {
            let other_bulb = &bulb_sharer.cells()[0];

            if bulb != other_bulb {
                return Err(ThermoError::CollidingThermometers);
            }
        }

        let mut prev_sharer_indices = bulb_sharer_indices;

        for cell in cells {
            let sharer_indices = self.cell_assignment.get(cell)
                .unwrap_or_else(|| &empty);

            if !sharer_indices.is_subset(prev_sharer_indices) {
                return Err(ThermoError::CollidingThermometers);
            }

            for sharer_index in sharer_indices {
                let sharer = &self.thermometers[*sharer_index];

                if sharer.cells().last().unwrap() == cell {
                    return Err(ThermoError::RedundantThermometer);
                }
            }

            prev_sharer_indices = sharer_indices;
        }

        if prev_sharer_indices.is_empty() {
            Ok(())
        }
        else {
            Err(ThermoError::RedundantThermometer)
        }
    }

    fn insert(&mut self, cell: (usize, usize), index: usize) {
        if let Some(indices) = self.cell_assignment.get_mut(&cell) {
            indices.insert(index);
        }
        else {
            let mut indices = HashSet::new();
            indices.insert(index);
            self.cell_assignment.insert(cell, indices);
        }
    }

    fn remove(&mut self, cell: (usize, usize), index: usize) {
        let indices = self.cell_assignment.get_mut(&cell).unwrap();
        indices.remove(&index);

        if indices.is_empty() {
            self.cell_assignment.remove(&cell);
        }
    }

    /// Adds the given [Thermometer] to this constraint, that is, after this
    /// method the constraint will check that numbers along the given
    /// thermometer strictly increase. It must be valid according to
    /// [ThermoConstraint::verify].
    pub fn add_thermometer(&mut self, thermometer: Thermometer)
            -> Result<(), ThermoError> {
        self.verify(&thermometer)?;
        let index = self.thermometers.len();

        for &cell in thermometer.cells().iter() {
            self.insert(cell, index);
        }

        self.thermometers.push(thermometer);
        Ok(())
    }

    /// Gets a vector of all thermometers that contain the given cell. If there
    /// is no such thermometer, an empty vector will be returned.
    pub fn thermometers_at(&self, column: usize, row: usize)
            -> Vec<&Thermometer> {
        if let Some(thermometers) = self.cell_assignment.get(&(column, row)) {
            thermometers.iter()
                .map(|&i| &self.thermometers[i])
                .collect()
        }
        else {
            Vec::new()
        }
    }

    fn shorten_thermometer(&mut self, index: usize) -> ThermoRevertInfo {
        let cells = self.thermometers[index].cells().clone();
        let mut cells_iter_rev = cells.into_iter().rev();
        let last_cell = cells_iter_rev.next().unwrap();
        self.cell_assignment.remove(&last_cell);
        let second_last_cell = cells_iter_rev.next().unwrap();
        let becomes_redundant =
            self.cell_assignment.get(&second_last_cell).unwrap().len() > 1;

        if becomes_redundant || !self.thermometers[index].shorten() {
            self.remove(second_last_cell, index);

            for cell in cells_iter_rev {
                self.remove(cell, index);
            }

            for cell_indices in self.cell_assignment.values_mut() {
                let cell_index_vec: Vec<usize> =
                    cell_indices.iter().cloned().collect();

                for cell_index in cell_index_vec {
                    if cell_index > index {
                        cell_indices.remove(&cell_index);
                        cell_indices.insert(cell_index - 1);
                    }
                }
            }

            ThermoRevertInfo::Add(self.thermometers.remove(index))
        }
        else {
            let (column, row) = last_cell;

            ThermoRevertInfo::Extend {
                index,
                column,
                row
            }
        }
    }
}

impl From<ThermoConstraint> for Vec<Thermometer> {
    fn from(t: ThermoConstraint) -> Vec<Thermometer> {
        t.thermometers
    }
}

impl TryFrom<Vec<Thermometer>> for ThermoConstraint {
    type Error = ThermoError;

    fn try_from(thermometers: Vec<Thermometer>)
            -> Result<ThermoConstraint, ThermoError> {
        let mut constraint = ThermoConstraint::new();

        for thermometer in thermometers {
            constraint.add_thermometer(thermometer)?;
        }

        Ok(constraint)
    }
}

/// The reduction type of the [ThermoConstraint]. That is, instances of this
/// type encode possible reductions that can be applied to a Thermo constraint.
///
/// This is mostly an implementation detail that is public due to the public
/// implementation of [Constraint].
pub enum ThermoRevertInfo {

    /// Re-add a [Thermometer] that was previously removed.
    Add(Thermometer),

    /// Extend a [Thermometer] that was previously shortened.
    Extend {

        /// The internal index of the thermometer.
        index: usize,

        /// The column of the cell to be restored.
        column: usize,

        /// The row of the cell to be restored.
        row: usize
    }
}

fn check_thermometer(grid: &SudokuGrid, thermometer: &Thermometer) -> bool {
    let mut prev = 0;

    for &(column, row) in thermometer.cells() {
        if let Some(number) = grid.get_cell(column, row).unwrap() {
            if number <= prev {
                return false;
            }

            prev = number;
        }
    }

    true
}

/// Indicates whether the cell with the given `index` along the `thermometer`
/// is in the relation specified by `cmp` relative to `number`. If the cell is
/// not filled, this is considered to be true by default.
fn check_relative_cell(grid: &SudokuGrid, thermometer: &Thermometer,
        number: usize, index: usize, cmp: impl Fn(usize, usize) -> bool)
        -> bool {
    let (column, row) = thermometer.cells()[index];

    if let Some(relative_number) = grid.get_cell(column, row).unwrap() {
        cmp(relative_number, number)
    }
    else {
        true
    }
}

impl Constraint for ThermoConstraint {

    // The coordinates of the second cell (index 1) of the thermometer (the
    // first cell that is uniquely assigned to the thermometer).
    type Reduction = (usize, usize);

    type RevertInfo = ThermoRevertInfo;

    fn check(&self, grid: &SudokuGrid) -> bool {
        self.thermometers.iter()
            .all(|t| check_thermometer(grid, t))
    }

    fn check_number(&self, grid: &SudokuGrid, column: usize, row: usize,
            number: usize) -> bool {
        for thermometer in self.thermometers_at(column, row) {
            let cell_index = thermometer.cells().iter()
                .position(|e| e == &(column, row))
                .unwrap();

            for i in (cell_index + 1)..thermometer.len() {
                if !check_relative_cell(grid, thermometer, number, i,
                        |a, b| a > b) {
                    return false;
                }
            }

            for i in 0..cell_index {
                if !check_relative_cell(grid, thermometer, number, i,
                        |a, b| a < b) {
                    return false;
                }
            }
        }

        true
    }

    fn get_groups(&self, _: &SudokuGrid) -> Vec<Group> {
        Vec::new()
    }

    fn list_reductions(&self, _: &SudokuGrid) -> Vec<(usize, usize)> {
        self.thermometers.iter()
            .flat_map(|t| iter::repeat(t.cells()[0]).take(t.len() - 1))
            .collect()
    }

    fn reduce(&mut self, _: &SudokuGrid, reduction: &(usize, usize))
            -> Result<ThermoRevertInfo, ReductionError> {
        if let Some(indices) = self.cell_assignment.get(reduction) {
            let index = *indices.iter().next().unwrap();
            Ok(self.shorten_thermometer(index))
        }
        else {
            Err(ReductionError::InvalidReduction)
        }
    }

    fn revert(&mut self, _: &SudokuGrid, _: &(usize, usize),
            revert_info: ThermoRevertInfo) {
        match revert_info {
            ThermoRevertInfo::Add(thermometer) =>
                self.add_thermometer(thermometer).unwrap(),
            ThermoRevertInfo::Extend { index, column, row } => {
                self.thermometers[index].add_cell_unchecked(column, row);
                self.insert((column, row), index);
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use std::fmt::Debug;
    use std::hash::Hash;

    #[test]
    fn invalid_thermometers() {
        assert_eq!(Err(ThermoError::CyclicThermometer),
            Thermometer::new(vec![(0, 0), (0, 1), (1, 0), (0, 0)]));
        assert_eq!(Err(ThermoError::DisconnectedThermometer),
            Thermometer::new(vec![(1, 1), (2, 1), (2, 3), (3, 3)]));
        assert_eq!(Err(ThermoError::ThermometerTooShort),
            Thermometer::new(vec![(2, 2)]));
    }

    #[test]
    fn valid_thermometer() {
        assert!(Thermometer::new(vec![(1, 1), (2, 2)]).is_ok());
    }

    fn single_thermo_constraint() -> ThermoConstraint {
        let mut constraint = ThermoConstraint::new();
        constraint.add_thermometer(
            Thermometer::new(vec![(4, 0), (4, 1), (4, 2)]).unwrap()
        ).unwrap();
        constraint
    }

    #[test]
    fn invalid_additions() {
        let mut constraint = single_thermo_constraint();

        assert_eq!(Err(ThermoError::CollidingThermometers),
            constraint.add_thermometer(
                Thermometer::new(vec![(3, 0), (4, 1), (4, 2)]).unwrap()
            ));
        assert_eq!(Err(ThermoError::CollidingThermometers),
            constraint.add_thermometer(
                Thermometer::new(vec![(4, 1), (5, 1), (6, 1)]).unwrap()
            ));
        assert_eq!(Err(ThermoError::RedundantThermometer),
            constraint.add_thermometer(
                Thermometer::new(vec![(4, 0), (4, 1), (4, 2)]).unwrap()
            ));
        assert_eq!(Err(ThermoError::RedundantThermometer),
            constraint.add_thermometer(
                Thermometer::new(vec![(4, 0), (4, 1), (4, 2), (4, 3)]).unwrap()
            ));
    }

    #[test]
    fn valid_additions() {
        let mut constraint = single_thermo_constraint();
        constraint.add_thermometer(
            Thermometer::new(vec![(4, 0), (4, 1), (5, 1)]).unwrap()
        ).unwrap();
    }

    fn branching_constraint() -> ThermoConstraint {
        // Layout:
        // ╔═══╤═══╦═══╤═══╗
        // ║   │ O ║   │   ║
        // ╟───┼─╫─╫───┼───╢
        // ║ ╞═╪═╩═╬═╗ │   ║
        // ╠═══╪═══╬═╬═╪═══╣
        // ║   │   ║ ╨ │   ║
        // ╟───┼───╫───┼───╢
        // ║   │   ║   │   ║
        // ╚═══╧═══╩═══╧═══╝

        let mut constraint = ThermoConstraint::new();
        constraint.add_thermometer(
            Thermometer::new(vec![(1, 0), (1, 1), (0, 1)]).unwrap()
        ).unwrap();
        constraint.add_thermometer(
            Thermometer::new(vec![(1, 0), (1, 1), (2, 1), (2, 2)]).unwrap()
        ).unwrap();
        constraint
    }

    fn branching_constraint_solution() -> SudokuGrid {
        SudokuGrid::parse("2x2;
            3,1,2,4,\
            4,2,3,1,\
            1,3,4,2,\
            2,4,1,3").unwrap()
    }

    fn assert_set_eq<T: Debug + Eq + Hash>(set: &HashSet<T>, values: Vec<&T>) {
        assert_eq!(values.len(), set.len());

        for value in values {
            assert!(set.contains(value));
        }
    }

    fn assert_cell_assignment(constraint: &ThermoConstraint, column: usize,
            row: usize, indices: Vec<usize>) {
        assert_set_eq(constraint.cell_assignment.get(&(column, row)).unwrap(),
            indices.iter().collect());
    }

    fn reduced_constraint(reduction: (usize, usize))
            -> (ThermoConstraint, ThermoRevertInfo, SudokuGrid) {
        let mut constraint = branching_constraint();
        let solution = branching_constraint_solution();
        let revert_info = constraint.reduce(&solution, &reduction).unwrap();
        (constraint, revert_info, solution)
    }

    fn reverted_constraint(reduction: (usize, usize)) -> ThermoConstraint {
        let (mut constraint, revert_info, solution) =
            reduced_constraint(reduction);
        constraint.revert(&solution, &reduction, revert_info);
        constraint
    }

    #[test]
    fn thermometer_removal_applied_correctly() {
        let (constraint, _, _) = reduced_constraint((0, 1));
        let remaining_thermometer_cells = vec![(1, 0), (1, 1), (2, 1), (2, 2)];

        assert_eq!(1, constraint.thermometers.len());
        assert_eq!(&remaining_thermometer_cells,
            constraint.thermometers[0].cells());
        assert_eq!(4, constraint.cell_assignment.len());

        for (column, row) in remaining_thermometer_cells {
            assert_cell_assignment(&constraint, column, row, vec![0]);
        }
    }

    #[test]
    fn thermometer_removal_reverted_correctly() {
        let constraint = reverted_constraint((0, 1));

        assert_eq!(2, constraint.thermometers.len());
        assert_eq!(&vec![(1, 0), (1, 1), (2, 1), (2, 2)],
            constraint.thermometers[0].cells());
        assert_eq!(&vec![(1, 0), (1, 1), (0, 1)],
            constraint.thermometers[1].cells());

        assert_cell_assignment(&constraint, 1, 0, vec![0, 1]);
        assert_cell_assignment(&constraint, 1, 1, vec![0, 1]);
        assert_cell_assignment(&constraint, 2, 1, vec![0]);
        assert_cell_assignment(&constraint, 2, 2, vec![0]);
        assert_cell_assignment(&constraint, 0, 1, vec![1]);
    }

    #[test]
    fn thermometer_shortening_applied_correctly() {
        let (constraint, _, _) = reduced_constraint((2, 1));

        assert_eq!(2, constraint.thermometers.len());
        assert_eq!(&vec![(1, 0), (1, 1), (0, 1)],
            constraint.thermometers[0].cells());
        assert_eq!(&vec![(1, 0), (1, 1), (2, 1)],
            constraint.thermometers[1].cells());

        assert_cell_assignment(&constraint, 1, 0, vec![0, 1]);
        assert_cell_assignment(&constraint, 1, 1, vec![0, 1]);
        assert_cell_assignment(&constraint, 0, 1, vec![0]);
        assert_cell_assignment(&constraint, 2, 1, vec![1]);
    }

    #[test]
    fn thermometer_shortening_reverted_correctly() {
        let constraint = reverted_constraint((2, 1));

        assert_eq!(2, constraint.thermometers.len());
        assert_eq!(&vec![(1, 0), (1, 1), (0, 1)],
            constraint.thermometers[0].cells());
        assert_eq!(&vec![(1, 0), (1, 1), (2, 1), (2, 2)],
            constraint.thermometers[1].cells());

        assert_cell_assignment(&constraint, 1, 0, vec![0, 1]);
        assert_cell_assignment(&constraint, 1, 1, vec![0, 1]);
        assert_cell_assignment(&constraint, 0, 1, vec![0]);
        assert_cell_assignment(&constraint, 2, 1, vec![1]);
        assert_cell_assignment(&constraint, 2, 2, vec![1]);
    }

    #[test]
    fn thermo_constraint_satisfied_empty() {
        let constraint = branching_constraint();
        let grid = SudokuGrid::new(2, 2).unwrap();

        assert!(constraint.check(&grid));
        assert!(constraint.check_cell(&grid, 1, 0));
        assert!(constraint.check_cell(&grid, 0, 1));
        assert!(constraint.check_cell(&grid, 2, 1));
    }

    #[test]
    fn thermo_constraint_satisfied_partial() {
        let constraint = branching_constraint();
        let grid = SudokuGrid::parse("2x2;
             ,1, , ,\
            4, ,3, ,\
             , , , ,\
             , , , ").unwrap();

        assert!(constraint.check(&grid));
        assert!(constraint.check_cell(&grid, 1, 0));
        assert!(constraint.check_cell(&grid, 0, 1));
        assert!(constraint.check_cell(&grid, 1, 1));
        assert!(constraint.check_cell(&grid, 2, 1));
        assert!(constraint.check_number(&grid, 1, 1, 2));
        assert!(constraint.check_number(&grid, 2, 2, 4));
    }

    #[test]
    fn thermo_constraint_satisfied_full() {
        let constraint = branching_constraint();
        let mut grid = branching_constraint_solution();

        assert!(constraint.check(&grid));
        assert!(constraint.check_cell(&grid, 1, 0));
        assert!(constraint.check_cell(&grid, 0, 1));
        assert!(constraint.check_cell(&grid, 1, 1));
        assert!(constraint.check_cell(&grid, 2, 1));

        grid.clear_cell(1, 1).unwrap();

        assert!(constraint.check_number(&grid, 1, 1, 2));
    }

    #[test]
    fn thermo_constraint_violated_partial() {
        let constraint = branching_constraint();
        let grid_1 = SudokuGrid::parse("2x2;
             ,2, , ,\
            2, ,3, ,\
             , , , ,\
             , , , ").unwrap();

        assert!(!constraint.check(&grid_1));
        assert!(!constraint.check_cell(&grid_1, 0, 1));
        assert!(constraint.check_cell(&grid_1, 2, 1));
        assert!(!constraint.check_number(&grid_1, 2, 1, 2));

        let grid_2 = SudokuGrid::parse("2x2;
             ,1, , ,\
             ,3, , ,\
             , ,2, ,\
             , , , ").unwrap();

        assert!(!constraint.check(&grid_2));
        assert!(!constraint.check_cell(&grid_2, 1, 1));
        assert!(!constraint.check_number(&grid_2, 1, 0, 3));
    }

    #[test]
    fn thermo_constraint_violated_full() {
        let constraint = branching_constraint();
        let grid = SudokuGrid::parse("2x2;
            3,1,2,4,\
            4,2,4,1,\
            1,3,3,2,\
            2,4,1,3").unwrap();

        assert!(!constraint.check(&grid));
        assert!(!constraint.check_cell(&grid, 2, 1));
        assert!(!constraint.check_cell(&grid, 2, 2));
        assert!(constraint.check_cell(&grid, 0, 1));
        assert!(!constraint.check_number(&grid, 0, 1, 1));
        assert!(!constraint.check_number(&grid, 2, 1, 3));
        assert!(!constraint.check_number(&grid, 2, 1, 2));
    }
}
