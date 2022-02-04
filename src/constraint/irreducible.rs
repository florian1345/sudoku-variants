//! This module contains the definition of all irreducible constraints. All of
//! them are re-exported in the [constraint](crate::constraint) module, so you
//! should not have to `use` anything from this module directly.

use crate::SudokuGrid;
use crate::constraint::{self, Constraint, Group, ReductionError};
use crate::util::USizeSet;

use serde::{Deserialize, Serialize};

use std::any::Any;
use std::iter::Cloned;
use std::slice::Iter;

/// A trait for all constraints which are not reducible. That is, there is no
/// way to make this constraint less expressive while remaining correct.
/// Examples for such constraints are stateless constraints such as the classic
/// Sudoku constraint, which checks digit uniqueness in each row, column, and
/// block and therefore cannot be changed in any way, but also stateful
/// constraints whose state is unique for any given solution, such as an XV
/// constraint, which only has one valid configuration of X's and V's for any
/// filled grid. One counterexample is the Killer Sudoku constraint, where
/// neighboring cages can be merged, as long as they do not contain any
/// repeating digits, thus making the constraint less expressive.
pub trait IrreducibleConstraint {

    /// See [Constraint::check].
    #[inline]
    fn check(&self, grid: &SudokuGrid) -> bool {
        constraint::default_check(self, grid)
    }

    /// See [Constraint::check_cell].
    #[inline]
    fn check_cell(&self, grid: &SudokuGrid, column: usize, row: usize)
            -> bool {
        constraint::default_check_cell(self, grid, column, row)
    }

    /// See [Constraint::check_number].
    fn check_number(&self, grid: &SudokuGrid, column: usize, row: usize,
        number: usize) -> bool;

    /// See [Constraint::get_groups].
    fn get_groups(&self, grid: &SudokuGrid) -> Vec<Group>;

    /// See [Constraint::to_objects].
    fn to_objects(&self) -> Vec<&dyn Any>
    where
        Self : Sized + 'static
    {
        vec![self]
    }
}

impl<C: IrreducibleConstraint + ?Sized> Constraint for C {
    type Reduction = ();
    type RevertInfo = ();

    #[inline]
    fn check(&self, grid: &SudokuGrid) -> bool {
        <C as IrreducibleConstraint>::check(self, grid)
    }

    #[inline]
    fn check_cell(&self, grid: &SudokuGrid, column: usize, row: usize)
            -> bool {
        <C as IrreducibleConstraint>::check_cell(self, grid, column, row)
    }

    #[inline]
    fn check_number(&self, grid: &SudokuGrid, column: usize, row: usize,
            number: usize) -> bool {
        <C as IrreducibleConstraint>::check_number(self, grid, column, row,
            number)
    }

    #[inline]
    fn get_groups(&self, grid: &SudokuGrid) -> Vec<Group> {
        <C as IrreducibleConstraint>::get_groups(self, grid)
    }

    fn list_reductions(&self, _: &SudokuGrid) -> Vec<Self::Reduction> {
        Vec::new()
    }

    fn reduce(&mut self, _: &SudokuGrid, _: &())
            -> Result<(), ReductionError> {
        Err(ReductionError::InvalidReduction)
    }

    fn revert(&mut self, _: &SudokuGrid, _: &(), _: ()) { }

    #[inline]
    fn to_objects(&self) -> Vec<&dyn Any>
    where
        Self: Sized + 'static
    {
        <C as IrreducibleConstraint>::to_objects(self)
    }
}

/// A [Constraint] that there are no duplicates in each row.
#[derive(Clone, Deserialize, Serialize)]
pub struct RowConstraint;

impl IrreducibleConstraint for RowConstraint {
    fn check(&self, grid: &SudokuGrid) -> bool {
        let size = grid.size();
        let mut set = USizeSet::new(1, size).unwrap();

        for row in 0..size {
            set.clear();

            for column in 0..size {
                if let Some(number) = grid.get_cell(column, row).unwrap() {
                    if !set.insert(number).unwrap() {
                        return false;
                    }
                }
            }
        }

        true
    }

    fn check_number(&self, grid: &SudokuGrid, column: usize, row: usize,
            number: usize) -> bool {
        let size = grid.size();

        for other_column in 0..size {
            if other_column != column &&
                    grid.has_number(other_column, row, number).unwrap()  {
                return false;
            }
        }

        true
    }

    fn get_groups(&self, grid: &SudokuGrid) -> Vec<Group> {
        let size = grid.size();
        let mut groups = Vec::new();

        for row in 0..size {
            let mut group = Group::new();

            for column in 0..size {
                group.push((column, row));
            }

            groups.push(group);
        }

        groups
    }
}

/// A [Constraint] that there are no duplicates in each column.
#[derive(Clone, Deserialize, Serialize)]
pub struct ColumnConstraint;

impl IrreducibleConstraint for ColumnConstraint {

    // TODO investigate whether code duplication between this and RowConstraint
    // can be avoided.

    fn check(&self, grid: &SudokuGrid) -> bool {
        let size = grid.size();
        let mut set = USizeSet::new(1, size).unwrap();

        for column in 0..size {
            set.clear();

            for row in 0..size {
                if let Some(number) = grid.get_cell(column, row).unwrap() {
                    if !set.insert(number).unwrap() {
                        return false;
                    }
                }
            }
        }

        true
    }

    fn check_number(&self, grid: &SudokuGrid, column: usize, row: usize,
            number: usize) -> bool {
        let size = grid.size();

        for other_row in 0..size {
            if other_row != row &&
                    grid.has_number(column, other_row, number).unwrap() {
                return false;
            }
        }

        true
    }

    fn get_groups(&self, grid: &SudokuGrid) -> Vec<Group> {
        let size = grid.size();
        let mut groups = Vec::new();

        for column in 0..size {
            let mut group = Group::new();

            for row in 0..size {
                group.push((column, row));
            }

            groups.push(group);
        }

        groups
    }
}

fn check_number_block(grid: &SudokuGrid, column: usize, row: usize,
        number: usize, bop: impl Fn(bool, bool) -> bool) -> bool {
    let block_width = grid.block_width();
    let block_height = grid.block_height();
    let block_column = (column / block_width) * block_width;
    let block_row = (row / block_height) * block_height;

    for other_row in block_row..(block_row + block_height) {
        for other_column in block_column..(block_column + block_width) {
            if bop(other_row != row, other_column != column) &&
                    grid.has_number(other_column, other_row, number).unwrap() {
                return false;
            }
        }
    }

    true
}

fn get_groups_block(grid: &SudokuGrid) -> Vec<Group> {
    let block_width = grid.block_width();
    let block_height = grid.block_height();
    let mut groups = Vec::new();

    for block_row in 0..block_width {
        let base_row = block_row * block_height;

        for block_column in 0..block_height {
            let base_column = block_column * block_width;
            let mut group = Group::new();

            for sub_row in 0..block_height {
                let row = base_row + sub_row;

                for sub_column in 0..block_width {
                    let column = base_column + sub_column;
                    group.push((column, row));
                }
            }

            groups.push(group);
        }
    }

    groups
}

/// A [Constraint] that there are no duplicates in each block.
#[derive(Clone, Deserialize, Serialize)]
pub struct BlockConstraint;

impl IrreducibleConstraint for BlockConstraint {
    
    // TODO investigate whether code duplication between this and RowConstraint
    // and ColumnConstraint can be avoided.

    fn check(&self, grid: &SudokuGrid) -> bool {
        let block_width = grid.block_width();
        let block_height = grid.block_height();
        let size = grid.size();
        let mut set = USizeSet::new(1, size).unwrap();

        for block_row in 0..block_width {
            for block_column in 0..block_height {
                set.clear();

                let start_column = block_column * block_width;
                let start_row = block_row * block_height;

                for row in start_row..(start_row + block_height) {
                    for column in start_column..(start_column + block_width) {
                        if let Some(number) =
                                grid.get_cell(column, row).unwrap() {
                            if !set.insert(number).unwrap() {
                                return false;
                            }
                        }
                    }
                }
            }
        }

        true
    }

    fn check_number(&self, grid: &SudokuGrid, column: usize, row: usize,
            number: usize) -> bool {
        check_number_block(grid, column, row, number, |a, b| a || b)
    }

    fn get_groups(&self, grid: &SudokuGrid) -> Vec<Group> {
        get_groups_block(grid)
    }
}

/// Similar to [BlockConstraint], but does not check numbers in the same row
/// and column to save some time. For use in the [DefaultConstraint].
#[derive(Clone, Deserialize, Serialize)]
struct BlockConstraintNoLineColumn;

impl IrreducibleConstraint for BlockConstraintNoLineColumn {
    fn check(&self, grid: &SudokuGrid) -> bool {
        <BlockConstraint as Constraint>::check(&BlockConstraint, grid)
    }

    fn check_number(&self, grid: &SudokuGrid, column: usize, row: usize,
            number: usize) -> bool {
        check_number_block(grid, column, row, number, |a, b| a && b)
    }

    fn get_groups(&self, grid: &SudokuGrid) -> Vec<Group> {
        get_groups_block(grid)
    }
}

/// The default Sudoku [Constraint] which is a logical conjunction of
/// [RowConstraint], [ColumnConstraint], and [BlockConstraint].
#[derive(Clone, Deserialize, Serialize)]
pub struct DefaultConstraint;

impl IrreducibleConstraint for DefaultConstraint {
    fn check(&self, grid: &SudokuGrid) -> bool {
        <RowConstraint as Constraint>::check(&RowConstraint, grid) &&
        <ColumnConstraint as Constraint>::check(&ColumnConstraint, grid) &&
        <BlockConstraintNoLineColumn as Constraint>::check(
            &BlockConstraintNoLineColumn, grid)
    }

    fn check_cell(&self, grid: &SudokuGrid, column: usize, row: usize)
            -> bool {
        <RowConstraint as Constraint>::check_cell(&RowConstraint, grid, column,
            row) &&
        <ColumnConstraint as Constraint>::check_cell(&ColumnConstraint, grid,
            column, row) &&
        <BlockConstraintNoLineColumn as Constraint>::check_cell(
            &BlockConstraintNoLineColumn, grid, column, row)
    }

    fn check_number(&self, grid: &SudokuGrid, column: usize, row: usize,
            number: usize) -> bool {
        <RowConstraint as Constraint>::check_number(&RowConstraint, grid,
            column, row, number) &&
        <ColumnConstraint as Constraint>::check_number(&ColumnConstraint, grid,
            column, row, number) &&
        <BlockConstraintNoLineColumn as Constraint>::check_number(
            &BlockConstraintNoLineColumn, grid, column, row, number)
    }

    fn get_groups(&self, grid: &SudokuGrid) -> Vec<Group> {
        let mut groups =
            <RowConstraint as Constraint>::get_groups(&RowConstraint, grid);
        groups.append(&mut <ColumnConstraint as Constraint>::get_groups(
            &ColumnConstraint, grid));
        groups.append(
            &mut <BlockConstraintNoLineColumn as Constraint>::get_groups(
                &BlockConstraintNoLineColumn, grid));
        groups
    }

    fn to_objects(&self) -> Vec<&dyn Any>
    where
        Self : Sized + 'static
    {
        vec![&RowConstraint, &ColumnConstraint, &BlockConstraint]
    }
}

/// A [Constraint] which checks that there are no duplicates in each of the two
/// diagonals ( ╲ and ╱ ).
#[derive(Clone, Deserialize, Serialize)]
pub struct DiagonalsConstraint;

impl IrreducibleConstraint for DiagonalsConstraint {
    fn check_number(&self, grid: &SudokuGrid, column: usize, row: usize,
            number: usize) -> bool {
        let size = grid.size();

        if column == row {
            // main diagonal

            for i in 0..size {
                if i != column &&
                        grid.has_number(i, i, number).unwrap() {
                    return false;
                }
            }
        }

        if column + row == size - 1 {
            // anti diagonal

            for i in 0..size {
                if i != column &&
                        grid.has_number(i, size - i - 1, number).unwrap() {
                    return false;
                }
            }
        }

        true
    }

    fn get_groups(&self, grid: &SudokuGrid) -> Vec<Group> {
        let size = grid.size();
        let mut main_diagonal = Group::new();
        let mut anti_diagonal = Group::new();

        for i in 0..size {
            main_diagonal.push((i, i));
            anti_diagonal.push((i, size - i - 1));
        }

        vec![
            main_diagonal,
            anti_diagonal
        ]
    }
}

struct RelativeCellIter<'a, I>
where
    I : Iterator<Item = (isize, isize)>
{
    coords: I,
    grid: &'a SudokuGrid,
    center_column: usize,
    center_row: usize
}

impl<'a, I> Iterator for RelativeCellIter<'a, I>
where
    I : Iterator<Item = (isize, isize)>
{
    type Item = Option<usize>;

    fn next(&mut self) -> Option<Self::Item> {
        for (delta_column, delta_row) in self.coords.by_ref() {
            let column = self.center_column as isize + delta_column;
            let row = self.center_row as isize + delta_row;
            let size = self.grid.size() as isize;

            if column >= 0 && column < size && row >= 0 && row < size {
                return Some(
                    self.grid.get_cell(column as usize, row as usize)
                        .unwrap());
            }
        }

        None
    }
}

type ISizePairIterator<'a> = Cloned<Iter<'a, (isize, isize)>>;

impl<'a> RelativeCellIter<'a, ISizePairIterator<'a>> {
    fn new(coords: &'a [(isize, isize)], grid: &'a SudokuGrid,
            column: usize, row: usize)
            -> RelativeCellIter<'a, ISizePairIterator<'a>> {
        RelativeCellIter {
            coords: coords.iter().cloned(),
            grid,
            center_column: column,
            center_row: row
        }
    }
}

/// A trait for `Constraint`s that are defined by having no forbidden numbers
/// in some relative configuration to the reference cell. Whether a number is
/// forbidden is defined by [RelativeCellConstraint::is_forbidden], which is a
/// boolean relation between the reference cell and the other cell. By default,
/// this checks for equality.
///
/// As an example, the constraint that no diagonally adjacent cells have the
/// same number may be formulated as a `RelativeCellConstraint` with the
/// relative coordinates `[(-1, -1), (-1, +1), (+1, -1), (+1, +1)]`, with the
/// default equality being used for `is_forbidden`.
pub trait RelativeCellConstraint {

    /// A slice of coordinates relative to the cell in question that must not
    /// contain the same number.
    const RELATIVE_COORDINATES: &'static [(isize, isize)];

    /// Given the contents of the reference cell and one other cell that is
    /// removed by one set of coordinates specified in
    /// [RelativeCellConstraint::RELATIVE_COORDINATES], this method determines
    /// whether the reference cell violates the constraint. Since it is assumed
    /// that an empty cell cannot violate the constraint, this method is only
    /// called if both cells contain a number.
    ///
    /// As an example, for ordinary constraints such as the no-knight's-move-
    /// constraint, this is usually an equality check. A cell removed by a
    /// knight's move may not be equal to the reference cell. This is actually
    /// the default behavior for this method.
    ///
    /// However, in some situations this may be different. As an example, for
    /// the no-adjacent-consecutive-constraint, this is a predicate that
    /// determines whether the two numbers are consecutive.
    ///
    /// # Arguments
    ///
    /// * `reference_cell`: The cell which is currently tested, i.e. relative
    /// to which the coordinates are defined.
    /// * `other_cell`: A cell removed from the `reference_cell` by a set of
    /// coordinates from [RelativeCellConstraint::RELATIVE_COORDINATES].
    fn is_forbidden(&self, reference_cell: usize, other_cell: usize) -> bool {
        reference_cell == other_cell
    }
}

impl<C: RelativeCellConstraint> IrreducibleConstraint for C {

    #[inline]
    fn check_number(&self, grid: &SudokuGrid, column: usize, row: usize,
            number: usize) -> bool {
        let iter =
            RelativeCellIter::new(C::RELATIVE_COORDINATES, grid, column, row);
        
        for other_cell in iter.flatten() {
            if self.is_forbidden(number, other_cell) {
                return false;
            }
        }
        
        true
    }

    fn get_groups(&self, _: &SudokuGrid) -> Vec<Group> {
        Vec::new()
    }
}

/// A [RelativeCellConstraint] that excludes duplicates a Chess-Knight's move
/// away from the reference cell.
///
/// As a visualization, the cells marked with 'X' in the following grid are
/// excluded from being a 3:
///
/// ```text
/// ┌───┬───┬───┬───┬───┐
/// │   │ X │   │ X │   │
/// ├───┼───┼───┼───┼───┤
/// │ X │   │   │   │ X │
/// ├───┼───┼───┼───┼───┤
/// │   │   │ 3 │   │   │
/// ├───┼───┼───┼───┼───┤
/// │ X │   │   │   │ X │
/// ├───┼───┼───┼───┼───┤
/// │   │ X │   │ X │   │
/// └───┴───┴───┴───┴───┘
/// ```
#[derive(Clone, Deserialize, Serialize)]
pub struct KnightsMoveConstraint;

const KNIGHTS_MOVES: [(isize, isize); 8] = [
    (-1, -2),
    (1, -2),
    (-2, -1),
    (2, -1),
    (-2, 1),
    (2, 1),
    (-1, 2),
    (1, 2)
];

impl RelativeCellConstraint for KnightsMoveConstraint {
    const RELATIVE_COORDINATES: &'static [(isize, isize)] = &KNIGHTS_MOVES;
}

/// A [RelativeCellConstraint] that excludes duplicates a Chess-Kings's move
/// away from the reference cell (orthogonally or diagonally adjacent). Note
/// that some checks performed by this constraint are redundant if standard
/// Sudoku rules apply, since orthogonally adjacent cells are either in the
/// same row or column as the reference cell. In that case, using the
/// [DiagonallyAdjacentConstraint] is more efficient and has the same effect.
#[derive(Clone, Deserialize, Serialize)]
pub struct KingsMoveConstraint;

const KINGS_MOVES: [(isize, isize); 8] = [
    (-1, -1),
    (0, -1),
    (1, -1),
    (-1, 0),
    (1, 0),
    (-1, 1),
    (0, 1),
    (1, 1)
];

impl RelativeCellConstraint for KingsMoveConstraint {
    const RELATIVE_COORDINATES: &'static [(isize, isize)] = &KINGS_MOVES;
}

/// A [RelativeCellConstraint] that excludes duplicates in a diagonally
/// adjacent cell to the reference cell. If normal Sudoku rules apply, this is
/// equivalent to a [KingsMoveConstraint].
///
/// As a visualization, the cells marked with 'X' in the following grid are
/// excluded from being a 3:
///
/// ```text
/// ┌───┬───┬───┐
/// │ X │   │ X │
/// ├───┼───┼───┤
/// │   │ 3 │   │
/// ├───┼───┼───┤
/// │ X │   │ X │
/// └───┴───┴───┘
/// ```
#[derive(Clone, Deserialize, Serialize)]
pub struct DiagonallyAdjacentConstraint;

const DIAGONALLY_ADJACENT: [(isize, isize); 4] = [
    (-1, -1),
    (1, -1),
    (-1, 1),
    (1, 1)
];

impl RelativeCellConstraint for DiagonallyAdjacentConstraint {
    const RELATIVE_COORDINATES: &'static [(isize, isize)] =
        &DIAGONALLY_ADJACENT;
}

/// A [RelativeCellConstraint] that excludes consecutive digits in orthogonally
/// adjacent cells. As a visualization, the cells marked with 'X' in the
/// following grid are excluded from being a 2 or a 4:
///
/// ```text
/// ┌───┬───┬───┐
/// │   │ X │   │
/// ├───┼───┼───┤
/// │ X │ 3 │ X │
/// ├───┼───┼───┤
/// │   │ X │   │
/// └───┴───┴───┘
/// ```
#[derive(Clone, Deserialize, Serialize)]
pub struct AdjacentConsecutiveConstraint;

const ORTHOGONALLY_ADJACENT: [(isize, isize); 4] = [
    (-1, 0),
    (1, 0),
    (0, -1),
    (0, 1)
];

impl RelativeCellConstraint for AdjacentConsecutiveConstraint {
    const RELATIVE_COORDINATES: &'static [(isize, isize)] =
        &ORTHOGONALLY_ADJACENT;

    fn is_forbidden(&self, reference_cell: usize, other_cell: usize) -> bool {
        reference_cell + 1 == other_cell || reference_cell == other_cell + 1
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::{Sudoku, constraint::Subconstraint};

    #[test]
    fn row_satisfied() {
        let code = "2x2;\
            1, , ,2,\
             ,2, ,3,\
             ,4,1, ,\
            3, , ,2";
        let sudoku = Sudoku::parse(code, RowConstraint).unwrap();
        assert!(sudoku.is_valid());
        assert!(sudoku.is_valid_cell(3, 2).unwrap());
        assert!(sudoku.is_valid_cell(3, 3).unwrap());
        assert!(sudoku.is_valid_number(2, 2, 3).unwrap());
    }

    #[test]
    fn row_violated() {
        let code = "2x2;\
            1, , ,2,\
             ,2, ,3,\
             , ,1, ,\
            4, , ,4";
        let sudoku = Sudoku::parse(code, RowConstraint).unwrap();
        assert!(!sudoku.is_valid());
        assert!(!sudoku.is_valid_cell(0, 3).unwrap());
        assert!(!sudoku.is_valid_cell(3, 3).unwrap());
        assert!(sudoku.is_valid_cell(2, 2).unwrap());
        assert!(!sudoku.is_valid_number(2, 0, 1).unwrap());
        assert!(!sudoku.is_valid_number(2, 1, 3).unwrap());
        assert!(sudoku.is_valid_number(3, 3, 1).unwrap());
    }

    #[test]
    fn column_satisfied() {
        let code = "2x2;\
            1, ,3, ,\
             ,2, ,2,\
            3, , ,1,\
             ,4, , ";
        let sudoku = Sudoku::parse(code, ColumnConstraint).unwrap();
        assert!(sudoku.is_valid());
        assert!(sudoku.is_valid_cell(1, 1).unwrap());
        assert!(sudoku.is_valid_cell(1, 2).unwrap());
        assert!(sudoku.is_valid_number(3, 0, 3).unwrap());
    }

    #[test]
    fn column_violated() {
        let code = "2x2;\
            1, ,3, ,\
             ,2, ,4,\
            1, , ,3,\
             ,4, , ";
        let sudoku = Sudoku::parse(code, ColumnConstraint).unwrap();
        assert!(!sudoku.is_valid());
        assert!(!sudoku.is_valid_cell(0, 0).unwrap());
        assert!(!sudoku.is_valid_cell(0, 2).unwrap());
        assert!(sudoku.is_valid_cell(1, 1).unwrap());
        assert!(!sudoku.is_valid_number(2, 1, 3).unwrap());
        assert!(!sudoku.is_valid_number(1, 0, 4).unwrap());
        assert!(sudoku.is_valid_number(3, 3, 1).unwrap());
    }

    #[test]
    fn block_satisfied() {
        let code = "2x2;\
            1,2, , ,\
             ,3, ,3,\
             ,2,4, ,\
            3, , ,1";
        let sudoku = Sudoku::parse(code, BlockConstraint).unwrap();
        assert!(sudoku.is_valid());
        assert!(sudoku.is_valid_cell(1, 1).unwrap());
        assert!(sudoku.is_valid_cell(3, 2).unwrap());
        assert!(sudoku.is_valid_number(3, 2, 2).unwrap());
    }

    #[test]
    fn block_violated() {
        let code = "2x2;\
            1, , ,3,\
             ,3, , ,\
             ,2,4, ,\
            2, , ,1";
        let sudoku = Sudoku::parse(code, BlockConstraint).unwrap();
        assert!(!sudoku.is_valid());
        assert!(!sudoku.is_valid_cell(0, 3).unwrap());
        assert!(!sudoku.is_valid_cell(1, 2).unwrap());
        assert!(sudoku.is_valid_cell(1, 1).unwrap());
        assert!(!sudoku.is_valid_number(2, 0, 3).unwrap());
        assert!(!sudoku.is_valid_number(3, 3, 4).unwrap());
        assert!(sudoku.is_valid_number(2, 1, 4).unwrap());
    }

    #[test]
    fn diagonals_satisfied() {
        let code = "2x2;\
            2,3,4,1,\
             , , , ,\
             , ,4, ,\
            3, , ,3";
        let sudoku = Sudoku::parse(code, DiagonalsConstraint).unwrap();
        assert!(sudoku.is_valid());
        assert!(sudoku.is_valid_cell(2, 2).unwrap());
        assert!(sudoku.is_valid_cell(3, 0).unwrap());
        assert!(sudoku.is_valid_cell(2, 0).unwrap());
        assert!(sudoku.is_valid_number(1, 1, 1).unwrap());
    }

    #[test]
    fn diagonals_violated() {
        let code = "2x2;\
            2,3,4,1,\
             , , , ,\
             , ,2, ,\
            3, , ,4";
        let sudoku = Sudoku::parse(code, DiagonalsConstraint).unwrap();
        assert!(!sudoku.is_valid());
        assert!(!sudoku.is_valid_cell(0, 0).unwrap());
        assert!(!sudoku.is_valid_cell(2, 2).unwrap());
        assert!(sudoku.is_valid_cell(0, 3).unwrap());
        assert!(sudoku.is_valid_cell(2, 0).unwrap());
        assert!(!sudoku.is_valid_number(1, 2, 1).unwrap());
        assert!(!sudoku.is_valid_number(1, 1, 4).unwrap());
        assert!(sudoku.is_valid_number(2, 2, 3).unwrap());
        assert!(sudoku.is_valid_number(1, 1, 3).unwrap());
    }

    #[test]
    fn knights_move_satisfied() {
        let code = "2x2;\
            1, ,3, ,\
             ,2, ,3,\
             ,4, ,1,\
            1,4,1,2";
        let sudoku = Sudoku::parse(code, KnightsMoveConstraint).unwrap();
        assert!(sudoku.is_valid());
        assert!(sudoku.is_valid_cell(3, 2).unwrap());
        assert!(sudoku.is_valid_cell(0, 2).unwrap());
        assert!(sudoku.is_valid_number(2, 1, 3).unwrap());
    }

    #[test]
    fn knights_move_violated() {
        let code = "2x2;\
            1, ,3, ,\
             ,2, ,4,\
             ,4, ,1,\
            3, ,2, ";
        let sudoku = Sudoku::parse(code, KnightsMoveConstraint).unwrap();
        assert!(!sudoku.is_valid());
        assert!(!sudoku.is_valid_cell(1, 1).unwrap());
        assert!(!sudoku.is_valid_cell(2, 3).unwrap());
        assert!(!sudoku.is_valid_cell(3, 1).unwrap());
        assert!(!sudoku.is_valid_cell(1, 2).unwrap());
        assert!(sudoku.is_valid_cell(2, 0).unwrap());
        assert!(sudoku.is_valid_cell(2, 1).unwrap());
        assert!(!sudoku.is_valid_number(2, 2, 3).unwrap());
        assert!(sudoku.is_valid_number(1, 1, 4).unwrap());
    }

    #[test]
    fn kings_move_satisfied() {
        let code = "2x2;\
            2,3, , ,\
             ,4,2,1,\
             ,1, ,4,\
             ,2, ,2";
        let sudoku = Sudoku::parse(code, KingsMoveConstraint).unwrap();
        assert!(sudoku.is_valid());
        assert!(sudoku.is_valid_cell(1, 1).unwrap());
        assert!(sudoku.is_valid_cell(1, 3).unwrap());
        assert!(sudoku.is_valid_number(2, 2, 3).unwrap());
    }

    #[test]
    fn kings_move_violated() {
        let code = "2x2;\
            1,3, , ,\
             ,2,2,1,\
             ,1, ,4,\
             , ,1,3";
        let sudoku = Sudoku::parse(code, KingsMoveConstraint).unwrap();
        assert!(!sudoku.is_valid());
        assert!(!sudoku.is_valid_cell(1, 1).unwrap());
        assert!(!sudoku.is_valid_cell(2, 1).unwrap());
        assert!(!sudoku.is_valid_cell(1, 2).unwrap());
        assert!(!sudoku.is_valid_cell(2, 3).unwrap());
        assert!(sudoku.is_valid_cell(3, 2).unwrap());
        assert!(sudoku.is_valid_cell(2, 2).unwrap());
        assert!(!sudoku.is_valid_number(2, 2, 3).unwrap());
        assert!(!sudoku.is_valid_number(2, 2, 4).unwrap());
        assert!(sudoku.is_valid_number(2, 0, 4).unwrap());
    }

    #[test]
    fn diagonally_adjacent_satisfied() {
        let code = "2x2;\
            1,3, , ,\
             ,3,2, ,\
            2,1,1, ,\
            4, , , ";
        let sudoku =
            Sudoku::parse(code, DiagonallyAdjacentConstraint).unwrap();
        assert!(sudoku.is_valid());
        assert!(sudoku.is_valid_cell(1, 1).unwrap());
        assert!(sudoku.is_valid_cell(2, 2).unwrap());
        assert!(sudoku.is_valid_number(1, 2, 3).unwrap());
    }

    #[test]
    fn diagonally_adjacent_violated() {
        let code = "2x2;\
            1,2, , ,\
             ,3,2, ,\
             ,2, ,4,\
            4, ,1, ";
        let sudoku =
            Sudoku::parse(code, DiagonallyAdjacentConstraint).unwrap();
        assert!(!sudoku.is_valid());
        assert!(!sudoku.is_valid_cell(1, 0).unwrap());
        assert!(!sudoku.is_valid_cell(2, 1).unwrap());
        assert!(sudoku.is_valid_cell(1, 1).unwrap());
        assert!(!sudoku.is_valid_number(2, 1, 4).unwrap());
        assert!(!sudoku.is_valid_number(3, 0, 2).unwrap());
        assert!(sudoku.is_valid_number(1, 2, 3).unwrap());
    }

    #[test]
    fn adjacent_consecutive_satisfied() {
        let code = "2x2;\
            4,2,4,1,\
             ,4, ,3,\
             ,1,3, ,\
            2, ,1, ";
        let sudoku =
            Sudoku::parse(code, AdjacentConsecutiveConstraint).unwrap();
        assert!(sudoku.is_valid());
        assert!(sudoku.is_valid_cell(1, 1).unwrap());
        assert!(sudoku.is_valid_cell(2, 2).unwrap());
        assert!(sudoku.is_valid_number(2, 1, 1).unwrap());
    }

    #[test]
    fn adjacent_consecutive_violated() {
        let code = "2x2;\
            4,2, ,1,\
             ,3, ,4,\
             ,1,3,2,\
            2, , , ";
        let sudoku =
            Sudoku::parse(code, AdjacentConsecutiveConstraint).unwrap();
        assert!(!sudoku.is_valid());
        assert!(!sudoku.is_valid_cell(1, 0).unwrap());
        assert!(!sudoku.is_valid_cell(1, 1).unwrap());
        assert!(!sudoku.is_valid_cell(2, 2).unwrap());
        assert!(!sudoku.is_valid_cell(3, 2).unwrap());
        assert!(sudoku.is_valid_cell(1, 2).unwrap());
        assert!(!sudoku.is_valid_number(2, 1, 2).unwrap());
        assert!(sudoku.is_valid_number(1, 0, 1).unwrap());
    }

    #[test]
    fn default_subconstraints() {
        assert!(DefaultConstraint.has_subconstraint::<RowConstraint>());
        assert!(DefaultConstraint.has_subconstraint::<ColumnConstraint>());
        assert!(DefaultConstraint.has_subconstraint::<BlockConstraint>());
        assert!(!DefaultConstraint.has_subconstraint::<DiagonalsConstraint>());
    }
}
