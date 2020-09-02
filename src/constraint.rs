//! This module defines constraints which can be applied tu Sudoku grids, thus
//! specifying the rules of the puzzle.
//!
//! Besides the definition of the [Constraint](trait.Constraint.html) trait,
//! this crate contains some predefined constraint for default Sudoku rules and
//! some variants. We will cover them first and afterwards show how to
//! implement a custom constraint.
//!
//! # Default Sudoku rules
//!
//! To get the default Sudoku rules,
//! [DefaultConstraint](struct.DefaultConstraint.html) can be used.
//! Conceptually, it is a conjunction of
//! [RowConstraint](struct.RowConstraint.html),
//! [ColumnConstraint](struct.ColumnConstraint.html), and
//! [BlockConstraint](struct.BlockConstraint.html).
//!
//! # Variants
//!
//! Besides the default rules, `sudoku-variants` also offers some pre-defined
//! variantions. As an example, we will use the
//! [DiagonalsConstraint](struct.DiagonalsConstraint.html), which requires that
//! the two diagonals, top-left to bottom-right and top-right to bottom-left,
//! do not contain duplicate digits, just like each row, column, and block in
//! standard Sudoku.
//!
//! Normally, one wants to apply a `DiagonalsConstraint` *and* a
//! `DefaultConstraint`. This can be done in two ways: using a
//! [CompositeConstraint](struct.CompositeConstraint.html) and using a
//! [DynamicConstraint](struct.DynamicConstraint.html). The first is
//! type-checked over two parameter types, which both need to be constraints.
//! It is provided one instance of each type, and is defined to be fulfilled
//! if both instances are fulfilled. In contrast, the `DynamicConstraint` uses
//! a vector of trait objects and is fulfilled if all entries are fulfilled.
//! This enables a more flexible design and is less cumbersome, especially when
//! combining more than two constraints, but comes at a runtime cost due to
//! dynamic dispatch.
//!
//! To define our combination of default- and diagonals-constraints, we can
//! write the following code:
//!
//! ```
//! use sudoku_variants::constraint::{
//!     CompositeConstraint,
//!     DefaultConstraint,
//!     DiagonalsConstraint,
//!     DynamicConstraint
//! };
//!
//! // Option 1: CompositeConstraint
//! let c1 = CompositeConstraint::new(DefaultConstraint, DiagonalsConstraint);
//!
//! // Option 2: DynamicConstraint
//! let c2 = DynamicConstraint::new(vec![
//!     Box::new(DefaultConstraint),
//!     Box::new(DiagonalsConstraint)
//! ]);
//! ```
//!
//! # Custom constraints
//!
//! When implementing a constraint, it is usually sufficient to implement
//! [Constraint.check_number](trait.Constraint.html#tymethod.check_number). All
//! other methods are default-implemented based on it. However, the performance
//! of [Constraint.check](trait.Constraint.html#method.check) could be improved
//! by a specialized implementation, since by default it calls `check_number`
//! for every cell.
//!
//! As an example of an implementation of a custom constraint, we will look at
//! the source code of a subset of the `DiagonalsConstraint`, which we call
//! `MainDiagonalConstraint`. It only checks the diagonal from the top-left to
//! the bottom-right corner of the Sudoku.
//!
//! ```
//! use sudoku_variants::SudokuGrid;
//! use sudoku_variants::constraint::Constraint;
//!
//! #[derive(Clone)]
//! struct MainDiagonalConstraint;
//!
//! impl Constraint for MainDiagonalConstraint {
//!     fn check_number(&self, grid: &SudokuGrid, column: usize, row: usize,
//!             number: usize) -> bool {
//!         // For all cells on the diagonal, the column index is equal to the
//!         // row index. All other cells don't interact with this constraint,
//!         // so we return true, indicating that they don't violate it.
//!         if column == row {
//!             let size = grid.size();
//!
//!             for i in 0..size {
//!                 // Since column == row, if i == column we are looking at
//!                 // the checked cell itself, which may contain the number.
//!                 if i != column &&
//!                         grid.has_number(i, i, number).unwrap() {
//!                     return false;
//!                 }
//!             }
//!         }
//!
//!         true
//!     }
//! }
//! ```
//!
//! Deriving `Clone` is important, since occasionally Sudoku need to be cloned.
//! Sudoku therefore implements `Clone`, which requires its constraint to be
//! cloneable aswell. Note that `Clone` is not required by the `Constraint`
//! trait, since that would make it impossible to create `Constraint`-trait
//! objects, which are used in the `DynamicConstraint`. Instead,
//! [CloneConstraint](trait.CloneConstraint.html), which clones a trait object,
//! is required for elements of a `DynamicConstraint`. However, if you derive
//! `Clone`, you do not need to worry about `CloneConstraint`, since it is
//! implemented on every constraint that implements `Clone` by default.

use crate::SudokuGrid;

use std::iter::Cloned;
use std::slice::Iter;

/// A constraint defines some property on a Sudoku grid. These are essentially
/// the rules of the Sudoku. In standard Sudoku these are "No duplicates in a
/// row" (`RowConstraint`), "No duplicates in a column" (`ColumnConstraint`),
/// and "No duplicates in a block" (`BlockConstraint`). Here, however, the
/// design is more flexible to allow for custom constraints.
///
/// By default, implementors of this trait only need to implement the
/// `check_number` associated function, which verifies a proposed number for a
/// specified cell. `check_cell` and `check` are implemented by default based
/// on it, however `check` in particular may be very inefficient compared to a
/// specialized implementation (it checks every cell using `check_number`).
///
/// Note regarding cloning: To enable wrapping constraints in a trait object,
/// the `Clone` trait must not be required here. However, it is necessary later
/// to create a Sudoku with this constraint. Implementing the `Clone` trait
/// also automatically gives the `CloneConstraint` trait via a blanket
/// implementation, so it is recommended to derive `Clone` and not worry about
/// `CloneConstraint`.
pub trait Constraint {

    /// Checks whether the given [SudokuGrid](../struct.SudokuGrid.html)
    /// matches this constraint, that is, every cell matches this constraint.
    /// By default, this runs `check_cell` on every cell of the grid, which may
    /// be inefficient, so custom implementations may be advantageous.
    fn check(&self, grid: &SudokuGrid) -> bool {
        let size = grid.size();

        for row in 0..size {
            for column in 0..size {
                if !self.check_cell(grid, column, row) {
                    return false;
                }
            }
        }

        true
    }

    /// Checks whether the cell at the given position in the
    /// [SudokuGrid](../struct.SudokuGrid.html) fulfills the constraint. This
    /// is the same as calling `check_number` with the same coordinates and
    /// the number which is actually filled in that cell. If the cell is empty,
    /// this function always returns `true`.
    fn check_cell(&self, grid: &SudokuGrid, column: usize, row: usize)
            -> bool {
        if let Some(number) = grid.get_cell(column, row).unwrap() {
            self.check_number(grid, column, row, number)
        }
        else {
            true
        }
    }

    /// Checks whether the given `number` would fit into the cell specified by
    /// `column` and `row` into the `grid` without violating this constraint.
    /// This function does *not* have to check whether `number` is actually a
    /// valid number for this grid (i.e. in the interval [1, size]). If you
    /// require this guarantee, use `Sudoku.is_valid_number` instead.
    ///
    /// For some constraints, it may be difficult to decide whether a number
    /// could actually fill the cell without making the puzzle impossible. It
    /// is therefore explicitly *not* required for this function to check
    /// whether the actual solution could contain that number, however it must
    /// guarantee that an error in a full grid (where all numbers are filled
    /// in) is detected. Still, it should detect errors way before that to
    /// improve the performance of solvers.
    fn check_number(&self, grid: &SudokuGrid, column: usize, row: usize,
        number: usize) -> bool;
}

/// A `Constraint` that there are no duplicates in each row.
#[derive(Clone)]
pub struct RowConstraint;

impl Constraint for RowConstraint {
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
}

/// A `Constraint` that there are no duplicates in each column.
#[derive(Clone)]
pub struct ColumnConstraint;

impl Constraint for ColumnConstraint {
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
}

fn check_number_block(grid: &SudokuGrid, column: usize, row: usize,
        number: usize, bop: impl Fn(bool, bool) -> bool) -> bool {
    let block_width = grid.block_width();
    let block_height = grid.block_height();
    let block_column = (column / block_width) * block_width;
    let block_row = (row / block_height) * block_height;

    for other_row in block_row..(block_row + block_height) {
        for other_column in block_column..(block_column + block_width) {
            if bop(other_row != row, other_column != column) {
                if grid.has_number(other_column, other_row, number).unwrap() {
                    return false;
                }
            }
        }
    }

    true
}

/// A `Constraint` that there are no duplicates in each block.
#[derive(Clone)]
pub struct BlockConstraint;

impl Constraint for BlockConstraint {
    fn check_number(&self, grid: &SudokuGrid, column: usize, row: usize,
            number: usize) -> bool {
        check_number_block(grid, column, row, number, |a, b| a || b)
    }
}

/// Similar to `BlockConstraint`, but does not check numbers in the same row
/// and column to save some time. For use in the DefaultConstraint.
#[derive(Clone)]
struct BlockConstraintNoLineColumn;

impl Constraint for BlockConstraintNoLineColumn {
    fn check_number(&self, grid: &SudokuGrid, column: usize, row: usize,
            number: usize) -> bool {
        check_number_block(grid, column, row, number, |a, b| a && b)
    }
}

/// The default Sudoku `Constraint` which is a logical conjunction of
/// `RowConstraint`, `ColumnConstraint`, and `BlockConstraint`.
#[derive(Clone)]
pub struct DefaultConstraint;

impl Constraint for DefaultConstraint {
    fn check(&self, grid: &SudokuGrid) -> bool {
        RowConstraint.check(grid) &&
            ColumnConstraint.check(grid) &&
            BlockConstraintNoLineColumn.check(grid)
    }

    fn check_cell(&self, grid: &SudokuGrid, column: usize, row: usize)
            -> bool {
        RowConstraint.check_cell(grid, column, row) &&
            ColumnConstraint.check_cell(grid, column, row) &&
            BlockConstraintNoLineColumn.check_cell(grid, column, row)
    }

    fn check_number(&self, grid: &SudokuGrid, column: usize, row: usize,
            number: usize) -> bool {
        RowConstraint.check_number(grid, column, row, number) &&
            ColumnConstraint.check_number(grid, column, row, number) &&
            BlockConstraintNoLineColumn.check_number(grid, column, row, number)
    }
}

/// A `Constraint` which checks that there are no duplicates in each of the two
/// diagonals ( ╲ and ╱ ).
#[derive(Clone)]
pub struct DiagonalsConstraint;

impl Constraint for DiagonalsConstraint {
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
        while let Some((delta_column, delta_row)) = self.coords.next() {
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
/// forbidden is defined by [is_forbidden](#method.is_forbidden), which is a
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
    /// [RELATIVE_COORDINATES](#associatedconstant.RELATIVE_COORDINATES), this
    /// method determines whether the reference cell violates the constraint.
    /// Since it is assumed that an empty cell cannot violate the constraint,
    /// this method is only called if both cells contain a number.
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
    /// coordinates from
    /// [RELATIVE_COORDINATES](#associatedconstant.RELATIVE_COORDINATES).
    fn is_forbidden(&self, reference_cell: usize, other_cell: usize) -> bool {
        reference_cell == other_cell
    }
}

impl<C: RelativeCellConstraint> Constraint for C {
    fn check_number(&self, grid: &SudokuGrid, column: usize, row: usize,
            number: usize) -> bool {
        let iter =
            RelativeCellIter::new(&C::RELATIVE_COORDINATES, grid, column, row);
        
        for other_cell in iter {
            if let Some(other_number) = other_cell {
                if self.is_forbidden(number, other_number) {
                    return false;
                }
            }
        }
        
        true
    }
}

/// A `RelativeCellConstraint` that excludes duplicates a Chess-Knight's move
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
#[derive(Clone)]
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

/// A `RelativeCellConstraint` that excludes duplicates a Chess-Kings's move
/// away from the reference cell (orthogonally or diagonally adjacent). Note
/// that some checks performed by this constraint are redundant if standard
/// Sudoku rules apply, since orthogonally adjacent cells are either in the
/// same row or column as the reference cell. In that case, using the
/// `DiagonallyAdjacentConstraint` is more efficient and has the same effect.
#[derive(Clone)]
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

/// A `RelativeCellConstraint` that excludes duplicates in a diagonally
/// adjacent cell to the reference cell. If normal Sudoku rules apply, this is
/// equivalent to a `KingsMoveConstraint`.
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
#[derive(Clone)]
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

/// A `RelativeCellConstraint` that excludes consecutive digits in orthogonally
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
#[derive(Clone)]
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

/// A `Constraint` which simultaneously enforces two other constraints. This
/// allows the construction of complex constraints by nesting composite
/// constraints.
///
/// As an example, a constraint with `DefaultConstraint`,
/// `DiagonalsConstraint`, and `KnightsMoveConstraint` would be constructed
/// as follows:
///
/// ```
/// use sudoku_variants::constraint::{
///     CompositeConstraint,
///     DefaultConstraint,
///     DiagonalsConstraint,
///     KnightsMoveConstraint
/// };
///
/// let constraint = CompositeConstraint::new(
///     DefaultConstraint,
///     CompositeConstraint::new(
///         DiagonalsConstraint,
///         KnightsMoveConstraint
///     )
/// );
/// ```
///
/// The advantage of using this over a
/// [DynamicConstraint](struct.DynamicConstraint.html) is that it is statically
/// known which types of constraints are used, so no dynamic dispatch is
/// necessary. On the contrary, a `CompositeConstraint` is less flexible.
#[derive(Clone)]
pub struct CompositeConstraint<C1, C2>
where
    C1: Constraint + Clone + 'static,
    C2: Constraint + Clone + 'static
{
    c1: C1,
    c2: C2
}

impl<C1, C2> CompositeConstraint<C1, C2>
where
    C1: Constraint + Clone + 'static,
    C2: Constraint + Clone + 'static
{
    /// Creates a new composite constraint from the two child consraints which
    /// will be enforced.
    pub fn new(c1: C1, c2: C2) -> CompositeConstraint<C1, C2> {
        CompositeConstraint {
            c1,
            c2
        }
    }
}

impl<C1, C2> Constraint for CompositeConstraint<C1, C2>
where
    C1: Constraint + Clone + 'static,
    C2: Constraint + Clone + 'static
{
    fn check(&self, grid: &SudokuGrid) -> bool {
        self.c1.check(grid) && self.c2.check(grid)
    }

    fn check_cell(&self, grid: &SudokuGrid, column: usize, row: usize)
            -> bool {
        self.c1.check_cell(grid, column, row) &&
            self.c2.check_cell(grid, column, row)
    }

    fn check_number(&self, grid: &SudokuGrid, column: usize, row: usize,
            number: usize) -> bool {
        self.c1.check_number(grid, column, row, number) &&
            self.c2.check_number(grid, column, row, number)
    }
}

/// A trait for cloneable `Constraints` which is used in the
/// `DynamicConstraint` to clone trait objects. Normally a user should not have
/// to implement this trait manually, as it is automatically implemented for
/// all `Constraint`s that implement `Clone` (and have static lifetime).
pub trait CloneConstraint : Constraint {

    /// Clones a trait object of this constraint.
    fn clone_box(&self) -> Box<dyn CloneConstraint>;
}

impl<C: Constraint + Clone + 'static> CloneConstraint for C {
    fn clone_box(&self) -> Box<dyn CloneConstraint> {
        Box::new(self.clone())
    }
}

/// A `Constraint` that contains a vector of trait objects representing
/// constraints and verifies all of them. This is more flexible than a
/// `CompositeConstraint`, but also less efficient, since it needs dynamic
/// dispatch.
pub struct DynamicConstraint {
    constraints: Vec<Box<dyn CloneConstraint>>
}

impl DynamicConstraint {

    /// Creates a new dynamic constraint from the given child constraints. The
    /// created constraint is defined to be satisfied if all children are
    /// satisfied.
    pub fn new(constraints: Vec<Box<dyn CloneConstraint>>) -> DynamicConstraint {
        DynamicConstraint {
            constraints
        }
    }
}

impl Constraint for DynamicConstraint {
    fn check(&self, grid: &SudokuGrid) -> bool {
        self.constraints.iter().all(|c| c.check(grid))
    }

    fn check_cell(&self, grid: &SudokuGrid, column: usize, row: usize) -> bool {
        self.constraints.iter().all(|c| c.check_cell(grid, column, row))
    }

    fn check_number(&self, grid: &SudokuGrid, column: usize, row: usize,
            number: usize) -> bool {
        self.constraints.iter().all(
            |c| c.check_number(grid, column, row, number))
    }
}

impl Clone for DynamicConstraint {
    fn clone(&self) -> Self {
        let constraints = self.constraints.iter()
            .map(|c| c.clone_box())
            .collect();
        DynamicConstraint {
            constraints
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::Sudoku;

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

    fn test_column_row_satisfied(constraint: impl Constraint + Clone) {
        let code = "2x2;\
            2,4, ,1,\
            1,3,2, ,\
             ,1, ,3,\
            4, ,3, ";
        let sudoku = Sudoku::parse(code, constraint).unwrap();
        assert!(sudoku.is_valid());
        assert!(sudoku.is_valid_cell(1, 1).unwrap());
        assert!(sudoku.is_valid_number(2, 2, 4).unwrap());
    }

    fn test_column_row_violated(constraint: impl Constraint + Clone) {
        let code1 = "2x2;\
            2,4, ,4,\
            1,3,2, ,\
             ,1, ,3,\
            4, ,3, ";
        let sudoku = Sudoku::parse(code1, constraint).unwrap();
        assert!(!sudoku.is_valid());
        assert!(!sudoku.is_valid_cell(1, 0).unwrap());
        assert!(!sudoku.is_valid_cell(3, 0).unwrap());
        assert!(sudoku.is_valid_cell(1, 1).unwrap());
        assert!(!sudoku.is_valid_number(2, 2, 1).unwrap());
        assert!(sudoku.is_valid_number(2, 0, 1).unwrap());
    }

    #[test]
    fn composite_satisfied() {
        test_column_row_satisfied(CompositeConstraint::new(
            RowConstraint, ColumnConstraint));
    }

    #[test]
    fn composite_violated() {
        test_column_row_violated(CompositeConstraint::new(
            RowConstraint, ColumnConstraint));
    }

    #[test]
    fn dynamic_satisfied() {
        test_column_row_satisfied(DynamicConstraint::new(vec![
            Box::new(RowConstraint),
            Box::new(ColumnConstraint)
        ]));
    }

    #[test]
    fn dynamic_violated() {
        test_column_row_violated(DynamicConstraint::new(vec![
            Box::new(RowConstraint),
            Box::new(ColumnConstraint)
        ]));
    }
}
