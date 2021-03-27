//! This module defines constraints which can be applied tu Sudoku grids, thus
//! specifying the rules of the puzzle.
//!
//! Besides the definition of the [Constraint] trait, this crate contains some
//! predefined constraint for default Sudoku rules and some variants. We will
//! cover them first and afterwards show how to implement a custom constraint.
//!
//! # Default Sudoku rules
//!
//! To get the default Sudoku rules, [DefaultConstraint] can be used.
//! Conceptually, it is a conjunction of [RowConstraint], [ColumnConstraint],
//! and [BlockConstraint].
//!
//! # Variants
//!
//! Besides the default rules, `sudoku-variants` also offers some pre-defined
//! variantions. As an example, we will use the [DiagonalsConstraint], which
//! requires that the two diagonals, top-left to bottom-right and top-right to
//! bottom-left, do not contain duplicate digits, just like each row, column,
//! and block in standard Sudoku.
//!
//! Normally, one wants to apply a `DiagonalsConstraint` *and* a
//! `DefaultConstraint`. This can be done in two ways: using a
//! [CompositeConstraint] and using a [DynamicConstraint]. The first is
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
//! let c2 = DynamicConstraint::with_children(vec![
//!     Box::new(DefaultConstraint),
//!     Box::new(DiagonalsConstraint)
//! ]);
//! ```
//!
//! # Custom constraints
//!
//! When implementing a constraint, it is usually sufficient to implement
//! [Constraint::check_number] and [Constraint::get_groups]. All other methods
//! are default-implemented. However, the performance of [Constraint::check]
//! could be improved by a specialized implementation, since by default it
//! calls `check_number` for every cell.
//!
//! As an example of an implementation of a custom constraint, we will look at
//! the source code of a subset of the `DiagonalsConstraint`, which we call
//! `MainDiagonalConstraint`. It only checks the diagonal from the top-left to
//! the bottom-right corner of the Sudoku.
//!
//! ```
//! use sudoku_variants::SudokuGrid;
//! use sudoku_variants::constraint::{Constraint, Group};
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
//!
//!     fn get_groups(&self, grid: &SudokuGrid) -> Vec<Group> {
//!         // There is one group in this case: the main diagonal.
//!         let size = grid.size();
//!         let mut group = Group::new();
//!
//!         for i in 0..size {
//!             group.push((i, i));
//!         }
//!
//!         vec![ group ]
//!     }
//! }
//! ```
//!
//! Deriving `Clone` is important, since occasionally Sudoku need to be cloned.
//! Sudoku therefore implements `Clone`, which requires its constraint to be
//! cloneable aswell. Note that `Clone` is not required by the `Constraint`
//! trait, since that would make it impossible to create `Constraint`-trait
//! objects, which are used in the `DynamicConstraint`. Instead,
//! [CloneConstraint], which clones a trait object, is required for elements of
//! a `DynamicConstraint`. However, if you derive `Clone`, you do not need to
//! worry about `CloneConstraint`, since it is implemented for every constraint
//! that implements `Clone` by default.

use crate::SudokuGrid;

pub mod composite;
pub mod irreducible;

pub use composite::*;
pub use irreducible::*;

/// A group of cells, represented by a vector of their coordinates in the form
/// `(column, row)`.
pub type Group = Vec<(usize, usize)>;

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

    /// Checks whether the given [SudokuGrid] matches this constraint, that is,
    /// every cell matches this constraint.  By default, this runs `check_cell`
    /// on every cell of the grid, which may be inefficient, so custom
    /// implementations may be advantageous.
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

    /// Checks whether the cell at the given position in the [SudokuGrid]
    /// fulfills the constraint. This is the same as calling `check_number`
    /// with the same coordinates and the number which is actually filled in
    /// that cell. If the cell is empty, this function always returns `true`.
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
    /// require this guarantee, use
    /// [Sudoku::is_valid_number](crate::Sudoku::is_valid_number) instead.
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

    /// Gets a vector of all groups that are defined by this constraint. A
    /// group is a set of cells which may not contain repeated numbers. As an
    /// example, the [BlockConstraint] defines each block as a group. Some
    /// constraints, such as the [KingsMoveConstraint], do not have groups. In
    /// this particular case, a cell removed by a kings-move to the top-left
    /// may be the same as one to the bottom-right, so the cells removed by a
    /// kings-move from any particular cell cannot form a group. Such
    /// constraints should return an empty vector here.
    ///
    /// Arguing about groups is necessary for some strategies. While it is
    /// possible to solve Sudoku with constraints which do not implement this
    /// method, getting this implementation will enable some strategies as well
    /// as improve the performance of strategic backtracking.
    fn get_groups(&self, grid: &SudokuGrid) -> Vec<Group>;
}
