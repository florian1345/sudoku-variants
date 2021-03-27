//! This module contains the definition of all composite constraints, i.e. the
//! statically linked [CompositeConstraint] and the dynamically linked
//! [DynamicConstraint], including all necessary utility. All definitions of
//! this module are re-exported in the [constraint](crate::constraint) module,
//! so you should not have to `use` anything from this module directly.

use crate::SudokuGrid;
use crate::constraint::{Constraint, Group};

/// A [Constraint] which simultaneously enforces two other constraints. This
/// allows the construction of complex constraints by nesting composite
/// constraints.
///
/// As an example, a constraint with [DefaultConstraint],
/// [DiagonalsConstraint], and [KnightsMoveConstraint] would be constructed
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
/// The advantage of using this over a [DynamicConstraint] is that it is
/// statically known which types of constraints are used, so no dynamic
/// dispatch is necessary. On the contrary, a `CompositeConstraint` is less
/// flexible.
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

    fn get_groups(&self, grid: &SudokuGrid) -> Vec<Group> {
        let mut groups = self.c1.get_groups(grid);
        groups.append(&mut self.c2.get_groups(grid));
        groups
    }
}

/// A trait for cloneable [Constraint]s which is used in the
/// [DynamicConstraint] to clone trait objects. Normally a user should not have
/// to implement this trait manually, as it is automatically implemented for
/// all `Constraint`s that implement [Clone] (and have static lifetime).
pub trait CloneConstraint : Constraint {

    /// Clones a trait object of this constraint.
    fn clone_box(&self) -> Box<dyn CloneConstraint>;
}

impl<C: Constraint + Clone + 'static> CloneConstraint for C {
    fn clone_box(&self) -> Box<dyn CloneConstraint> {
        Box::new(self.clone())
    }
}

/// A [Constraint] that contains a vector of trait objects representing
/// constraints and verifies all of them. This is more flexible than a
/// [CompositeConstraint], but also less efficient, since it needs dynamic
/// dispatch.
pub struct DynamicConstraint {
    constraints: Vec<Box<dyn CloneConstraint>>
}

impl DynamicConstraint {

    /// Creates a new dynamic constraint from the given child constraints. The
    /// created constraint is defined to be satisfied if all children are
    /// satisfied.
    pub fn with_children(constraints: Vec<Box<dyn CloneConstraint>>)
            -> DynamicConstraint {
        DynamicConstraint {
            constraints
        }
    }

    /// Creates a new dynamic constraint without any child constraint. Children
    /// can be added later using [DynamicConstraint::add].
    pub fn new() -> DynamicConstraint {
        DynamicConstraint {
            constraints: Vec::new()
        }
    }

    /// Adds a [CloneConstraint] to this dynamic constraint as a child. It is
    /// wrapped in a trait object.
    pub fn add(&mut self, constraint: impl CloneConstraint + 'static) {
        self.constraints.push(Box::new(constraint))
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

    fn get_groups(&self, grid: &SudokuGrid) -> Vec<Group> {
        self.constraints.iter()
            .map(|c| c.get_groups(grid))
            .flat_map(|g| g.into_iter())
            .collect()
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

impl Default for DynamicConstraint {
    fn default() -> DynamicConstraint {
        DynamicConstraint::new()
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::Sudoku;
    use crate::constraint::{ColumnConstraint, RowConstraint};

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
        test_column_row_satisfied(DynamicConstraint::with_children(vec![
            Box::new(RowConstraint),
            Box::new(ColumnConstraint)
        ]));
    }

    #[test]
    fn dynamic_violated() {
        test_column_row_violated(DynamicConstraint::with_children(vec![
            Box::new(RowConstraint),
            Box::new(ColumnConstraint)
        ]));
    }
}
