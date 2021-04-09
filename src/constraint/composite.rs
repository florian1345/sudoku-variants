//! This module contains the definition of all composite constraints, i.e. the
//! statically linked [CompositeConstraint] and the dynamically linked
//! [DynamicConstraint], including all necessary utility. All definitions of
//! this module are re-exported in the [constraint](crate::constraint) module,
//! so you should not have to `use` anything from this module directly.

use crate::SudokuGrid;
use crate::constraint::{Constraint, Group, ReductionError};

use serde::{Deserialize, Serialize};

use std::any::Any;

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
#[derive(Clone, Deserialize, Serialize)]
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

    /// Gets the first constraint that is part of this composite constraint.
    pub fn first(&self) -> &C1 {
        &self.c1
    }

    /// Gets a mutable reference to the first constraint that is part of this
    /// composite constraint.
    pub fn first_mut(&mut self) -> &mut C1 {
        &mut self.c1
    }

    /// Gets the second constraint that is part of this composite constraint.
    pub fn second(&self) -> &C2 {
        &self.c2
    }

    /// Gets a mutable reference to the second constraint that is part of this
    /// composite constraint.
    pub fn second_mut(&mut self) -> &mut C2 {
        &mut self.c2
    }
}

/// Data of one of two types `D1` and `D2`.
pub enum CompositeData<D1, D2> {

    /// Data of the first type.
    First(D1),

    /// Data of the second type.
    Second(D2)
}

impl<C1, C2> Constraint for CompositeConstraint<C1, C2>
where
    C1: Constraint + Clone + 'static,
    C2: Constraint + Clone + 'static
{
    type Reduction = CompositeData<C1::Reduction, C2::Reduction>;
    type RevertInfo = CompositeData<C1::RevertInfo, C2::RevertInfo>;

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

    fn list_reductions(&self, solution: &SudokuGrid) -> Vec<Self::Reduction> {
        let mut r1: Vec<Self::Reduction> = self.c1.list_reductions(solution)
            .into_iter()
            .map(CompositeData::First)
            .collect();
        let mut r2: Vec<Self::Reduction> = self.c2.list_reductions(solution)
            .into_iter()
            .map(CompositeData::Second)
            .collect();
        r1.append(&mut r2);
        r1
    }

    fn reduce(&mut self, solution: &SudokuGrid, reduction: &Self::Reduction)
            -> Result<Self::RevertInfo, ReductionError> {
        match reduction {
            CompositeData::First(reduction) =>
                Ok(CompositeData::First(self.c1.reduce(solution, reduction)?)),
            CompositeData::Second(reduction) =>
                Ok(CompositeData::Second(self.c2.reduce(solution, reduction)?))
        }
    }

    fn revert(&mut self, solution: &SudokuGrid, reduction: &Self::Reduction,
            revert_info: Self::RevertInfo) {
        match reduction {
            CompositeData::First(reduction) => {
                if let CompositeData::First(revert_info) = revert_info {
                    self.c1.revert(solution, reduction, revert_info)
                }
                else {
                    panic!("Incompatible reduction and reverse info provided.")
                }
            },
            CompositeData::Second(reduction) => {
                if let CompositeData::Second(revert_info) = revert_info {
                    self.c2.revert(solution, reduction, revert_info)
                }
                else {
                    panic!("Incompatible reduction and reverse info provided.")
                }
            }
        }
    }

    fn to_objects(&self) -> Vec<&dyn Any>
    where
        Self : Sized + 'static
    {
        let mut result = self.c1.to_objects();
        result.append(&mut self.c2.to_objects());
        result
    }
}

/// A trait for cloneable [Constraint]s which is used in the
/// [DynamicConstraint] to clone trait objects. Normally a user should not have
/// to implement this trait manually, as it is automatically implemented for
/// all `Constraint`s that implement [Clone] (and have static lifetime).
trait CloneConstraint :
        Constraint<Reduction = Box<dyn Any>, RevertInfo = Box<dyn Any>> {

    /// Clones a trait object of this constraint.
    fn clone_box(&self) -> Box<dyn CloneConstraint>;

    fn to_objects_wrapped(&self) -> Vec<&dyn Any>;
}

#[derive(Clone)]
struct WrappedConstraint<C: Constraint + Clone> {
    constraint: C
}

impl<C: Constraint + Clone + 'static> From<C> for WrappedConstraint<C> {
    fn from(c: C) -> WrappedConstraint<C> {
        WrappedConstraint {
            constraint: c
        }
    }
}

impl<C: Constraint + Clone + 'static> Constraint for WrappedConstraint<C> {
    type Reduction = Box<dyn Any>;
    type RevertInfo = Box<dyn Any>;

    fn check(&self, grid: &SudokuGrid) -> bool {
        self.constraint.check(grid)
    }

    fn check_cell(&self, grid: &SudokuGrid, column: usize, row: usize)
            -> bool {
        self.constraint.check_cell(grid, column, row)
    }

    fn check_number(&self, grid: &SudokuGrid, column: usize, row: usize,
            number: usize) -> bool {
        self.constraint.check_number(grid, column, row, number)
    }

    fn get_groups(&self, grid: &SudokuGrid) -> Vec<Group> {
        self.constraint.get_groups(grid)
    }

    fn list_reductions(&self, solution: &SudokuGrid) -> Vec<Box<dyn Any>> {
        self.constraint.list_reductions(solution).into_iter()
            .map(|r| {
                let r_any: Box<dyn Any> = Box::new(r);
                r_any
            })
            .collect()
    }

    fn reduce(&mut self, solution: &SudokuGrid, reduction: &Box<dyn Any>)
            -> Result<Box<dyn Any>, ReductionError> {
        let reduction: &C::Reduction = reduction.downcast_ref()
            .expect("Reduction has wrong type.");
        let reverse_info = self.constraint.reduce(solution, reduction)?;
        Ok(Box::new(reverse_info))
    }

    fn revert(&mut self, solution: &SudokuGrid, reduction: &Self::Reduction,
            revert_info: Self::RevertInfo) {
        let reduction: &C::Reduction = reduction.downcast_ref()
            .expect("Reduction has wrong type.");
        let revert_info: C::RevertInfo = *revert_info.downcast()
            .expect("Revert info has wrong type.");
        self.constraint.revert(solution, reduction, revert_info);
    }

    fn to_objects(&self) -> Vec<&dyn Any>
    where
        Self : Sized + 'static
    {
        self.constraint.to_objects()
    }
}

impl<C> CloneConstraint for WrappedConstraint<C>
where
    C: Constraint + Clone + 'static
{
    fn clone_box(&self) -> Box<dyn CloneConstraint> {
        Box::new(self.clone())
    }

    fn to_objects_wrapped(&self) -> Vec<&dyn Any> {
        self.constraint.to_objects()
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

    /// Creates a new dynamic constraint without any child constraint. Children
    /// can be added later using [DynamicConstraint::add].
    pub fn new() -> DynamicConstraint {
        DynamicConstraint {
            constraints: Vec::new()
        }
    }

    /// Adds a [Constraint] to this dynamic constraint as a child. It is
    /// wrapped in a trait object.
    pub fn add(&mut self, constraint: impl Constraint + Clone + 'static) {
        self.constraints.push(Box::new(WrappedConstraint::from(constraint)))
    }
}

impl Constraint for DynamicConstraint {

    type Reduction = (usize, Box<dyn Any>);
    type RevertInfo = Box<dyn Any>;

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

    fn list_reductions(&self, solution: &SudokuGrid) -> Vec<(usize, Box<dyn Any>)> {
        self.constraints.iter()
            .enumerate()
            .flat_map(|(i, c)| c.list_reductions(solution).into_iter()
                .map(move |r| (i, r)))
            .collect()
    }

    fn reduce(&mut self, solution: &SudokuGrid,
            (index, data): &(usize, Box<dyn Any>))
            -> Result<Box<dyn Any>, ReductionError> {
        let constraint = self.constraints.get_mut(*index)
            .expect("Reduction had invalid index.");
        constraint.reduce(solution, data)
    }

    fn revert(&mut self, solution: &SudokuGrid,
            (index, data): &(usize, Box<dyn Any>),
            revert_info: Box<dyn Any>) {
        let constraint = self.constraints.get_mut(*index)
            .expect("Reduction had invalid index.");
        constraint.revert(solution, data, revert_info);
    }

    fn to_objects(&self) -> Vec<&dyn Any>
    where
        Self : Sized + 'static
    {
        let mut result = Vec::new();

        for constraint in self.constraints.iter() {
            result.append(&mut constraint.to_objects_wrapped());
        }

        result
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
        let mut c = DynamicConstraint::new();
        c.add(RowConstraint);
        c.add(ColumnConstraint);
        test_column_row_satisfied(c);
    }

    #[test]
    fn dynamic_violated() {
        let mut c = DynamicConstraint::new();
        c.add(RowConstraint);
        c.add(ColumnConstraint);
        test_column_row_violated(c);
    }
}
