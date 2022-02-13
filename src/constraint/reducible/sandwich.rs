//! This module contains the implementation of the [SandwichConstraint] and all
//! related structures. The constraint itself is re-exported in the
//! [constraint](crate::constraint) module so you do not have to use it
//! directly.

use crate::SudokuGrid;
use crate::constraint::{Constraint, Group, ReductionError};

use serde::{Deserialize, Serialize};

fn iter_column(grid: &SudokuGrid, column: usize)
        -> impl Iterator<Item = Option<usize>> + '_ {
    (0..grid.size())
        .map(move |row| grid.get_cell(column, row).unwrap())
}

fn iter_row(grid: &SudokuGrid, row: usize)
        -> impl Iterator<Item = Option<usize>> + '_ {
    (0..grid.size())
        .map(move |column| grid.get_cell(column, row).unwrap())
}

/// Describes the states a sandwich line (column or row) can be in.
enum SandwichState {

    /// Indicates that there is no full sandwich yet, but there is still
    /// sufficient space for one. This means the constraint is satisfied for
    /// this line.
    Incomplete,

    /// Indicates that there is at most one bun and not enough space for two
    /// buns in the line. This means the constraint is violated.
    MissingBun,

    /// Indicates that there is a complete sandwich in the line. Depending on
    /// the sum, number of missing digits, and required sum, this may or may
    /// not cause the constraint to be violated.
    Complete {

        /// The sum of all digits that are present in the sandwich.
        sum: usize,

        /// The number of missing digits in the sandwich.
        missing: usize
    },

    /// Indicates that there are too many buns in the line. This means the
    /// constraint is violated.
    ExtraBun
}

impl SandwichState {
    fn unwrap(self) -> (usize, usize) {
        match self {
            SandwichState::Complete { sum, missing } => (sum, missing),
            _ => panic!("Expected complete sandwich state, but was not.")
        }
    }
}

fn sandwich_with(cells: impl Iterator<Item = Option<usize>>,
        replace: impl Fn(usize) -> Option<usize>, size: usize)
        -> SandwichState {
    let mut collecting = false;
    let mut sum = 0;
    let mut missing = 0;
    let mut total_missing = 0;
    let mut result = SandwichState::Incomplete;

    for (index, cell) in cells.enumerate() {
        let cell = replace(index).or(cell);

        if cell == Some(1) || cell == Some(size) {
            if matches!(result, SandwichState::Complete { .. }) {
                return SandwichState::ExtraBun;
            }
            else if collecting {
                result = SandwichState::Complete {
                    sum,
                    missing
                };
            }
            else {
                collecting = true;
            }
        }
        else if collecting {
            if let Some(number) = cell {
                sum += number;
            }
            else {
                missing += 1;
                total_missing += 1;
            }
        }
        else if cell.is_none() {
            total_missing += 1;
        }
    }

    if matches!(result, SandwichState::Incomplete) {
        let max_buns = total_missing + (collecting as usize);

        if max_buns < 2 {
            return SandwichState::MissingBun;
        }
    }

    result
}

fn column_sandwich_with(grid: &SudokuGrid, column: usize,
        replace: impl Fn(usize) -> Option<usize>) -> SandwichState {
    sandwich_with(iter_column(grid, column), replace, grid.size())
}

fn row_sandwich_with(grid: &SudokuGrid, row: usize,
        replace: impl Fn(usize) -> Option<usize>) -> SandwichState {
    sandwich_with(iter_row(grid, row), replace, grid.size())
}

fn sandwich(cells: impl Iterator<Item = Option<usize>>, size: usize)
        -> SandwichState {
    sandwich_with(cells, |_| None, size)
}

fn column_sandwich(grid: &SudokuGrid, column: usize) -> SandwichState {
    sandwich(iter_column(grid, column), grid.size())
}

fn row_sandwich(grid: &SudokuGrid, row: usize) -> SandwichState {
    sandwich(iter_row(grid, row), grid.size())
}

/// An enumeration of the errors which may occur when working with
/// [SandwichConstraint]s.
#[derive(Debug, Eq, PartialEq)]
pub enum SandwichError {

    /// Indicates that a sum was attempted to be inserted which was invalid for
    /// the constraint's size.
    InvalidSum,

    /// Indicates that a sum was inserted or queried from a column or row
    /// outside of the constraint's size.
    OutOfBounds
}

/// Syntactic sugar for `Result<T, SandwichError>`.
pub type SandwichResult<T> = Result<T, SandwichError>;

/// A [Constraint] that annotates numbers on some (or all) columns and rows of
/// the grid. These numbers define the sum of digits located between the two
/// cells that are filled with 1 or the highest digit that can fit on the grid
/// grid (9 in ordinary Sudoku). If there are more or less than two cells
/// filled with these "bun" digits, this constraint will be counted as
/// violated.
///
/// As an example, in the following example the second column could be
/// annotated with `16` and the third row could have a `7`. If the constraint
/// specified different sums, it would be violated.
///
/// ```text
/// ╔═══╤═══╤═══╦═══╤═══╤═══╦═══╤═══╤═══╗
/// ║   │ 3 │   ║   │   │   ║   │   │   ║
/// ╟───┼───┼───╫───┼───┼───╫───┼───┼───╢
/// ║   │ 2 │   ║   │   │   ║   │   │   ║
/// ╟───┼───┼───╫───┼───┼───╫───┼───┼───╢
/// ║ 4 │ 9 │ 5 ║ 2 │ 1 │ 8 ║ 3 │ 7 │ 6 ║
/// ╠═══╪═══╪═══╬═══╪═══╪═══╬═══╪═══╪═══╣
/// ║   │ 5 │   ║   │   │   ║   │   │   ║
/// ╟───┼───┼───╫───┼───┼───╫───┼───┼───╢
/// ║   │ 7 │   ║   │   │   ║   │   │   ║
/// ╟───┼───┼───╫───┼───┼───╫───┼───┼───╢
/// ║   │ 4 │   ║   │   │   ║   │   │   ║
/// ╠═══╪═══╪═══╬═══╪═══╪═══╬═══╪═══╪═══╣
/// ║   │ 1 │   ║   │   │   ║   │   │   ║
/// ╟───┼───┼───╫───┼───┼───╫───┼───┼───╢
/// ║   │ 6 │   ║   │   │   ║   │   │   ║
/// ╟───┼───┼───╫───┼───┼───╫───┼───┼───╢
/// ║   │ 8 │   ║   │   │   ║   │   │   ║
/// ╚═══╧═══╧═══╩═══╧═══╧═══╩═══╧═══╧═══╝
/// ```
#[derive(Clone, Deserialize, Serialize)]
pub struct SandwichConstraint {
    columns: Vec<Option<usize>>,
    rows: Vec<Option<usize>>
}

fn check_sum(sandwich_computer: impl Fn() -> SandwichState,
        annotation: Option<usize>, size: usize) -> bool {
    if let Some(required_sum) = annotation {
        match sandwich_computer() {
            SandwichState::Incomplete => true,
            SandwichState::MissingBun => false,
            SandwichState::Complete { sum, missing } => {
                let min_sum = sum + missing * 2;
                let max_sum = sum + missing * (size - 1);
                min_sum <= required_sum && max_sum >= required_sum
            },
            SandwichState::ExtraBun => false
        }
    }
    else {
        true
    }
}

impl SandwichConstraint {

    /// Creates a new sandwich constraint with no annotated sums. `size`
    /// specifies the number of rows and columns the grids input to this
    /// constraint will have.
    pub fn new(size: usize) -> SandwichConstraint {
        SandwichConstraint {
            columns: vec![None; size],
            rows: vec![None; size]
        }
    }

    /// Creates a new sandwich constraint where all rows and columns have sums
    /// fitting the given `grid`.
    pub fn new_full(grid: &SudokuGrid) -> SandwichConstraint {
        let size = grid.size();
        let columns = (0..size)
            .map(|column| Some(column_sandwich(grid, column).unwrap().0))
            .collect();
        let rows = (0..size)
            .map(|row| Some(row_sandwich(grid, row).unwrap().0))
            .collect();

        SandwichConstraint {
            columns,
            rows
        }
    }

    /// Gets the size of [SudokuGrid]s this constraint can check.
    pub fn size(&self) -> usize {
        self.columns.len()
    }

    /// Gets the maximum sum that a sandwich with the expected size (specified
    /// by [SandwichConstraint::size()]) can have. This constraint cannot
    /// assume that digits may not repeat in columns and rows, so this is the
    /// second-highest digit times the size of the largest sandwich. In an
    /// ordinary 9x9 Sudoku, this is 56 (8 * 7).
    pub fn max_sum(&self) -> usize {
        let size = self.size();
        (size - 1) * (size - 2)
    }

    fn verify(&self, coordinate: usize, sum: usize) -> SandwichResult<()> {
        let max_sum = self.max_sum();

        if coordinate >= self.size() {
            Err(SandwichError::OutOfBounds)
        }
        else if sum == 1 || sum > max_sum {
            Err(SandwichError::InvalidSum)
        }
        else {
            Ok(())
        }
    }

    /// Gets the annotated sandwich `sum` of the specified `column`, or `None`
    /// if no such sum has yet been specified.
    ///
    /// # Errors
    ///
    /// * [SandwichError::OutOfBounds] if the given `column` is outside a grid
    /// with the size expected by this constraint (specified by
    /// [SandwichConstraint::size()]).
    pub fn get_column_sandwich(&self, column: usize)
            -> SandwichResult<Option<usize>> {
        self.columns.get(column)
            .cloned()
            .ok_or(SandwichError::OutOfBounds)
    }

    /// Sets the annotated sandwich `sum` of the specified `column`.
    ///
    /// # Errors
    ///
    /// * [SandwichError::OutOfBounds] if the given `column` is outside a grid
    /// with the size expected by this constraint (specified by
    /// [SandwichConstraint::size()]).
    /// * [SandwichError::InvalidSum] if the given `sum` cannot exist in a grid
    /// with the size expected by this constraint. This is the case if it is 1
    /// (since 1 is a delimiter, it cannot be sandwiched), or greater than the
    /// maximum sum (specified by [SandwichConstraint::max_sum()]).
    pub fn set_column_sandwich(&mut self, column: usize, sum: usize)
            -> SandwichResult<()> {
        self.verify(column, sum)?;
        self.columns[column] = Some(sum);
        Ok(())
    }

    /// Sets the annotated sandwich `sum` of the specified `row`.
    ///
    /// # Errors
    ///
    /// * [SandwichError::OutOfBounds] if the given `row` is outside a grid
    /// with the size expected by this constraint (specified by
    /// [SandwichConstraint::size()]).
    /// * [SandwichError::InvalidSum] if the given `sum` cannot exist in a grid
    /// with the size expected by this constraint. This is the case if it is 1
    /// (since 1 is a delimiter, it cannot be sandwiched), or greater than the
    /// maximum sum (specified by [SandwichConstraint::max_sum()]).
    pub fn set_row_sandwich(&mut self, row: usize, sum: usize)
            -> SandwichResult<()> {
        self.verify(row, sum)?;
        self.rows[row] = Some(sum);
        Ok(())
    }

    /// Gets the annotated sandwich `sum` of the specified `row`, or `None` if
    /// no such sum has yet been specified.
    ///
    /// # Errors
    ///
    /// * [SandwichError::OutOfBounds] if the given `row` is outside a grid
    /// with the size expected by this constraint (specified by
    /// [SandwichConstraint::size()]).
    pub fn get_row_sandwich(&self, row: usize)
            -> SandwichResult<Option<usize>> {
        self.rows.get(row)
            .cloned()
            .ok_or(SandwichError::OutOfBounds)
    }

    /// Gets a list of the column sandwich sums for all columns in increasing
    /// order of column index. If there is no sum annotated at some column, it
    /// is denoted by a `None` entry.
    pub fn column_sandwiches(&self) -> &Vec<Option<usize>> {
        &self.columns
    }

    /// Gets a list of the row sandwich sums for all rows in increasing order
    /// of row index. If there is no sum annotated at some row, it is denoted
    /// by a `None` entry.
    pub fn row_sandwiches(&self) -> &Vec<Option<usize>> {
        &self.rows
    }

    fn check_column(&self, column: usize, grid: &SudokuGrid) -> bool {
        check_sum(|| column_sandwich(grid, column), self.columns[column],
            grid.size())
    }

    fn check_row(&self, row: usize, grid: &SudokuGrid) -> bool {
        check_sum(|| row_sandwich(grid, row), self.rows[row], grid.size())
    }
}

/// An enumeration of the different reductions that can be applied to a
/// [SandwichConstraint].
///
/// This is mostly an implementation detail that is public due to the public
/// implementation of [Constraint](crate::constraint::Constraint).
#[derive(Clone, Eq, PartialEq)]
pub enum SandwichReduction {

    /// Remove the annotated sum from the column with the given index.
    Column(usize),

    /// Remove the annotated sum from the row with the given index.
    Row(usize)
}

fn push_reductions(vec: &mut Vec<SandwichReduction>, entries: &[Option<usize>],
        constructor: impl Fn(usize) -> SandwichReduction) {
    for (index, entry) in entries.iter().enumerate() {
        if entry.is_some() {
            vec.push(constructor(index));
        }
    }
}

impl Constraint for SandwichConstraint {

    type Reduction = SandwichReduction;
    type RevertInfo = usize;

    fn check(&self, grid: &SudokuGrid) -> bool {
        let size = grid.size();

        for column in 0..size {
            if !self.check_column(column, grid) {
                return false;
            }
        }

        for row in 0..size {
            if !self.check_row(row, grid) {
                return false;
            }
        }

        true
    }

    fn check_cell(&self, grid: &SudokuGrid, column: usize, row: usize)
            -> bool {
        self.check_column(column, grid) && self.check_row(row, grid)
    }

    fn check_number(&self, grid: &SudokuGrid, column: usize, row: usize,
            number: usize) -> bool {
        let size = grid.size();
        let column_satisfied = check_sum(||
            column_sandwich_with(
                grid,
                column,
                |r| if r == row { Some(number) } else { None }),
            self.columns[column],
            size);

        if !column_satisfied {
            return false;
        }

        check_sum(||
            row_sandwich_with(
                grid,
                row,
                |c| if c == column { Some(number) } else { None }), 
            self.rows[row],
            size)
    }

    fn get_groups(&self, _: &SudokuGrid) -> Vec<Group> {
        Vec::new()
    }

    fn list_reductions(&self, _: &SudokuGrid) -> Vec<SandwichReduction> {
        let mut result = Vec::new();
        push_reductions(&mut result, &self.columns, SandwichReduction::Column);
        push_reductions(&mut result, &self.rows, SandwichReduction::Row);
        result
    }

    fn reduce(&mut self, _: &SudokuGrid, reduction: &SandwichReduction)
            -> Result<usize, ReductionError> {
        let entry = match *reduction {
            SandwichReduction::Column(i) => &mut self.columns[i],
            SandwichReduction::Row(i) => &mut self.rows[i]
        };

        if let Some(sum) = entry.take() {
            Ok(sum)
        }
        else {
            Err(ReductionError::InvalidReduction)
        }
    }

    fn revert(&mut self, _: &SudokuGrid, reduction: &SandwichReduction,
            revert_info: usize) {
        match *reduction {
            SandwichReduction::Column(i) =>
                self.columns[i] = Some(revert_info),
            SandwichReduction::Row(i) =>
                self.rows[i] = Some(revert_info),
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn valid_sandwiches() {
        let mut c = SandwichConstraint::new(9);
        c.set_column_sandwich(0, 56).unwrap();
        c.set_column_sandwich(8, 0).unwrap();
        c.set_row_sandwich(8, 15).unwrap();

        assert_eq!(Some(56), c.get_column_sandwich(0).unwrap());
        assert_eq!(Some(0), c.get_column_sandwich(8).unwrap());
        assert_eq!(Some(15), c.get_row_sandwich(8).unwrap());
    }

    #[test]
    fn invalid_sandwiches_out_of_bounds() {
        let mut c = SandwichConstraint::new(9);

        assert_eq!(Err(SandwichError::OutOfBounds),
            c.set_column_sandwich(9, 5));
        assert_eq!(Err(SandwichError::OutOfBounds),
            c.set_row_sandwich(10, 30));
    }

    #[test]
    fn invalid_sandwich_sums() {
        let mut c = SandwichConstraint::new(9);

        assert_eq!(Err(SandwichError::InvalidSum),
            c.set_column_sandwich(4, 1));
        assert_eq!(Err(SandwichError::InvalidSum), c.set_row_sandwich(5, 57));
    }

    fn small_example_grid() -> SudokuGrid {
        SudokuGrid::parse("3x2;
            2,3,1,4,6,5,\
            4,6,5,2,3,1,\
            3,4,2,5,1,6,\
            1,5,6,3,2,4,\
            5,1,3,6,4,2,\
            6,2,4,1,5,3").unwrap()
    }

    fn small_example_full_constraint() -> (SandwichConstraint, SudokuGrid) {
        let grid = small_example_grid();
        (SandwichConstraint::new_full(&grid), grid)
    }

    #[test]
    fn full_generation() {
        let (c, _) = small_example_full_constraint();

        assert_eq!(&vec![Some(5), Some(9), Some(7), Some(0), Some(3), Some(0)],
            c.column_sandwiches());
        assert_eq!(
            &vec![Some(4), Some(10), Some(0), Some(5), Some(3), Some(6)],
            c.row_sandwiches());
    }

    #[test]
    fn reduction_list() {
        let mut c = SandwichConstraint::new(6);
        c.set_column_sandwich(2, 7).unwrap();
        c.set_column_sandwich(3, 0).unwrap();
        c.set_row_sandwich(4, 5).unwrap();
        let reductions = c.list_reductions(&small_example_grid());

        assert_eq!(3, reductions.len());
        assert!(reductions.contains(&SandwichReduction::Column(2)));
        assert!(reductions.contains(&SandwichReduction::Column(3)));
        assert!(reductions.contains(&SandwichReduction::Row(4)));
    }

    #[test]
    fn reduces_column_correctly() {
        let (mut c, grid) = small_example_full_constraint();
        let reduction = SandwichReduction::Column(1);

        assert!(c.reduce(&grid, &reduction).is_ok());
        assert_eq!(&vec![Some(5), None, Some(7), Some(0), Some(3), Some(0)],
            c.column_sandwiches());
    }

    #[test]
    fn reduces_row_correctly() {
        let (mut c, grid) = small_example_full_constraint();
        let reduction = SandwichReduction::Row(5);

        assert!(c.reduce(&grid, &reduction).is_ok());
        assert_eq!(&vec![Some(4), Some(10), Some(0), Some(5), Some(3), None],
            c.row_sandwiches());
    }

    fn test_reversion(reduction: SandwichReduction) {
        let (original, grid) = small_example_full_constraint();
        let mut modified = original.clone();
        let revert_info = modified.reduce(&grid, &reduction).unwrap();
        modified.revert(&grid, &reduction, revert_info);

        assert_eq!(original.column_sandwiches(), modified.column_sandwiches());
        assert_eq!(original.row_sandwiches(), modified.row_sandwiches());
    }

    #[test]
    fn reverts_column_correctly() {
        test_reversion(SandwichReduction::Column(3));
    }

    #[test]
    fn reverts_row_correctly() {
        test_reversion(SandwichReduction::Row(1));
    }

    fn example_constraint() -> SandwichConstraint {
        let mut c = SandwichConstraint::new(4);
        c.set_column_sandwich(1, 5).unwrap();
        c.set_column_sandwich(3, 2).unwrap();
        c.set_row_sandwich(0, 3).unwrap();
        c.set_row_sandwich(2, 0).unwrap();
        c
    }

    #[test]
    fn sandwich_satisfied_empty() {
        let constraint = example_constraint();
        let grid = SudokuGrid::new(2, 2).unwrap();

        assert!(constraint.check(&grid));
        assert!(constraint.check_cell(&grid, 0, 1));
        assert!(constraint.check_cell(&grid, 0, 2));
        assert!(constraint.check_cell(&grid, 1, 3));
        assert!(constraint.check_cell(&grid, 3, 0));
    }

    #[test]
    fn sandwich_satisfied_full() {
        let constraint = example_constraint();
        let grid = SudokuGrid::parse("2x2;
            2,1,3,4,\
            4,3,1,2,\
            3,2,4,1,\
            1,4,2,3").unwrap();

        assert!(constraint.check(&grid));
        assert!(constraint.check_cell(&grid, 0, 1));
        assert!(constraint.check_cell(&grid, 2, 2));
        assert!(constraint.check_cell(&grid, 1, 1));
        assert!(constraint.check_cell(&grid, 3, 1));
        assert!(constraint.check_number(&grid, 0, 1, 1));
        assert!(constraint.check_number(&grid, 2, 2, 1));
        assert!(constraint.check_number(&grid, 3, 1, 2));
    }

    #[test]
    fn sandwich_satisfied_partial() {
        let constraint = example_constraint();
        let grid = SudokuGrid::parse("2x2;
             ,1,3, ,\
             , ,1, ,\
            3,2, ,1,\
            1,4, , ").unwrap();

        assert!(constraint.check(&grid));
        assert!(constraint.check_cell(&grid, 0, 1));
        assert!(constraint.check_cell(&grid, 2, 2));
        assert!(constraint.check_cell(&grid, 1, 1));
        assert!(constraint.check_cell(&grid, 3, 1));
        assert!(constraint.check_number(&grid, 3, 1, 2));
        assert!(constraint.check_number(&grid, 3, 0, 4));
        assert!(constraint.check_number(&grid, 1, 0, 4));
        assert!(constraint.check_number(&grid, 2, 2, 4));
    }

    #[test]
    fn sandwich_violated_full() {
        let constraint = example_constraint();
        let mut grid = SudokuGrid::parse("2x2;
            2,1,3,4,\
            4,3,1,2,\
            3,3,4,1,\
            1,4,2,3").unwrap();

        assert!(!constraint.check(&grid));
        assert!(constraint.check_cell(&grid, 2, 2));
        assert!(!constraint.check_cell(&grid, 1, 2));

        grid.set_cell(1, 2, 2).unwrap();
        grid.set_cell(3, 1, 1).unwrap();
        
        assert!(!constraint.check(&grid));
        assert!(constraint.check_cell(&grid, 1, 1));
        assert!(!constraint.check_cell(&grid, 3, 0));
        assert!(!constraint.check_number(&grid, 1, 1, 2));
    }

    #[test]
    fn sandwich_violated_partial() {
        let constraint = example_constraint();
        let grid = SudokuGrid::parse("2x2;
             ,1,3, ,\
             , ,1, ,\
            3,4, ,1,\
            1, , , ").unwrap();

        assert!(!constraint.check(&grid));
        assert!(constraint.check_cell(&grid, 0, 1));
        assert!(!constraint.check_cell(&grid, 1, 0));
        assert!(constraint.check_number(&grid, 1, 2, 3));
        assert!(!constraint.check_number(&grid, 1, 1, 3));
    }

    #[test]
    fn sandwich_constraint_violated_missing_bun() {
        let constraint = example_constraint();
        let grid = SudokuGrid::parse("2x2;
             , , , ,\
             ,2, , ,\
             ,3, , ,\
             ,3, , ").unwrap();

        assert!(!constraint.check(&grid));
        assert!(constraint.check_cell(&grid, 0, 1));
        assert!(!constraint.check_cell(&grid, 1, 0));
        assert!(!constraint.check_number(&grid, 1, 0, 1));
    }

    #[test]
    fn sandwich_constraint_violated_extra_bun() {
        let constraint = example_constraint();
        let grid = SudokuGrid::parse("2x2;
            1, ,4,1,\
             , , , ,\
             , , , ,\
             , , , ").unwrap();

        assert!(!constraint.check(&grid));
        assert!(constraint.check_cell(&grid, 1, 1));
        assert!(!constraint.check_cell(&grid, 0, 0));
        assert!(!constraint.check_number(&grid, 1, 0, 3));
    }

    #[test]
    fn sandwich_constraint_does_not_require_two_buns_in_row_without_sum() {
        let constraint = example_constraint();
        let grid = SudokuGrid::parse("2x2;
             , , , ,\
             , , , ,\
             , , , ,\
            1, ,4,1").unwrap();

        assert!(constraint.check(&grid));
        assert!(constraint.check_cell(&grid, 2, 3));
        assert!(constraint.check_number(&grid, 1, 3, 1));
    }
}
