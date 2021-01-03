//! This module is about strategic solving of Sudoku. In contrast to
//! backtracking, this is often faster, but cannot solve all Sudoku. However,
//! strategic backtracking is also possible, which still uses backtracking, but
//! also uses strategies to reduce the search space. This is solely a
//! performance optimization and offers no functional advantage over pure
//! backtracking. For more information, view the [StrategicBacktrackingSolver].
//!
//! This module contains the definition of the [Strategy] trait, which all
//! strategies must implement, as well as the [SudokuInfo] struct, which wraps
//! metadata about Sudoku that can be used by strategies to exchange
//! information.
//!
//! `sudoku-variants` offers a small library of pre-defined strategies you can
//! use. See the documentation of those for further details.
//!
//! # Defining difficulties using strategies
//!
//! Besides a performance optimization for backtracking, strategies also have
//! the use of defining a difficulty level for generated Sudoku. This can be
//! done by instantiating the [Reducer](crate::generator::Reducer) with a
//! [StrategicSolver]. The resulting Sudoku is then guaranteed to be solveable
//! by the provided strategy. As an example consider the following code, which
//! generates a classic Sudoku that can be solved by solely looking for naked
//! singles (see [NakedSingleStrategy]).
//!
//! ```
//! use sudoku_variants::constraint::DefaultConstraint;
//! use sudoku_variants::generator::{Generator, Reducer};
//! use sudoku_variants::solver::{Solution, Solver};
//! use sudoku_variants::solver::strategy::{
//!     NakedSingleStrategy,
//!     StrategicSolver
//! };
//!
//! // Generate the full Sudoku
//! let mut generator = Generator::new_default();
//! let mut sudoku = generator.generate(3, 3, DefaultConstraint).unwrap();
//! let expected_solution = sudoku.grid().clone();
//!
//! // Define the difficulty level by providing a not-so-powerful solver
//! let solver = StrategicSolver::new(NakedSingleStrategy);
//!
//! // Reduce the Sudoku using the solver
//! let mut reducer = Reducer::new(solver.clone(), rand::thread_rng());
//! reducer.reduce(&mut sudoku);
//!
//! // Test that the solver can in fact solve the Sudoku
//! let actual_solution = solver.solve(&sudoku);
//! assert_eq!(Solution::Unique(expected_solution), actual_solution);
//! ```
//!
//! # Implementing a custom strategy
//!
//! As an example let's define a strategy that puts a 1 in every cell without
//! any other option. This is a subset of the [NakedSingleStrategy].
//!
//! To do this, we must implement the [Strategy] trait, which only requires the
//! [Strategy.apply] method. This method gets an instance of a [SudokuInfo]
//! struct for the Sudoku at hand. We must then implement our logic to make
//! deductions and if we can find something, that is, we can write in a digit
//! or remove an option, we can modify the sudoku info. If we changed
//! something, we must return true, and false otherwise. This indicates to the
//! solvers whether it is useful to apply this strategy or other strategies
//! again, since we may find something new.
//!
//! In our case, we can implement this method as follows:
//!
//! ```
//! use sudoku_variants::constraint::Constraint;
//! use sudoku_variants::solver::strategy::{Strategy, SudokuInfo};
//!
//! struct NakedOneStrategy;
//!
//! impl Strategy for NakedOneStrategy {
//!     fn apply(&self, sudoku_info: &mut SudokuInfo<impl Constraint + Clone>)
//!             -> bool {
//!         let size = sudoku_info.sudoku().grid().size();
//!         let mut changed = false;
//!
//!         // We must iterate over every cell.
//!         for row in 0..size {
//!             for column in 0..size {
//!                 // The SudokuInfo struct stores which digits could go into
//!                 // each cell. We can get that information with get_options.
//!                 let options =
//!                     sudoku_info.get_options(column, row).unwrap();
//!
//!                 if options.len() == 1 && options.contains(1) {
//!                     // Only a 1 can go into this cell! We found something!
//!                     // We batch all changes using enter_cell_no_update for
//!                     // performance reasons.
//!                     sudoku_info.enter_cell_no_update(column, row, 1)
//!                         .unwrap();
//!                     changed = true;
//!                 }
//!             }
//!         }
//!
//!         changed
//!     }
//! }
//! ```

use crate::Sudoku;
use crate::constraint::Constraint;
use crate::error::{SudokuError, SudokuResult};
use crate::util::USizeSet;

pub mod impls;
pub mod solvers;

pub use impls::*;
pub use solvers::*;

/// Enriches a [Sudoku] with additional information about which numbers can go
/// into the cells. This is analogous to the pencil markings a human player
/// would make. It is used by [Strategies](Strategy) to communicate the results
/// of logical reasoning.
///
/// This struct already excludes options which violate the Sudoku's constraint,
/// unless unprocessed changes have been made.
#[derive(Clone)]
pub struct SudokuInfo<C: Constraint + Clone> {
    sudoku: Sudoku<C>,
    cell_options: Vec<USizeSet>,
    enqueued_cells: Vec<(usize, usize, usize)>,
    up_to_date: bool
}

impl<C: Constraint + Clone> SudokuInfo<C> {

    /// Creates a new Sudok info for a [Sudoku]. The options for all cells that
    /// are empty in the provided Sudoku are all valid digits, and the options
    /// for cells which are filled in the Sudoku are only the digit in that
    /// cell.
    pub fn from_sudoku(sudoku: Sudoku<C>) -> SudokuInfo<C> {
        let size = sudoku.grid().size();
        let mut cell_options = Vec::new();

        for row in 0..size {
            for column in 0..size {
                let cell = sudoku.grid().get_cell(column, row).unwrap();
                let options = match cell {
                    Some(number) =>
                        USizeSet::singleton(1, size, number).unwrap(),
                    None => {
                        let mut options = USizeSet::new(1, size).unwrap();

                        for option in 1..=size {
                            let is_valid = sudoku
                                .is_valid_number(column, row, option)
                                .unwrap();

                            if is_valid {
                                options.insert(option).unwrap();
                            }
                        }

                        options
                    }
                };

                cell_options.push(options);
            }
        }

        SudokuInfo {
            sudoku,
            cell_options,
            enqueued_cells: Vec::new(),
            up_to_date: true
        }
    }

    fn verified_index(&self, column: usize, row: usize)
            -> SudokuResult<usize> {
        let size = self.size();

        if column >= size || row >= size {
            Err(SudokuError::OutOfBounds)
        }
        else {
            Ok(crate::index(column, row, size))
        }
    }

    /// Gets the content of the cell at the specified position.
    ///
    /// This is syntactic sugar for `x.sudoku().grid().get_cell(...)`.
    ///
    /// # Arguments
    ///
    /// * `column`: The column (x-coordinate) of the desired cell. Must be in
    /// the range `[0, size[`.
    /// * `row`: The row (y-coordinate) of the desired cell. Must be in the
    /// range `[0, size[`.
    ///
    /// # Errors
    ///
    /// If either `column` or `row` are not in the specified range. In that
    /// case, `SudokuError::OutOfBounds` is returned.
    pub fn get_cell(&self, column: usize, row: usize)
            -> SudokuResult<Option<usize>> {
        self.sudoku.grid().get_cell(column, row)
    }

    /// Enqueues a number to be assigned to the content of the cell at the
    /// specified position on the next update. If the cell is not empty at that
    /// point, the old number will be overwritten.
    ///
    /// In contrast with
    /// [enter_cell_no_update](SudokuInfo::enter_cell_no_update), this function
    /// never enters the number into the cell right away, so when querying the
    /// cell it will still look empty. This is done both for performance
    /// reasons and to preserve semantics of only applying a strategy once for
    /// strategies which may process the same cell more than once, which is
    /// important for the bounded backtracking strategies. To ensure that the
    /// state of this is up-to-date, i.e. the new cells are entered and the
    /// options are adapted to accomodate for them, call
    /// [invalidate](SudokuInfo::invalidate) after you are finished enqueueing
    /// changes.
    ///
    /// # Arguments
    ///
    /// * `column`: The column (x-coordinate) of the assigned cell. Must be in
    /// the range `[0, size[`.
    /// * `row`: The row (y-coordinate) of the assigned cell. Must be in the
    /// range `[0, size[`.
    /// * `number`: The number to assign to the specified cell. Must be in the
    /// range `[1, size]`.
    ///
    /// # Errors
    ///
    /// * `SudokuError::OutOfBounds` If either `column` or `row` are not in the
    /// specified range.
    /// * `SudokuError::InvalidNumber` If `number` is not in the specified
    /// range.
    pub fn enqueue_enter_cell(&mut self, column: usize, row: usize,
            number: usize) -> SudokuResult<()> {
        let size = self.sudoku.grid().size();

        if column >= size || row >= size {
            return Err(SudokuError::InvalidDimensions);
        }

        if number < 1 || number > size {
            return Err(SudokuError::InvalidNumber);
        }

        self.enqueued_cells.push((column, row, number));
        self.up_to_date = false;
        Ok(())
    }

    /// Sets the content of the cell at the specified position to the given
    /// number. If the cell was not empty, the old number will be overwritten.
    ///
    /// In contrast with [enter_cell](SudokuInfo::enter_cell), this method does
    /// not remove cell options that are invalidated by the new digit. This is
    /// done for performance reasons to allow batching of multiple changes
    /// before updating the options. To ensure the cell options are up-to-date,
    /// call [invalidate](SudokuInfo::invalidate) after making any changes.
    ///
    /// # Arguments
    ///
    /// * `column`: The column (x-coordinate) of the assigned cell. Must be in
    /// the range `[0, size[`.
    /// * `row`: The row (y-coordinate) of the assigned cell. Must be in the
    /// range `[0, size[`.
    /// * `number`: The number to assign to the specified cell. Must be in the
    /// range `[1, size]`.
    ///
    /// # Errors
    ///
    /// * `SudokuError::OutOfBounds` If either `column` or `row` are not in the
    /// specified range.
    /// * `SudokuError::InvalidNumber` If `number` is not in the specified
    /// range.
    pub fn enter_cell_no_update(&mut self, column: usize, row: usize,
            number: usize) -> SudokuResult<()> {
        self.sudoku.grid_mut().set_cell(column, row, number)?;
        let options = self.get_options_mut(column, row).unwrap();
        options.clear();
        options.insert(number).unwrap();
        self.up_to_date = false;
        Ok(())
    }

    /// Sets the content of the cell at the specified position to the given
    /// number. If the cell was not empty, the old number will be overwritten.
    ///
    /// In contrast with
    /// [enter_cell_no_update](SudokuInfo::enter_cell_no_update), this method
    /// immediately removes all cell options that are invalidated by the new
    /// digit.
    ///
    /// # Arguments
    ///
    /// * `column`: The column (x-coordinate) of the assigned cell. Must be in
    /// the range `[0, size[`.
    /// * `row`: The row (y-coordinate) of the assigned cell. Must be in the
    /// range `[0, size[`.
    /// * `number`: The number to assign to the specified cell. Must be in the
    /// range `[1, size]`.
    ///
    /// # Errors
    ///
    /// * `SudokuError::OutOfBounds` If either `column` or `row` are not in the
    /// specified range.
    /// * `SudokuError::InvalidNumber` If `number` is not in the specified
    /// range.
    pub fn enter_cell(&mut self, column: usize, row: usize, number: usize)
            -> SudokuResult<()> {
        self.enter_cell_no_update(column, row, number)?;
        self.update();
        Ok(())
    }

    fn update(&mut self) {
        let size = self.size();
        let mut options_to_remove = Vec::new();
        let enqueued_cells: Vec<(usize, usize, usize)> =
            self.enqueued_cells.drain(..).collect();

        for (column, row, number) in enqueued_cells {
            self.enter_cell_no_update(column, row, number).unwrap();
        }

        for row in 0..size {
            for column in 0..size {
                let content = self.sudoku.grid().get_cell(column, row)
                    .unwrap();

                if let Some(_) = content {
                    continue;
                }

                // TODO find a way to use get_options without triggering the
                // borrow checker

                let options =
                    &mut self.cell_options[crate::index(column, row, size)];
                options_to_remove.clear();

                for option in options.iter() {
                    let is_valid = self.sudoku
                        .is_valid_number(column, row, option)
                        .unwrap();

                    if !is_valid {
                        options_to_remove.push(option);
                    }
                }

                for &option_to_remove in options_to_remove.iter() {
                    options.remove(option_to_remove).unwrap();
                }
            }
        }

        self.up_to_date = true;
    }

    /// Removes all cell options that have been invalidated by digits entered
    /// using [enter_cell_no_update](SudokuInfo::enter_cell_no_update) which
    /// have not yet been processed. If there are no pending digits, nothing
    /// will be done.
    pub fn invalidate(&mut self) {
        if !self.up_to_date {
            self.update();
        }
    }

    /// Gets a [USizeSet] of the possible digits that can be entered into the
    /// cell at the given position according to this grid info.
    ///
    /// Note that, because options are adapted to new digits lazily, this
    /// operation may require changes to this instance, namely if digits were
    /// changed since the last call to `get_options` or `get_options_mut`. This
    /// means a mutable reference to this instance is required.
    ///
    /// # Arguments
    ///
    /// * `column`: The column (x-coordinate) of the desired cell. Must be in
    /// the range `[0, size[`.
    /// * `row`: The row (y-coordinate) of the desired cell. Must be in the
    /// range `[0, size[`.
    ///
    /// # Errors
    ///
    /// If either `column` or `row` are not in the specified range. In that
    /// case, `SudokuError::OutOfBounds` is returned.
    pub fn get_options(&self, column: usize, row: usize)
            -> SudokuResult<&USizeSet> {
        let index = self.verified_index(column, row)?;
        Ok(&self.cell_options[index])
    }

    /// Gets a mutable reference to the [USizeSet] that tracks the possible
    /// digits that can be entered into the cell at the given position
    /// according to this grid info.
    ///
    /// Note that, because options are adapted to new digits lazily, this
    /// operation may require changes to this instance, namely if digits were
    /// changed since the last call to `get_options` or `get_options_mut`.
    ///
    /// # Arguments
    ///
    /// * `column`: The column (x-coordinate) of the desired cell. Must be in
    /// the range `[0, size[`.
    /// * `row`: The row (y-coordinate) of the desired cell. Must be in the
    /// range `[0, size[`.
    ///
    /// # Errors
    ///
    /// If either `column` or `row` are not in the specified range. In that
    /// case, `SudokuError::OutOfBounds` is returned.
    pub fn get_options_mut(&mut self, column: usize, row: usize)
            -> SudokuResult<&mut USizeSet> {
        let index = self.verified_index(column, row)?;
        Ok(&mut self.cell_options[index])
    }

    /// Gets the total size of the grid for which this instance tracks
    /// information on one axis (horizontally or vertically). Since grids are
    /// always squares, this is guaranteed to be valid for both axes.
    pub fn size(&self) -> usize {
        self.sudoku.grid().size()
    }

    /// Gets a read-only reference to the vector storing the options for every
    /// cell in a [USizeSet]. The cells are in eft-to-right, top-to-bottom
    /// order, where rows are together.
    pub fn cell_options(&self) -> &Vec<USizeSet> {
        &self.cell_options
    }

    /// Gets a mutable reference to the vector storing the options for every
    /// cell in a [USizeSet]. The cells are in left-to-right, top-to-bottom
    /// order, where rows are together.
    pub fn cell_options_mut(&mut self) -> &mut Vec<USizeSet> {
        &mut self.cell_options
    }

    /// Gets the width (number of columns) of one sub-block of the Sudoku. To
    /// ensure a square grid, this is also the number of blocks that compose
    /// the grid vertically.
    ///
    /// This is syntactic sugar for `x.sudoku().grid().block_width()`.
    pub fn block_width(&self) -> usize {
        self.sudoku.grid().block_width()
    }

    /// Gets the height (number of rows) of one sub-block of the Sudoku. To
    /// ensure a square grid, this is also the number of blocks that compose
    /// the grid horizontally.
    ///
    /// This is syntactic sugar for `x.sudoku().grid().block_height()`.
    pub fn block_height(&self) -> usize {
        self.sudoku.grid().block_height()
    }

    /// Assigns the content of another grid info to this one, that is, after
    /// the operation this grid info will equal `other`. The dimensions must be
    /// equivalent.
    ///
    /// # Errors
    ///
    /// If `other` has different dimensions to this instance. In that case,
    /// `SudokuError::InvalidDimensions` is returned.
    pub fn assign(&mut self, other: &SudokuInfo<C>) -> SudokuResult<()> {
        self.sudoku.grid_mut().assign(other.sudoku.grid())?;

        for i in 0..self.cell_options.len() {
            self.cell_options[i] = other.cell_options[i].clone();
        }

        Ok(())
    }

    /// Gets the [Sudoku] for which this Sudoku info stores additional
    /// information.
    pub fn sudoku(&self) -> &Sudoku<C> {
        &self.sudoku
    }

    /// Gets a mutable reference to the [Sudoku] for which this Sudoku info
    /// stores additional information.
    pub fn sudoku_mut(&mut self) -> &mut Sudoku<C> {
        &mut self.sudoku
    }

    fn op(&mut self, other: &SudokuInfo<C>,
            single_op: impl Fn((&mut Option<usize>, &mut USizeSet),
                (&Option<usize>, &USizeSet)) -> bool)
            -> SudokuResult<bool> {
        if self.block_width() != other.block_width() ||
                self.block_height() != other.block_height() {
            return Err(SudokuError::InvalidDimensions);
        }

        let mut changed = false;
        let iter = (&mut self.sudoku).grid_mut().cells_mut().iter_mut()
            .zip((&mut self.cell_options).iter_mut())
            .zip(other.sudoku().grid().cells().iter()
                .zip(other.cell_options().iter()));
        
        for (self_info, other_info) in iter {
            changed |= single_op(self_info, other_info);
        }

        Ok(changed)
    }

    /// Intersects this Sudoku info with the given other one, implying that all
    /// information of both is correct. All cells that are filled in in either
    /// will be written in the result and only options that are present in both
    /// will be retained. Note that contradictions (different digits in this
    /// and the other Sudoku info) will result in the cell being cleared and
    /// all options being removed.
    pub fn intersect_assign(&mut self, other: &SudokuInfo<C>)
            -> SudokuResult<bool> {
        self.op(other, |(self_cell, self_options), (other_cell, other_options)| {
            let cells_changed = if let Some(number) = other_cell {
                let old_number = self_cell.replace(*number);

                if Some(*number) == old_number {
                    false
                }
                else {
                    if let Some(_) = old_number {
                        self_options.clear();
                        self_cell.take();
                    }

                    true
                }
            }
            else {
                false
            };
            let options_changed =
                self_options.intersect_assign(other_options).unwrap();
            cells_changed || options_changed
        })
    }

    /// Unifies this Sudoku info with the given other one, implying that all
    /// information of both *could* be correct. Options present in at least one
    /// will be put in the result and digits are only retained if they are
    /// present in both (unless the other does not have any options for that
    /// cell). Note that contradictions (different digits in this
    /// and the other Sudoku info) will result in the cell being cleared and
    /// both numbers being put in the option set.
    pub fn union_assign(&mut self, other: &SudokuInfo<C>)
            -> SudokuResult<bool> {
        self.op(other, |(self_cell, self_options), (other_cell, other_options)| {
            let content_changed = if let Some(self_number) = self_cell {
                if &Some(*self_number) == other_cell || other_options.is_empty() {
                    false
                }
                else if let Some(other_number) = other_cell {
                    self_options.clear();
                    self_options.insert(*self_number).unwrap();
                    self_options.insert(*other_number).unwrap();
                    self_cell.take();
                    return true;
                }
                else {
                    self_cell.take();
                    true
                }
            }
            else if self_options.is_empty() {
                *self_cell = other_cell.clone();
                self_cell != &mut None
            }
            else {
                false
            };
            let options_changed = self_options.union_assign(other_options).unwrap();
            content_changed || options_changed
        })
    }
}

impl<C: Constraint + Clone> PartialEq for SudokuInfo<C> {
    fn eq(&self, other: &Self) -> bool {
        if self.sudoku().grid() != other.sudoku().grid() {
            false
        }
        else if !self.up_to_date {
            let mut lhs = self.clone();
            lhs.update();
            lhs.eq(other)
        }
        else if !other.up_to_date {
            let mut other = other.clone();
            other.update();
            self.eq(&other)
        }
        else {
            self.cell_options() == other.cell_options()
        }
    }
}

/// A trait for strategies, which use logical reasoning to restrict the
/// possibilities of a Sudoku.
pub trait Strategy {

    /// Applies this strategy to the given Sudoku. The strategy may rely on and
    /// modify the information in the given `sudoku_info`. This instance is
    /// given to other strategies that participate in the solution and/or
    /// future iterations of the same strategy. It can thus be used to
    /// communicate insights.
    ///
    /// This method shall return `true` if and only if something has changed,
    /// that is, a digit has been entered or an option has been removed.
    fn apply(&self, sudoku_info: &mut SudokuInfo<impl Constraint + Clone>)
        -> bool;
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::Sudoku;
    use crate::constraint::DefaultConstraint;

    #[test]
    fn sudoku_info_equality() {
        let sudoku = Sudoku::parse("2x2;\
             ,1, ,4,\
             ,2,3, ,\
             , , ,2,\
             , , , ", DefaultConstraint).unwrap();
        let mut si1 = SudokuInfo::from_sudoku(sudoku.clone());
        let mut si2 = SudokuInfo::from_sudoku(sudoku);

        assert!(si1 == si2);

        si1.enter_cell_no_update(3, 1, 1).unwrap();
        assert!(si1 != si2);
        si2.enter_cell_no_update(3, 1, 1).unwrap();
        assert!(si1 == si2);

        si1.update();
        assert!(si1 == si2);
        si2.update();
        assert!(si1 == si2);

        si1.get_options_mut(0, 3).unwrap().remove(1).unwrap();
        assert!(si1 != si2);
    }
    
    fn get_different_sudoku_infos()
            -> (SudokuInfo<DefaultConstraint>, SudokuInfo<DefaultConstraint>) {
        let sudoku = Sudoku::parse("2x2;\
             ,1, ,4,\
             ,2,3, ,\
             , , ,2,\
             , , , ", DefaultConstraint).unwrap();
        let mut si1 = SudokuInfo::from_sudoku(sudoku.clone());
        let mut si2 = SudokuInfo::from_sudoku(sudoku);
        
        si1.enter_cell(2, 0, 2).unwrap();
        si1.enter_cell(3, 1, 1).unwrap();
        si2.enter_cell(3, 1, 1).unwrap();
        
        si1.get_options_mut(0, 3).unwrap().remove(1).unwrap();
        si2.get_options_mut(0, 3).unwrap().remove(1).unwrap();
        si2.get_options_mut(1, 3).unwrap().remove(3).unwrap();
        
        (si1, si2)
    }

    #[test]
    fn sudoku_info_union() {
        let (mut si1, si2) = get_different_sudoku_infos();

        assert!(si1.union_assign(&si2).unwrap());

        assert_eq!(None, si1.get_cell(2, 0).unwrap());
        assert_eq!(Some(1), si1.get_cell(3, 1).unwrap());

        assert!(!si1.get_options(0, 3).unwrap().contains(1));
        assert!(si1.get_options(1, 3).unwrap().contains(3));
    }

    #[test]
    fn sudoku_info_intersect() {
        let (mut si1, si2) = get_different_sudoku_infos();

        assert!(si1.intersect_assign(&si2).unwrap());

        assert_eq!(Some(2), si1.get_cell(2, 0).unwrap());
        assert_eq!(Some(1), si1.get_cell(3, 1).unwrap());

        assert!(!si1.get_options(0, 3).unwrap().contains(1));
        assert!(!si1.get_options(1, 3).unwrap().contains(3));
    }

    #[test]
    fn sudoku_info_operation_err() {
        let sudoku1 = Sudoku::parse("1x2;1,2,2,1", DefaultConstraint).unwrap();
        let sudoku2 = Sudoku::parse("2x1;1,2,2,1", DefaultConstraint).unwrap();
        let mut si1 = SudokuInfo::from_sudoku(sudoku1);
        let si2 = SudokuInfo::from_sudoku(sudoku2);

        assert_eq!(Err(SudokuError::InvalidDimensions), si1.union_assign(&si2));
        assert_eq!(Err(SudokuError::InvalidDimensions), si1.intersect_assign(&si2));
    }
}
