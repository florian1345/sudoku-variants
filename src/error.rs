//! This module contains some error and result definitions used in this crate.

use std::num::ParseIntError;

/// Miscellaneous errors that can occur on some methods in the
/// [root module](../index.html). This does not exclude errors that occur when
/// parsing Sudoku, see [SudokuParseError](enum.SudokuParseError.html) for
/// that.
#[derive(Debug, Eq, PartialEq)]
pub enum SudokuError {

    /// Indicates that the dimensions specified for a created Sudoku are
    /// invalid. This is the case if they are less than 1.
    InvalidDimensions,

    /// Indicates that some number is invalid for the size of the grid in
    /// question. This is the case if it is less than 1 or greater than the
    /// size.
    InvalidNumber,

    /// Indicates that the specified coordinates (column and row) lie outside
    /// the Sudoku grid in question. This is the case if they are greater than
    /// or equal to the size.
    OutOfBounds,

    /// An error that is raised whenever it is attempted to generate a Sudoku
    /// with a constraint that is not satisfied by any Sudoku with the given
    /// parameters.
    UnsatisfiableConstraint
}

/// Syntactic sugar for `Result<V, SudokuError>`.
pub type SudokuResult<V> = Result<V, SudokuError>;

/// An enumeration of the errors that may occur when parsing a `Sudoku` or
/// `SudokuGrid`.
#[derive(Debug, Eq, PartialEq)]
pub enum SudokuParseError {

    /// Indicates that the code has the wrong number of parts, which are
    /// separated by semicolons. The code should have two parts: dimensions and
    /// cells (separated by ';'), so if the code does not contain exactly one
    /// semicolon, this error will be returned.
    WrongNumberOfParts,

    /// Indicates that the number of cells (which are separated by commas) does
    /// not equal the number deduced from the dimensions.
    WrongNumberOfCells,

    /// Indicates that the dimensions have the wrong format. They should be of
    /// the form `<block_width>x<block_height>`, so if the amount of 'x's in
    /// the dimension string is not exactly one, this error will be raised.
    MalformedDimensions,

    /// Indicates that the provided dimensions are invalid (i.e. at least one
    /// is zero).
    InvalidDimensions,

    /// Indicates that one of the numbers (dimension or cell content) could not
    /// be parsed.
    NumberFormatError,

    /// Indicates that a cell is filled with an invalid number (0 or more than
    /// the grid size).
    InvalidNumber
}

impl From<ParseIntError> for SudokuParseError {
    fn from(_: ParseIntError) -> Self {
        SudokuParseError::NumberFormatError
    }
}
