// Code lints

#![warn(trivial_casts)]
#![warn(trivial_numeric_casts)]
#![warn(unreachable_pub)]
#![warn(unused_import_braces)]
#![warn(unused_lifetimes)]
#![warn(unused_qualifications)]

// Doc lints

#![warn(broken_intra_doc_links)]
#![warn(missing_docs)]
#![warn(missing_crate_level_docs)]
#![warn(invalid_codeblock_attributes)]

//! This crate implements an easy-to-understand and flexible Sudoku engine. It
//! supports the following key features:
//!
//! * Parsing and printing Sudoku
//! * Checking validity of Sudoku and solutions according to standard rules as
//! well as some common variants
//! * Injection of custom constraints
//! * Solving Sudoku using a perfect backtracking algorithm
//! * Generating Sudoku with a possibility to specify a custom solver that has
//! to be able to solve the result, thus controlling the difficulty
//!
//! Note in this introduction we will mostly be using 4x4 Sudoku due to their
//! simpler nature. These are divided in 4 2x2 blocks, each with the digits 1
//! to 4, just like each row and column.
//!
//! # Parsing and printing Sudoku
//!
//! See [SudokuGrid::parse] for the exact format of a Sudoku code.
//!
//! Codes can be used to exchange Sudoku, while pretty prints can be used to
//! display a Sudoku in a clearer manner. An example of how to parse and
//! display a Sudoku grid is provided below.
//!
//! ```
//! use sudoku_variants::SudokuGrid;
//!
//! let grid =
//!     SudokuGrid::parse("2x2;2, ,3, , ,1, , ,1, , ,4, ,2, ,3").unwrap();
//! println!("{}", grid);
//! ```
//!
//! # Checking validity of Sudoku
//!
//! To check validity, an instance of [Sudoku] not only contains the numbers
//! (stored in a [SudokuGrid]), but also some constraint which specifies the
//! rules. For classic Sudoku rules,
//! [DefaultConstraint](constraint::DefaultConstraint) can be used.
//!
//! It is possible to check an entire Sudoku, individual cells, or potential
//! changes to individual cells that do not require changing the Sudoku's
//! state. An example of the former is provided below.
//!
//! ```
//! use sudoku_variants::Sudoku;
//! use sudoku_variants::constraint::DefaultConstraint;
//!
//! // Some Sudoku for which it is totally unclear whether it is valid.
//! let sudoku = Sudoku::parse("2x2;1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1",
//!     DefaultConstraint).unwrap();
//! assert!(!sudoku.is_valid());
//! ```
//!
//! If you are developing an app that gives feedback to the user, it may be
//! desirable to specify where they made an error. Also, sometimes checking the
//! entire Sudoku is redundant, since only one cell has changed. To do this, it
//! is possible to check the validity of just one cell in the grid.
//!
//! ```
//! use sudoku_variants::Sudoku;
//! use sudoku_variants::constraint::DefaultConstraint;
//!
//! // A riddle posed by our app:
//! // ╔═══╤═══╦═══╤═══╗
//! // ║   │   ║   │ 4 ║
//! // ╟───┼───╫───┼───╢
//! // ║   │ 4 ║ 3 │   ║
//! // ╠═══╪═══╬═══╪═══╣
//! // ║   │ 3 ║   │   ║
//! // ╟───┼───╫───┼───╢
//! // ║   │   ║ 1 │   ║
//! // ╚═══╧═══╩═══╧═══╝
//! let mut sudoku = Sudoku::parse("2x2; , , ,4, ,4,3, , ,3, , , , ,1, ",
//!     DefaultConstraint).unwrap();
//!
//! // Some (unfortunatly wrong) user input to the top-left cell
//! sudoku.grid_mut().set_cell(0, 0, 4);
//! assert!(!sudoku.is_valid_cell(0, 0).unwrap());
//! ```
//!
//! Similarly, it is also possible to check a singular cell with a potntial new
//! entry, before changing the Sudoku, using [Sudoku::is_valid_number]. Since
//! it otherwise behaves just like the example above, we will not provide
//! another example.
//!
//! All examples above have been using the
//! [DefaultConstraint](constraint::DefaultConstraint), which is actually a
//! composition of [RowConstraint](constraint::RowConstraint),
//! [ColumnConstraint](constraint::ColumnConstraint), and
//! [BlockConstraint](constraint::BlockConstraint). Additionally to
//! those three primitives, a few more common Sudoku variants' rules are
//! provided, which can be combined into more exciting rule sets. Check out the
//! [constraint] module for more details and instructions on how to write your
//! own rules.
//!
//! # Solving Sudoku
//!
//! This crate offers a [Solver](solver::Solver) trait for structs that can
//! totally or partially solve Sudoku (that is, able to solve every Sudoku with
//! a unique solution or not). As a default implementation,
//! [BacktrackingSolver](solver::BacktrackingSolver) is provided, which can
//! solve every uniquely solveable Sudoku.
//!
//! To use it, first instantiate a Sudoku an then call
//! [Solver.solve](solver::Solver::solve) on a backtracking
//! solver (as it is a zero-sized struct, no instantiation is required).
//!
//! ```
//! use sudoku_variants::{Sudoku, SudokuGrid};
//! use sudoku_variants::constraint::DefaultConstraint;
//! use sudoku_variants::solver::{BacktrackingSolver, Solution, Solver};
//!
//! // The same Sudoku as in our previous example.
//! let sudoku = Sudoku::parse("2x2; , , ,4, ,4,3, , ,3, , , , ,1, ",
//!     DefaultConstraint).unwrap();
//! let solution = BacktrackingSolver.solve(&sudoku);
//!
//! // The solution we expect:
//! // ╔═══╤═══╦═══╤═══╗
//! // ║ 3 │ 1 ║ 2 │ 4 ║
//! // ╟───┼───╫───┼───╢
//! // ║ 2 │ 4 ║ 3 │ 1 ║
//! // ╠═══╪═══╬═══╪═══╣
//! // ║ 1 │ 3 ║ 4 │ 2 ║
//! // ╟───┼───╫───┼───╢
//! // ║ 4 │ 2 ║ 1 │ 3 ║
//! // ╚═══╧═══╩═══╧═══╝
//! let expected_solution_grid =
//!     SudokuGrid::parse("2x2;3,1,2,4,2,4,3,1,1,3,4,2,4,2,1,3").unwrap();
//!
//! assert_eq!(Solution::Unique(expected_solution_grid), solution);
//! ```
//!
//! The backtracking solver can deal with any (correctly implemented)
//! constraint and type of Sudoku. If there is no solution, it will return
//! `Solution::Impossible` and if there are multiple solutions, it will reutrn
//! `Solution::Ambiguous`.
//!
//! # Generating Sudoku
//!
//! Probably the most interesting feature of this crate is the generation of
//! random Sudoku. This is done in two steps: generating a full grid using a
//! [Generator](generator::Generator) and then removing as many clues as
//! possible using a [Reducer](generator::Reducer).
//!
//! The generator needs a solver, which helps to reduce the search space for
//! valid grids, and a random number generator, for which we use the `Rng`
//! trait from the [rand](https://rust-random.github.io/rand/rand/index.html)
//! crate. The reducer needs the same, however its solver is used to define the
//! difficulty. Essentially, the reducer will generate a puzzle that is just
//! not too hard for the given solver, that is, if one more clue were removed,
//! the solver would be unable to solve it. An example of generating a minimal
//! puzzle (where no clues can be removed without losing uniqueness) is
//! provided below.
//!
//! ```
//! use sudoku_variants::constraint::DefaultConstraint;
//! use sudoku_variants::generator::{Generator, Reducer};
//! use sudoku_variants::solver::{BacktrackingSolver, Solution, Solver};
//!
//! // new_default yields a generator/reducer with a backtracking solver and
//! // rand::thread_rng()
//! let mut generator = Generator::new_default();
//! let mut reducer = Reducer::new_default();
//!
//! // Generate a full, 3x3 block Sudoku board with default rules.
//! let mut sudoku = generator.generate(3, 3, DefaultConstraint).unwrap();
//! assert!(sudoku.is_valid());
//!
//! // Remove as many clues as possible
//! reducer.reduce(&mut sudoku);
//!
//! let unique = match BacktrackingSolver.solve(&sudoku) {
//!     Solution::Unique(_) => true,
//!     _ => false
//! };
//! assert!(unique);
//! ```
//!
//! # Note regarding performance
//!
//! While generating ordinary, minimal Sudoku with this crate is doable within
//! a few seconds, more complicated rule sets which result in less necessary
//! clues or larger boards may result in performance issues. In any case, it is
//! strongly recommended to use at least `opt-level = 2` for approximately a
//! 28-fold performance improvement, even in tests that use Sudoku generation.

pub mod constraint;
pub mod error;
pub mod generator;
pub mod solver;
pub mod util;

use constraint::Constraint;
use error::{SudokuError, SudokuParseError, SudokuParseResult, SudokuResult};

use std::fmt::{self, Display, Error, Formatter};

/// A Sudoku grid is composed of cells that are organized into blocks of a
/// given width and height in a way that makes the entire grid a square.
/// Consequently, the number of blocks in a row is equal to the block height
/// and vice versa. Each cell may or may not be occupied by a number.
///
/// In ordinary Sudoku, the block width and height are both 3. Here, however,
/// more exotic variants are permitted, for example 4x2 blocks, which would
/// result in a grid like this:
///
/// ```text
/// ╔═══╤═══╤═══╤═══╦═══╤═══╤═══╤═══╗
/// ║   │   │   │   ║   │   │   │   ║
/// ╟───┼───┼───┼───╫───┼───┼───┼───╢
/// ║   │   │   │   ║   │   │   │   ║
/// ╠═══╪═══╪═══╪═══╬═══╪═══╪═══╪═══╣
/// ║   │   │   │   ║   │   │   │   ║
/// ╟───┼───┼───┼───╫───┼───┼───┼───╢
/// ║   │   │   │   ║   │   │   │   ║
/// ╠═══╪═══╪═══╪═══╬═══╪═══╪═══╪═══╣
/// ║   │   │   │   ║   │   │   │   ║
/// ╟───┼───┼───┼───╫───┼───┼───┼───╢
/// ║   │   │   │   ║   │   │   │   ║
/// ╠═══╪═══╪═══╪═══╬═══╪═══╪═══╪═══╣
/// ║   │   │   │   ║   │   │   │   ║
/// ╟───┼───┼───┼───╫───┼───┼───┼───╢
/// ║   │   │   │   ║   │   │   │   ║
/// ╚═══╧═══╧═══╧═══╩═══╧═══╧═══╧═══╝
/// ```
///
/// `SudokuGrid` implements `Display`, but only grids with a size (that is,
/// width or height) of less than or equal to 9 can be displayed with digits
/// 1 to 9. Sudoku of all other sizes will raise an error.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SudokuGrid {
    block_width: usize,
    block_height: usize,
    size: usize,
    cells: Vec<Option<usize>>
}

fn to_char(cell: Option<usize>) -> char {
    if let Some(n) = cell {
        ('0' as u8 + n as u8) as char
    }
    else {
        ' '
    }
}

fn line(grid: &SudokuGrid, start: char, thick_sep: char, thin_sep: char,
        segment: impl Fn(usize) -> char, pad: char, end: char, newline: bool) -> String {
    let size = grid.size();
    let mut result = String::new();

    for x in 0..size {
        if x == 0 {
            result.push(start);
        }
        else if x % grid.block_width == 0 {
            result.push(thick_sep);
        }
        else {
            result.push(thin_sep);
        }

        result.push(pad);
        result.push(segment(x));
        result.push(pad);
    }

    result.push(end);

    if newline {
        result.push('\n');
    }

    result
}

fn top_row(grid: &SudokuGrid) -> String {
    line(grid, '╔', '╦', '╤', |_| '═', '═', '╗', true)
}

fn thin_separator_line(grid: &SudokuGrid) -> String {
    line(grid, '╟', '╫', '┼', |_| '─', '─', '╢', true)
}

fn thick_separator_line(grid: &SudokuGrid) -> String {
    line(grid, '╠', '╬', '╪', |_| '═', '═', '╣', true)
}

fn bottom_row(grid: &SudokuGrid) -> String {
    line(grid, '╚', '╩', '╧', |_| '═', '═', '╝', false)
}

fn content_row(grid: &SudokuGrid, y: usize) -> String {
    line(grid, '║', '║', '│', |x| to_char(grid.get_cell(x, y).unwrap()), ' ',
        '║', true)
}

impl Display for SudokuGrid {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let size = self.size();

        if size > 9 {
            return Err(Error::default());
        }

        let top_row = top_row(self);
        let thin_separator_line = thin_separator_line(self);
        let thick_separator_line = thick_separator_line(self);
        let bottom_row = bottom_row(self);

        for y in 0..size {
            if y == 0 {
                f.write_str(top_row.as_str())?;
            }
            else if y % self.block_height == 0 {
                f.write_str(thick_separator_line.as_str())?;
            }
            else {
                f.write_str(thin_separator_line.as_str())?;
            }

            f.write_str(content_row(self, y).as_str())?;
        }

        f.write_str(bottom_row.as_str())?;
        Ok(())
    }
}

fn to_string(cell: &Option<usize>) -> String {
    if let Some(number) = cell {
        number.to_string()
    }
    else {
        String::from("")
    }
}

pub(crate) fn index(column: usize, row: usize, size: usize) -> usize {
    row * size + column
}

fn parse_dimensions(code: &str) -> Result<(usize, usize), SudokuParseError> {
    let parts: Vec<&str> = code.split('x').collect();

    if parts.len() != 2 {
        return Err(SudokuParseError::MalformedDimensions);
    }

    Ok((parts[0].parse()?, parts[1].parse()?))
}

impl SudokuGrid {

    /// Creates a new, empty Sudoku grid where the blocks have the given
    /// dimensions. The total width and height of the grid will be equal to the
    /// product of `block_width` and `block_height`.
    ///
    /// # Arguments
    ///
    /// * `block_width`: The horizontal dimension of one sub-block of the grid.
    /// To ensure a square grid, this is also the number of blocks that compose
    /// the grid vertically. For an ordinary Sudoku grid, this is 3. Must be
    /// greater than 0.
    /// * `block_height`: The vertical dimension of one sub-block of the grid.
    /// To ensure a square grid, this is also the number of blocks that compose
    /// the grid horizontally. For an ordinary Sudoku grid, this is 3. Must be
    /// greater than 0.
    ///
    /// # Errors
    ///
    /// If `block_width` or `block_height` is invalid (zero).
    pub fn new(block_width: usize, block_height: usize)
            -> SudokuResult<SudokuGrid> {
        if block_width == 0 || block_height == 0 {
            return Err(SudokuError::InvalidDimensions);
        }

        let size = block_width * block_height;
        let cells = vec![None; size * size];

        Ok(SudokuGrid {
            block_width,
            block_height,
            size,
            cells
        })
    }

    /// Parses a code encoding a Sudoku grid. The code has to be of the format
    /// `<block_width>x<block_height>;<cells>` where `<cells>` is a
    /// comma-separated list of entries, which are either empty or a number.
    /// The entries are assigned left-to-right, top-to-bottom, where each row
    /// is completed before the next one is started. Whitespace in the entries
    /// is ignored to allow for more intuitive formatting. The number of
    /// entries must match the amount of cells in a grid with the given
    /// dimensions, i.e. it must be `(block_width · block_height)²`.
    ///
    /// As an example, the code `2x2;1, ,2, , ,3, ,4, , , ,3, ,1, ,2` will
    /// parse to the following grid:
    ///
    /// ```text
    /// ╔═══╤═══╦═══╤═══╗
    /// ║ 1 │   ║ 2 │   ║
    /// ╟───┼───╫───┼───╢
    /// ║   │ 3 ║   │ 4 ║
    /// ╠═══╪═══╬═══╪═══╣
    /// ║   │   ║ 3 │   ║
    /// ╟───┼───╫───┼───╢
    /// ║   │ 1 ║   │ 2 ║
    /// ╚═══╧═══╩═══╧═══╝
    /// ```
    ///
    /// # Errors
    ///
    /// Any specialization of `SudokuParseError` (see that documentation).
    pub fn parse(code: &str) -> SudokuParseResult<SudokuGrid> {
        let parts: Vec<&str> = code.split(';').collect();

        if parts.len() != 2 {
            return Err(SudokuParseError::WrongNumberOfParts);
        }

        let (block_width, block_height) = parse_dimensions(parts[0])?;

        if let Ok(mut grid) = SudokuGrid::new(block_width, block_height) {
            let size = grid.size();
            let numbers: Vec<&str> = parts[1].split(',').collect();

            if numbers.len() != size * size {
                return Err(SudokuParseError::WrongNumberOfCells);
            }

            for (i, number_str) in numbers.iter().enumerate() {
                let number_str = number_str.trim();

                if number_str.is_empty() {
                    continue;
                }

                let number = number_str.parse::<usize>()?;

                if number == 0 || number > size {
                    return Err(SudokuParseError::InvalidNumber);
                }

                grid.cells[i] = Some(number);
            }

            Ok(grid)
        }
        else {
            Err(SudokuParseError::InvalidDimensions)
        }
    }

    /// Converts the grid into a `String` in a way that is consistent with
    /// [SudokuGrid::parse](#method.parse). That is, a grid that is converted
    /// to a string and parsed again will not change, as is illustrated below.
    ///
    /// ```
    /// use sudoku_variants::SudokuGrid;
    ///
    /// let mut grid = SudokuGrid::new(3, 2).unwrap();
    ///
    /// // Just some arbitrary changes to create some content.
    /// grid.set_cell(1, 1, 4).unwrap();
    /// grid.set_cell(1, 2, 5).unwrap();
    ///
    /// let grid_str = grid.to_parseable_string();
    /// let grid_parsed = SudokuGrid::parse(grid_str.as_str()).unwrap();
    /// assert_eq!(grid, grid_parsed);
    /// ```
    pub fn to_parseable_string(&self) -> String {
        let mut s = format!("{}x{};", self.block_width, self.block_height);
        let cells = self.cells.iter()
            .map(to_string)
            .collect::<Vec<String>>()
            .join(",");
        s.push_str(cells.as_str());
        s
    }

    /// Gets the width (number of columns) of one sub-block of the grid. To
    /// ensure a square grid, this is also the number of blocks that compose
    /// the grid vertically.
    pub fn block_width(&self) -> usize {
        self.block_width
    }

    /// Gets the height (number of rows) of one sub-block of the grid. To
    /// ensure a square grid, this is also the number of blocks that compose
    /// the grid horizontally.
    pub fn block_height(&self) -> usize {
        self.block_height
    }

    /// Gets the total size of the grid on one axis (horizontally or
    /// vertically). Since a square grid is enforced at construction time, this
    /// is guaranteed to be valid for both axes.
    pub fn size(&self) -> usize {
        self.size
    }

    /// Gets the content of the cell at the specified position.
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
        let size = self.size();

        if column >= size || row >= size {
            Err(SudokuError::OutOfBounds)
        }
        else {
            let index = index(column, row, size);
            Ok(self.cells[index])
        }
    }

    /// Indicates whether the cell at the specified position has the given
    /// number. This will return `false` if there is a different number in that
    /// cell or it is empty.
    ///
    /// # Arguments
    ///
    /// * `column`: The column (x-coordinate) of the checked cell. Must be in
    /// the range `[0, size[`.
    /// * `row`: The row (y-coordinate) of the checked cell. Must be in the
    /// range `[0, size[`.
    /// * `number`: The number to check whether it is in the specified cell. If
    /// it is *not* in the range `[1, size]`, `false` will always be returned.
    ///
    /// # Errors
    ///
    /// If either `column` or `row` are not in the specified range. In that
    /// case, `SudokuError::OutOfBounds` is returned.
    pub fn has_number(&self, column: usize, row: usize, number: usize)
            -> SudokuResult<bool> {
        if let Some(content) = self.get_cell(column, row)? {
            Ok(number == content)
        }
        else {
            Ok(false)
        }
    }

    /// Sets the content of the cell at the specified position to the given
    /// number. If the cell was not empty, the old number will be overwritten.
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
    pub fn set_cell(&mut self, column: usize, row: usize, number: usize)
            -> SudokuResult<()> {
        let size = self.size();

        if column >= size || row >= size {
            return Err(SudokuError::OutOfBounds);
        }

        if number == 0 || number > size {
            return Err(SudokuError::InvalidNumber);
        }

        let index = index(column, row, size);
        self.cells[index] = Some(number);
        Ok(())
    }

    /// Clears the content of the cell at the specified position, that is, if
    /// contains a number, that number is removed. If the cell is already
    /// empty, it will be left that way.
    ///
    /// # Arguments
    ///
    /// * `column`: The column (x-coordinate) of the cleared cell. Must be in
    /// the range `[0, size[`.
    /// * `row`: The row (y-coordinate) of the cleared cell. Must be in the
    /// range `[0, size[`.
    ///
    /// # Errors
    ///
    /// If either `column` or `row` are not in the specified range. In that
    /// case, `SudokuError::OutOfBounds` is returned.
    pub fn clear_cell(&mut self, column: usize, row: usize)
            -> SudokuResult<()> {
        let size = self.size();

        if column >= size || row >= size {
            return Err(SudokuError::OutOfBounds);
        }
        
        let index = index(column, row, size);
        self.cells[index] = None;
        Ok(())
    }

    fn verify_dimensions(&self, other: &SudokuGrid) -> SudokuResult<()> {
        if self.block_width != other.block_width ||
                self.block_height != other.block_height {
            Err(SudokuError::InvalidDimensions)
        }
        else {
            Ok(())
        }
    }

    /// Assigns the content of another grid to this one, i.e., changes the
    /// cells in this grid to the state in `other`. The other grid must have
    /// the same dimensions as this one.
    ///
    /// # Errors
    ///
    /// If the dimensions are not the same. In that case,
    /// `SudokuError::InvalidDimensions` is returned.
    pub fn assign(&mut self, other: &SudokuGrid) -> SudokuResult<()> {
        self.verify_dimensions(other)?;
        self.cells.copy_from_slice(&other.cells);
        Ok(())
    }

    /// Counts the number of clues given by this grid. This is the number of
    /// non-empty cells. While on average Sudoku with less clues are harder,
    /// this is *not* a reliable measure of difficulty.
    pub fn count_clues(&self) -> usize {
        let size = self.size();
        let mut clues = 0usize;

        for row in 0..size {
            for column in 0..size {
                if let Some(_) = self.get_cell(column, row).unwrap() {
                    clues += 1;
                }
            }
        }

        clues
    }

    /// Indicates whether this grid is full, i.e. every cell is filled with a
    /// number. In this case, [SudokuGrid::count_clues] returns the square of
    /// [SudokuGrid::size].
    pub fn is_full(&self) -> bool {
        !self.cells.iter().any(|c| c == &None)
    }

    /// Indicates whether this grid is empty, i.e. no cell is filled with a
    /// number. In this case, [SudokuGrid::count_clues] returns 0.
    pub fn is_empty(&self) -> bool {
        self.cells.iter().all(|c| c == &None)
    }

    /// Indicates whether this grid configuration is a subset of another one.
    /// That is, all cells filled in this grid with some number must be filled
    /// in `other` with the same number. If this condition is met, `true` is
    /// returned, and `false` otherwise.
    ///
    /// # Errors
    ///
    /// If the dimensions of this and the `other` grid are not the same. In
    /// that case, `SudokuError::InvalidDimensions` is returned.
    pub fn is_subset(&self, other: &SudokuGrid) -> SudokuResult<bool> {
        self.verify_dimensions(other)?;
        Ok(self.cells.iter()
            .zip(other.cells.iter())
            .all(|(self_cell, other_cell)| {
                match self_cell {
                    Some(self_number) =>
                        match other_cell {
                            Some(other_number) => self_number == other_number,
                            None => false
                        },
                    None => true
                }
            }))
    }

    /// Indicates whether this grid configuration is a superset of another one.
    /// That is, all cells filled in the `other `grid with some number must be
    /// filled in this one with the same number. If this condition is met,
    /// `true` is returned, and `false` otherwise.
    ///
    /// # Errors
    ///
    /// If the dimensions of this and the `other` grid are not the same. In
    /// that case, `SudokuError::InvalidDimensions` is returned.
    pub fn is_superset(&self, other: &SudokuGrid) -> SudokuResult<bool> {
        other.is_subset(self)
    }

    /// Gets a reference to the vector which holds the cells. They are in
    /// left-to-right, top-to-bottom order, where rows are together.
    pub fn cells(&self) -> &Vec<Option<usize>> {
        &self.cells
    }

    /// Gets a mutable reference to the vector which holds the cells. They are
    /// in left-to-right, top-to-bottom order, where rows are together.
    pub fn cells_mut(&mut self) -> &mut Vec<Option<usize>> {
        &mut self.cells
    }
}

/// A Sudoku represents a grid of numbers with an associated constraint. The
/// numbers may or may not fulfill the constraint, but there is a method to
/// check it.
///
/// There is no guarantee  that the Sudoku is uniquely solveable or even
/// solveable at all, however there are ways to check that (see the [solver]
/// module).
#[derive(Clone)]
pub struct Sudoku<C: Constraint + Clone> {
    grid: SudokuGrid,
    constraint: C
}

impl<C: Constraint + Clone> Sudoku<C> {

    /// Creates a new Sudoku with the provided constraint and an empty grid
    /// of the given dimensions. The total width and height of the grid will be
    /// equal to the product of `block_width` and `block_height`.
    ///
    /// # Arguments
    ///
    /// * `block_width`: The horizontal dimension of one sub-block of the grid.
    /// To ensure a square grid, this is also the number of blocks that compose
    /// the grid vertically. For an ordinary Sudoku grid, this is 3. Must be
    /// greater than 0.
    /// * `block_height`: The vertical dimension of one sub-block of the grid.
    /// To ensure a square grid, this is also the number of blocks that compose
    /// the grid horizontally. For an ordinary Sudoku grid, this is 3. Must be
    /// greater than 0.
    /// * `constraint`: The constraint which is checked by this Sudoku. Grid
    /// configurations which violate this constraint will be seen as invalid by
    /// [Sudoku::is_valid()].
    ///
    /// # Errors
    ///
    /// If `block_width` or `block_height` is invalid (zero).
    pub fn new_empty(block_width: usize, block_height: usize, constraint: C)
            -> SudokuResult<Sudoku<C>> {
        Ok(Sudoku {
            grid: SudokuGrid::new(block_width, block_height)?,
            constraint
        })
    }

    /// Creats a new Sudoku with the provided constraint and a given grid,
    /// which may already contain some numbers. Note that it is *not* checked
    /// whether the given grid fulfills the constraint - it is perfectly legal
    /// to create an invalid Sudoku here.
    ///
    /// # Arguments
    ///
    /// * `grid`: The initial [SudokuGrid] which contains the numbers with
    /// which the Sudoku is filled.
    /// * `constraint`: The constraint which is checked by this Sudoku. Grid
    /// configurations which violate this constraint will be seen as invalid by
    /// [Sudoku::is_valid]).
    pub fn new_with_grid(grid: SudokuGrid, constraint: C) -> Sudoku<C> {
        Sudoku {
            grid,
            constraint
        }
    }

    /// Parses the code into a [SudokuGrid] using [SudokuGrid::parse] and wraps
    /// the result in a Sudoku with the given constraint. Note that it is not
    /// required that the code matches the constraint. It is perfectly legal to
    /// parse an invalid Sudoku.
    ///
    /// # Arguments
    ///
    /// * `code`: The code that specifies the grid. See [SudokuGrid::parse] for
    /// a language specification.
    /// * `constraint`: The constraint which is checked by this Sudoku. Grid
    /// configurations which violate this constraint will be seen as invalid by
    /// [Sudoku::is_valid].
    ///
    /// # Errors
    ///
    /// If the parsing fails. See [SudokuGrid::parse] for further information.
    pub fn parse(code: &str, constraint: C) -> SudokuParseResult<Sudoku<C>> {
        Ok(Sudoku::new_with_grid(SudokuGrid::parse(code)?, constraint))
    }

    /// Gets a reference to the `SudokuGrid` of this Sudoku.
    pub fn grid(&self) -> &SudokuGrid {
        &self.grid
    }

    /// Gets a mutable reference to the `SudokuGrid` of this Sudoku.
    pub fn grid_mut(&mut self) -> &mut SudokuGrid {
        &mut self.grid
    }

    /// Gets a reference to the `Constraint` of this Sudoku.
    pub fn constraint(&self) -> &C {
        &self.constraint
    }

    /// Indicates whether the entire grid matches the constraint.
    pub fn is_valid(&self) -> bool {
        self.constraint.check(&self.grid)
    }

    /// Indicates whether the cell at the given location matches the
    /// constraint. That is, if the specified cell violates the constraint,
    /// `false` is returned, and `true` otherwise.
    ///
    /// # Arguments
    ///
    /// * `column`: The column (x-coordinate) of the checked cell. Must be in
    /// the range `[0, size[`.
    /// * `row`: The row (y-coordinate) of the checked cell. Must be in the
    /// range `[0, size[`.
    pub fn is_valid_cell(&self, column: usize, row: usize)
            -> SudokuResult<bool> {
        let size = self.grid.size();

        if column >= size || row >= size {
            Err(SudokuError::OutOfBounds)
        }
        else {
            Ok(self.constraint.check_cell(&self.grid, column, row))
        }
    }

    /// Indicates whether the given number would be valid in the cell at the
    /// given location. That is, if the number violated the constraint, `false`
    /// is returned, and `true` otherwise.
    ///
    /// # Arguments
    ///
    /// * `column`: The column (x-coordinate) of the checked cell. Must be in
    /// the range `[0, size[`.
    /// * `row`: The row (y-coordinate) of the checked cell. Must be in the
    /// range `[0, size[`.
    /// * `number`: The number to check whether it is valid in the given cell.
    ///
    /// # Errors
    ///
    /// * `SudokuError::OutOfBounds` If either `column` or `row` are not in the
    /// specified range.
    /// * `SudokuError::InvalidNumber` If `number` is not in the specified
    /// range.
    pub fn is_valid_number(&self, column: usize, row: usize, number: usize)
            -> SudokuResult<bool> {
        let size = self.grid.size();

        if column >= size || row >= size {
            Err(SudokuError::OutOfBounds)
        }
        else if number == 0 || number > size {
            Err(SudokuError::InvalidNumber)
        }
        else {
            Ok(self.constraint.check_number(&self.grid, column, row, number))
        }
    }

    /// Indicates whether the given [SudokuGrid] is a valid solution to this
    /// puzzle. That is the case if all digits from this Sudoku can be found in
    /// the `solution`, it matches the constraint of this Sudoku, and it is
    /// full.
    ///
    /// # Errors
    ///
    /// If the dimensions of this Sudoku's grid and the `solution` grid are not
    /// the same. In that case, `SudokuError::InvalidDimensions` is returned.
    pub fn is_valid_solution(&self, solution: &SudokuGrid)
            -> SudokuResult<bool> {
        Ok(self.grid.is_subset(solution)? &&
            self.constraint.check(solution) &&
            solution.is_full())
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::constraint::DefaultConstraint;

    #[test]
    fn parse_ok() {
        let grid_res = SudokuGrid::parse("2x2; 1,,,2, ,3,,4, ,2,,, 3,,,");

        if let Ok(grid) = grid_res {
            assert_eq!(2, grid.block_width());
            assert_eq!(2, grid.block_height());
            assert_eq!(Some(1), grid.get_cell(0, 0).unwrap());
            assert_eq!(None, grid.get_cell(1, 0).unwrap());
            assert_eq!(None, grid.get_cell(2, 0).unwrap());
            assert_eq!(Some(2), grid.get_cell(3, 0).unwrap());
            assert_eq!(None, grid.get_cell(0, 1).unwrap());
            assert_eq!(Some(3), grid.get_cell(1, 1).unwrap());
            assert_eq!(None, grid.get_cell(2, 1).unwrap());
            assert_eq!(Some(4), grid.get_cell(3, 1).unwrap());
            assert_eq!(None, grid.get_cell(0, 2).unwrap());
            assert_eq!(Some(2), grid.get_cell(1, 2).unwrap());
            assert_eq!(None, grid.get_cell(2, 2).unwrap());
            assert_eq!(None, grid.get_cell(3, 2).unwrap());
            assert_eq!(Some(3), grid.get_cell(0, 3).unwrap());
            assert_eq!(None, grid.get_cell(1, 3).unwrap());
            assert_eq!(None, grid.get_cell(2, 3).unwrap());
            assert_eq!(None, grid.get_cell(3, 3).unwrap());
        }
        else {
            panic!("Parsing valid grid failed.");
        }
    }

    #[test]
    fn parse_malformed_dimensions() {
        assert_eq!(Err(SudokuParseError::MalformedDimensions),
            SudokuGrid::parse("2x2x2;,,,,,,,,,,,,,,,"));
    }

    #[test]
    fn parse_invalid_dimensions() {
        assert_eq!(Err(SudokuParseError::InvalidDimensions),
            SudokuGrid::parse("2x0;,"));
    }

    #[test]
    fn parse_wrong_number_of_parts() {
        assert_eq!(Err(SudokuParseError::WrongNumberOfParts),
            SudokuGrid::parse("2x2;,,,,,,,,,,,,,,,;whatever"));
    }

    #[test]
    fn parse_number_format_error() {
        assert_eq!(Err(SudokuParseError::NumberFormatError),
            SudokuGrid::parse("2x#;,"));
    }

    #[test]
    fn parse_invalid_number() {
        assert_eq!(Err(SudokuParseError::InvalidNumber),
            SudokuGrid::parse("2x2;,,,4,,,5,,,,,,,,,"));
    }

    #[test]
    fn parse_wrong_number_of_cells() {
        assert_eq!(Err(SudokuParseError::WrongNumberOfCells),
            SudokuGrid::parse("2x2;1,2,3,4,1,2,3,4,1,2,3,4,1,2,3"));
        assert_eq!(Err(SudokuParseError::WrongNumberOfCells),
            SudokuGrid::parse("2x2;1,2,3,4,1,2,3,4,1,2,3,4,1,2,3,4,1"));
    }

    #[test]
    fn to_parseable_string() {
        let mut grid = SudokuGrid::new(2, 2).unwrap();

        assert_eq!("2x2;,,,,,,,,,,,,,,,", grid.to_parseable_string().as_str());

        grid.set_cell(0, 0, 1).unwrap();
        grid.set_cell(1, 1, 2).unwrap();
        grid.set_cell(2, 2, 3).unwrap();
        grid.set_cell(3, 3, 4).unwrap();

        assert_eq!("2x2;1,,,,,2,,,,,3,,,,,4",
            grid.to_parseable_string().as_str());

        let grid = SudokuGrid::new(4, 1).unwrap();

        assert_eq!("4x1;,,,,,,,,,,,,,,,", grid.to_parseable_string().as_str());
    }

    #[test]
    fn size() {
        let grid1x1 = SudokuGrid::new(1, 1).unwrap();
        let grid3x2 = SudokuGrid::new(3, 2).unwrap();
        let grid3x4 = SudokuGrid::new(3, 4).unwrap();
        assert_eq!(1, grid1x1.size());
        assert_eq!(6, grid3x2.size());
        assert_eq!(12, grid3x4.size());
    }

    #[test]
    fn count_clues_and_empty_and_full() {
        let empty = SudokuGrid::parse("2x2;,,,,,,,,,,,,,,,").unwrap();
        let partial = SudokuGrid::parse("2x2;1,,3,2,4,,,,,,,,,,1,").unwrap();
        let full = SudokuGrid::parse("2x2;2,3,4,1,1,4,2,3,4,1,3,2,3,2,1,4")
            .unwrap();

        assert_eq!(0, empty.count_clues());
        assert_eq!(5, partial.count_clues());
        assert_eq!(16, full.count_clues());

        assert!(empty.is_empty());
        assert!(!partial.is_empty());
        assert!(!full.is_empty());

        assert!(!empty.is_full());
        assert!(!partial.is_full());
        assert!(full.is_full());
    }

    fn assert_subset_relation(a: &SudokuGrid, b: &SudokuGrid, a_subset_b: bool,
            b_subset_a: bool) {
        assert!(a.is_subset(b).unwrap() == a_subset_b);
        assert!(a.is_superset(b).unwrap() == b_subset_a);
        assert!(b.is_subset(a).unwrap() == b_subset_a);
        assert!(b.is_superset(a).unwrap() == a_subset_b);
    }

    fn assert_true_subset(a: &SudokuGrid, b: &SudokuGrid) {
        assert_subset_relation(a, b, true, false)
    }

    fn assert_equal_set(a: &SudokuGrid, b: &SudokuGrid) {
        assert_subset_relation(a, b, true, true)
    }

    fn assert_unrelated_set(a: &SudokuGrid, b: &SudokuGrid) {
        assert_subset_relation(a, b, false, false)
    }

    #[test]
    fn empty_is_subset() {
        let empty = SudokuGrid::new(2, 2).unwrap();
        let non_empty = SudokuGrid::parse("2x2;1,,,,,,,,,,,,,,,").unwrap();
        let full = SudokuGrid::parse("2x2;1,2,3,4,3,4,1,2,2,3,1,4,4,1,3,2")
            .unwrap();

        assert_equal_set(&empty, &empty);
        assert_true_subset(&empty, &non_empty);
        assert_true_subset(&empty, &full);
    }

    #[test]
    fn equal_grids_subsets() {
        let g = SudokuGrid::parse("2x2;1,,3,,2,,,,4,,4,3,,,,2").unwrap();
        assert_equal_set(&g, &g);
    }

    #[test]
    fn true_subset() {
        let g1 = SudokuGrid::parse("2x2;1,,3,,2,,,,4,,4,3,,,,2").unwrap();
        let g2 = SudokuGrid::parse("2x2;1,2,3,,2,,3,,4,,4,3,,,1,2").unwrap();
        assert_true_subset(&g1, &g2);
    }

    #[test]
    fn unrelated_grids_not_subsets() {
        // g1 and g2 differ in the third digit (3 in g1, 4 in g2)
        let g1 = SudokuGrid::parse("2x2;1,,3,,2,,,,4,,4,3,,,,2").unwrap();
        let g2 = SudokuGrid::parse("2x2;1,2,4,,2,,3,,4,,4,3,,,1,2").unwrap();
        assert_unrelated_set(&g1, &g2);
    }

    fn solution_example_sudoku() -> Sudoku<DefaultConstraint> {
        Sudoku::parse("2x2;\
            2, , , ,\
             , ,3, ,\
             , , ,4,\
             ,2, , ", DefaultConstraint).unwrap()
    }

    #[test]
    fn solution_not_full() {
        let sudoku = solution_example_sudoku();
        let solution = SudokuGrid::parse("2x2;\
            2,3,4,1,\
            1,4,3, ,\
            3,1,2,4,\
            4,2,1,3").unwrap();
        assert!(!sudoku.is_valid_solution(&solution).unwrap());
    }

    #[test]
    fn solution_not_superset() {
        let sudoku = solution_example_sudoku();
        let solution = SudokuGrid::parse("2x2;\
            2,3,4,1,\
            1,4,3,2,\
            3,2,1,4,\
            4,1,2,3").unwrap();
        assert!(!sudoku.is_valid_solution(&solution).unwrap());
    }

    #[test]
    fn solution_violates_constraint() {
        let sudoku = solution_example_sudoku();
        let solution = SudokuGrid::parse("2x2;\
            2,3,4,1,\
            1,3,3,2,\
            3,1,2,4,\
            4,2,1,3").unwrap();
        assert!(!sudoku.is_valid_solution(&solution).unwrap());
    }

    #[test]
    fn solution_correct() {
        let sudoku = solution_example_sudoku();
        let solution = SudokuGrid::parse("2x2;\
            2,3,4,1,\
            1,4,3,2,\
            3,1,2,4,\
            4,2,1,3").unwrap();
        assert!(sudoku.is_valid_solution(&solution).unwrap());
    }
}
