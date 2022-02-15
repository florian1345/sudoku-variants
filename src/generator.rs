//! This module contains logic for generating random Sudoku.
//!
//! Generation of Sudoku puzzles is done by first generating a full grid with a
//! [Generator] and then removing some clues using a [Reducer].

use crate::{Sudoku, SudokuGrid};
use crate::constraint::Constraint;
use crate::error::{SudokuError, SudokuResult};
use crate::solver::{BacktrackingSolver, Solution, Solver};

use rand::Rng;
use rand::rngs::ThreadRng;

use rand_distr::Normal;

use std::f64::consts;

/// A generator randomly generates a full [Sudoku], that is, a Sudoku with no
/// missing digits. It uses a random number generator to decide the content.
/// For most cases, sensible defaults are provided by [Generator::new_default].
pub struct Generator<R: Rng> {
    rng: R
}

impl Generator<ThreadRng> {

    /// Creates a new generator that uses a [ThreadRng] to generate the random
    /// digits.
    pub fn new_default() -> Generator<ThreadRng> {
        Generator::new(rand::thread_rng())
    }
}

pub(crate) fn shuffle<T>(rng: &mut impl Rng, values: impl Iterator<Item = T>)
        -> Vec<T> {
    let mut vec: Vec<T> = values.collect();
    let len = vec.len();

    for i in 0..(len - 1) {
        let j = rng.gen_range(i..len);
        vec.swap(i, j);
    }

    vec
}

impl<R: Rng> Generator<R> {

    /// Creates a new generator that uses the given random number generator to
    /// generate random digits.
    pub fn new(rng: R) -> Generator<R> {
        Generator {
            rng
        }
    }

    fn fill_rec<C: Constraint + Clone>(&mut self, sudoku: &mut Sudoku<C>,
            column: usize, row: usize) -> bool {
        let size = sudoku.grid().size();

        if row == size {
            return true;
        }

        let next_column = (column + 1) % size;
        let next_row =
            if next_column == 0 { row + 1 } else { row };

        if sudoku.grid().get_cell(column, row).unwrap().is_some() {
            return self.fill_rec(sudoku, next_column, next_row);
        }

        for number in shuffle(&mut self.rng, 1..=size) {
            if sudoku.is_valid_number(column, row, number).unwrap() {
                sudoku.grid_mut().set_cell(column, row, number).unwrap();

                if self.fill_rec(sudoku, next_column, next_row) {
                    return true;
                }

                sudoku.grid_mut().clear_cell(column, row).unwrap();
            }
        }

        false
    }

    /// Fills the given [Sudoku] with random digits that satisfy its constraint
    /// and match all already present digits. If it is not possible, an error
    /// will be returned.
    ///
    /// If no error is returned, it is guaranteed that [Sudoku::is_valid] on
    /// `sudoku` result returns `true` after this operation. Otherwise, it
    /// remains unchanged.
    ///
    /// # Arguments
    ///
    /// * `sudoku`: The Sudoku to fill with random digits.
    ///
    /// # Errors
    ///
    /// * `SudokuError::UnsatisfiableConstraint` If there are no sets of digits
    /// that can be entered into the Sudoku that match its constraint without
    /// changing digits already present.
    pub fn fill<C>(&mut self, sudoku: &mut Sudoku<C>) -> SudokuResult<()>
    where
        C: Constraint + Clone
    {
        if self.fill_rec(sudoku, 0, 0) {
            Ok(())
        }
        else {
            Err(SudokuError::UnsatisfiableConstraint)
        }
    }

    /// Generates a new random [Sudoku] with all digits that matches the given
    /// parameters. If it is not possible, an error will be returned.
    ///
    /// It is guaranteed that [Sudoku::is_valid] on the result returns `true`.
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
    /// * `constraint`: The constraint which will be matched by the generated
    /// Sudoku, which will also be contained and checked by the output Sudoku.
    ///
    /// # Errors
    ///
    /// * `SudokuError::InvalidDimensions` If `block_width` or `block_height`
    /// is invalid (zero).
    /// * `SudokuError::UnsatisfiableConstraint` If there are no grids with the
    /// given dimensions that match the provided `constraint`.
    pub fn generate<C>(&mut self, block_width: usize, block_height: usize,
        constraint: C) -> SudokuResult<Sudoku<C>>
    where
        C: Constraint + Clone
    {
        let mut sudoku =
            Sudoku::new_empty(block_width, block_height, constraint)?;
        self.fill(&mut sudoku)?;
        Ok(sudoku)
    }
}

/// A trait for types which can prioritize the order in which Sudoku reductions
/// of type `R` shall be applied to a Sudoku to reduce. Note that there is some
/// random element to the ordering (see [ReductionPrioritizer::rough_priority]
/// for details on the mathematics). It is blanket-implemented for all types
/// implementing `Fn(&R) -> f64`.
pub trait ReductionPrioritizer<R> {

    /// Determines the approximate priority of the given reduction. Lower
    /// numbers indicate reductions that are applied first. When determining
    /// the order of two reductions, each of these scores is added to a
    /// normally distributed random number with a standard deviation of
    /// `1 / sqrt(2)`. The reduction with the lower sum will be applied first.
    ///
    /// In other words, if the difference between the scores of two reductions
    /// `a` and `b` is `score(a) - score(b) = x`, then the probability that `a`
    /// is applied _after_ `b` is equivalent to the probability a normally
    /// distributed random number is _below_ the `x`-sigma interval.
    ///
    /// For simple priorization where all reductions of some type are applied
    /// first, separate them by differences of at least 10 to ensure a
    /// negligible probability of overlap.
    ///
    /// This method must _always_ return finite numbers or inifinities.
    ///
    /// # Arguments
    ///
    /// * `reduction`: A reference to the reduction of which to get the rough
    /// priority score.
    fn rough_priority(&mut self, reduction: &R) -> f64;
}

struct EqualPrioritizer;

impl<R> ReductionPrioritizer<R> for EqualPrioritizer {
    fn rough_priority(&mut self, _: &R) -> f64 {
        0.0
    }
}

impl<R, F: Fn(&R) -> f64> ReductionPrioritizer<R> for F {
    fn rough_priority(&mut self, reduction: &R) -> f64 {
        self(reduction)
    }
}

/// A reducer can be applied to the output of a [Generator] to remove numbers
/// from the grid as long as it is still uniquely solveable using the provided
/// [Solver]. This may be intentionally suboptimal to control the difficulty. A
/// random number generator decides which digits are removed.
///
/// [Reducer::new_default] will yield a reducer with the highest difficulty (a
/// perfect backtracking solver) and a [ThreadRng].
pub struct Reducer<S: Solver, R: Rng> {
    solver: S,
    rng: R
}

impl Reducer<BacktrackingSolver, ThreadRng> {

    /// Generates a new reducer with a [BacktrackingSolver] to check unique
    /// solveability and a [ThreadRng] to decide which digits are removed.
    pub fn new_default() -> Reducer<BacktrackingSolver, ThreadRng> {
        Reducer::new(BacktrackingSolver, rand::thread_rng())
    }
}

/// An enumeration of the different reductions that can be applied to a Sudoku.
/// `R` is the type of reduction of the Sudoku's constraint. See
/// [Constraint::Reduction].
pub enum Reduction<R> {

    /// Remove a digit in a specified cell. This is applicable to any Sudoku.
    RemoveDigit {

        /// The column of the cell whose digit to remove.
        column: usize,

        /// The row of the cell whose digit to remove.
        row: usize
    },

    /// Apply a reduction to the [Constraint] of the Sudoku.
    ReduceConstraint {

        /// The reduction as emitted by [Constraint::list_reductions].
        reduction: R
    }
}

impl<R> Reduction<R> {
    fn apply<S, C>(&self, sudoku: &mut Sudoku<C>, solution: &SudokuGrid,
        solver: &S)
    where
        S: Solver,
        C: Constraint<Reduction = R> + Clone + 'static
    {
        match self {
            Reduction::RemoveDigit { column, row } => {
                let number = sudoku.grid().get_cell(*column, *row).unwrap()
                    .unwrap();
                sudoku.grid_mut().clear_cell(*column, *row).unwrap();

                if let Solution::Unique(_) = solver.solve(sudoku) { }
                else {
                    sudoku.grid_mut().set_cell(*column, *row, number).unwrap();
                }
            },
            Reduction::ReduceConstraint { reduction: r} => {
                let constraint = sudoku.constraint_mut();
                let reduce_res = constraint.reduce(solution, r);
                
                if let Ok(revert_info) = reduce_res {
                    if let Solution::Unique(_) = solver.solve(sudoku) { }
                    else {
                        let constraint = sudoku.constraint_mut();
                        constraint.revert(solution, r, revert_info);
                    }
                }
            }
        }
    }
}

fn reductions<R, C>(sudoku: &Sudoku<C>) -> impl Iterator<Item = Reduction<R>>
where
    C: Constraint<Reduction = R> + Clone
{
    let size = sudoku.grid().size();
    let digit_reductions = (0..size)
        .flat_map(move |column| (0..size)
            .map(move |row| Reduction::RemoveDigit {
                column,
                row
            }));
    let constraint_reductions = sudoku.constraint()
        .list_reductions(sudoku.grid())
        .into_iter()
        .map(|r| Reduction::ReduceConstraint {
            reduction: r
        });
    digit_reductions.chain(constraint_reductions)
}

fn prioritize<RED, P, RNG>(reduction: &RED, prioritizer: &mut P, rng: &mut RNG)
    -> f64
where
    P: ReductionPrioritizer<RED>,
    RNG: Rng
{
    let distr = Normal::new(0.0, consts::FRAC_1_SQRT_2).unwrap();
    prioritizer.rough_priority(reduction) + rng.sample(distr)
}

impl<S: Solver, R: Rng> Reducer<S, R> {

    /// Creates a new reducer with the given solver and random number gnerator.
    ///
    /// # Arguments
    ///
    /// * `solver`: A [Solver] to be used to check whether a reduced Sudoku is
    /// still uniquely solveable. This controls the difficulty by specifying a
    /// strategy that must be able to solve the Sudoku.
    /// * `rng`: A random number generator that decides which digits are
    /// removed.
    pub fn new(solver: S, rng: R) -> Reducer<S, R> {
        Reducer {
            solver,
            rng
        }
    }

    /// Reduces the given Sudoku as much as possible. That is, applies random
    /// reductions (removing digits or reducing a reducible constraint) until
    /// all remaining ones would cause the solver wrapped in this reducer to be
    /// unable to solve the Sudoku. All changes are done to the given mutable
    /// Sudoku.
    ///
    /// It is expected that the given `sudoku` is full, i.e. contains no empty
    /// cells.
    ///
    /// The order of reductions is fully random.
    pub fn reduce<C>(&mut self, sudoku: &mut Sudoku<C>)
    where
        C: Constraint + Clone + 'static
    {
        self.reduce_with_priority(sudoku, EqualPrioritizer)
    }

    /// Reduces the given Sudoku as much as possible. That is, applies random
    /// reductions (removing digits or reducing a reducible constraint) until
    /// all remaining ones would cause the solver wrapped in this reducer to be
    /// unable to solve the Sudoku. All changes are done to the given mutable
    /// Sudoku.
    ///
    /// It is expected that the given `sudoku` is full, i.e. contains no empty
    /// cells.
    ///
    /// The order of reductions is influenced by the given `prioritizer`. See
    /// the documentation of [ReductionPrioritizer].
    pub fn reduce_with_priority<C, P>(&mut self, sudoku: &mut Sudoku<C>,
        mut prioritizer: P)
    where
        C: Constraint + Clone + 'static,
        P: ReductionPrioritizer<Reduction<C::Reduction>>
    {
        let mut reductions = reductions(sudoku)
            .map(|r| (prioritize(&r, &mut prioritizer, &mut self.rng), r))
            .collect::<Vec<_>>();
        reductions.sort_by(|(p1, _), (p2, _)| p1.partial_cmp(p2).unwrap());
        let solution = sudoku.grid().clone();

        for (_, reduction) in reductions {
            reduction.apply(sudoku, &solution, &self.solver);
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::constraint::{
        CompositeConstraint,
        DefaultConstraint,
        Group,
        KillerConstraint,
        ReductionError
    };
    use crate::solver::strategy::{
        CompositeStrategy,
        NakedSingleStrategy,
        OnlyCellStrategy
    };
    use crate::solver::strategy::solvers::StrategicBacktrackingSolver;

    const DEFAULT_BLOCK_WIDTH: usize = 3;
    const DEFAULT_BLOCK_HEIGHT: usize = 3;

    fn generate_default() -> Sudoku<DefaultConstraint> {
        let mut generator = Generator::new_default();
        generator.generate(DEFAULT_BLOCK_WIDTH, DEFAULT_BLOCK_HEIGHT,
            DefaultConstraint).unwrap()
    }

    fn reduce_default() -> Sudoku<DefaultConstraint> {
        let mut sudoku = generate_default();
        let mut reducer = Reducer::new_default();
        reducer.reduce(&mut sudoku);
        sudoku
    }

    #[test]
    fn shuffling_uniformly_distributed() {
        // 18000 experiments, 6 options (3!), so if uniformly distributed:
        // p = 1/6, my = 3000, sigma = sqrt(18000 * 1/6 * 5/6) = 50
        // with a probability of the amount being in the range [2600, 3400]
        // is more than 99,9999999999999 %.

        let mut counts = [0; 6];
        let mut rng = rand::thread_rng();
        
        for _ in 0..18000 {
            let result = shuffle(&mut rng, 1..=3);

            if result == vec![1, 2, 3] {
                counts[0] += 1;
            }
            else if result == vec![1, 3, 2] {
                counts[1] += 1;
            }
            else if result == vec![2, 1, 3] {
                counts[2] += 1;
            }
            else if result == vec![2, 3, 1] {
                counts[3] += 1;
            }
            else if result == vec![3, 1, 2] {
                counts[4] += 1;
            }
            else if result == vec![3, 2, 1] {
                counts[5] += 1;
            }
        }

        for count in counts.iter() {
            assert!(*count >= 2600 && *count <= 3400,
                "Count is not in range [2600, 3400].");
        }
    }

    #[test]
    fn filled_sudoku_keeps_digits() {
        let mut sudoku = Sudoku::parse("2x2;\
             ,1, ,3,\
            2, , , ,\
             ,4, , ,\
             , , , ", DefaultConstraint).unwrap();
        let mut generator = Generator::new_default();
        generator.fill(&mut sudoku).unwrap();

        assert!(sudoku.is_valid());
        assert!(sudoku.grid().is_full());
        assert_eq!(Some(1), sudoku.grid().get_cell(1, 0).unwrap());
        assert_eq!(Some(3), sudoku.grid().get_cell(3, 0).unwrap());
        assert_eq!(Some(2), sudoku.grid().get_cell(0, 1).unwrap());
        assert_eq!(Some(4), sudoku.grid().get_cell(1, 2).unwrap());
    }

    #[test]
    fn unsatisfiable_filled_sudoku_is_not_changed() {
        let mut sudoku = Sudoku::parse("2x2;\
             ,1, ,3,\
            2, , , ,\
             , , , ,\
             , ,2, ", DefaultConstraint).unwrap();
        let mut generator = Generator::new_default();
        let grid_before = sudoku.grid().clone();
        let result = generator.fill(&mut sudoku);

        assert_eq!(Err(SudokuError::UnsatisfiableConstraint), result);
        assert_eq!(&grid_before, sudoku.grid());
    }

    #[test]
    fn generated_sudoku_valid() {
        let sudoku = generate_default();
        assert!(sudoku.is_valid(), "Generated Sudoku not valid.");
    }

    #[test]
    fn generated_sudoku_full() {
        let sudoku = generate_default();
        let size = DEFAULT_BLOCK_WIDTH * DEFAULT_BLOCK_HEIGHT;
        assert_eq!(size * size, sudoku.grid().count_clues(),
            "Generated Sudoku is not full.");
    }

    #[test]
    fn reduced_sudoku_valid_and_not_full() {
        let sudoku = reduce_default();
        let size = DEFAULT_BLOCK_WIDTH * DEFAULT_BLOCK_HEIGHT;
        assert!(sudoku.is_valid(), "Reduced Sudoku not valid.");
        assert!(sudoku.grid().count_clues() <= size * (size - 1),
            "Reduced Sudoku has too many clues.");
    }

    #[test]
    fn reduced_sudoku_uniquely_solveable() {
        let sudoku = reduce_default();
        let solver = BacktrackingSolver;
        let solution = solver.solve(&sudoku);

        if let Solution::Unique(_) = solution { }
        else {
            panic!("Reduced Sudoku not uniquely solveable.")
        }
    }

    fn fast_solver() -> impl Solver {
        let strategy =
            CompositeStrategy::new(NakedSingleStrategy, OnlyCellStrategy);
        StrategicBacktrackingSolver::new(strategy)
    }

    #[test]
    fn reduced_killer_sudoku_uniquely_solveable() {
        let mut generator = Generator::new_default();
        let sudoku = generator.generate(3, 3,
            DefaultConstraint).unwrap();
        let solution = sudoku.grid();
        let killer_constraint =
            KillerConstraint::new_singletons(solution);
        let mut sudoku = Sudoku::new_with_grid(solution.clone(),
            CompositeConstraint::new(DefaultConstraint, killer_constraint));
        let mut reducer = Reducer::new(fast_solver(), rand::thread_rng());
        reducer.reduce(&mut sudoku);
        let solver = fast_solver();

        assert!(sudoku.constraint().second().cages().len() < 81);
        assert_eq!(Solution::Unique(solution.clone()), solver.solve(&sudoku));
    }

    /// This is a deliberately bad solver which only checks differet options
    /// for the top-left cell of each Sudoku. If any other cells are missing,
    /// or there are multiple options for the top-left cell, the solver returns
    /// `Solution::Ambiguous`.
    struct TopLeftSolver;

    impl Solver for TopLeftSolver {
        fn solve<C>(&self, sudoku: &Sudoku<C>) -> Solution
        where
            C: Constraint + Clone + 'static
        {
            let size = sudoku.grid().size();
            let cells = size * size;
            let clues = sudoku.grid().count_clues();

            if clues == cells {
                // Sudoku is full anyway
                return Solution::Unique(sudoku.grid().clone());
            }
            else if clues < cells - 1 {
                // Sudoku missing other digit anyway
                return Solution::Ambiguous;
            }

            if let Some(_) = sudoku.grid().get_cell(0, 0).unwrap() {
                // Somewhere else a cell must be missing
                Solution::Ambiguous
            }
            else {
                let mut number = None;

                for i in 1..=size {
                    if sudoku.is_valid_number(0, 0, i).unwrap() {
                        if number == None {
                            number = Some(i);
                        }
                        else {
                            // Multiple options for top-left cell
                            return Solution::Ambiguous;
                        }
                    }
                }

                if let Some(number) = number {
                    let mut result_grid = sudoku.grid().clone();
                    result_grid.set_cell(0, 0, number).unwrap();
                    Solution::Unique(result_grid)
                }
                else {
                    Solution::Impossible
                }
            }
        }
    }

    #[test]
    fn reduced_sudoku_solveable_by_solver() {
        let mut sudoku = generate_default();
        let mut reducer = Reducer::new(TopLeftSolver, rand::thread_rng());
        reducer.reduce(&mut sudoku);

        let size = DEFAULT_BLOCK_WIDTH * DEFAULT_BLOCK_HEIGHT;
        assert_eq!(size * size - 1, sudoku.grid().count_clues(),
            "Reduced Sudoku missing too many clues or not reduced at all.");
        assert_eq!(None, sudoku.grid().get_cell(0, 0).unwrap(),
            "Reduced Sudoku missing wrong clue.");
    }

    /// A constraint which may or may not encode the maximum sum of the digits
    /// on the main diagonal and the anti diagonal.
    #[derive(Clone)]
    struct DiagonalSumConstraint {
        main_sum: Option<usize>,
        anti_sum: Option<usize>
    }

    impl DiagonalSumConstraint {
        fn new(grid: &SudokuGrid) -> DiagonalSumConstraint {
            let main_sum = Diagonal::Main.get_sum(grid);
            let anti_sum = Diagonal::Anti.get_sum(grid);

            DiagonalSumConstraint {
                main_sum: Some(main_sum),
                anti_sum: Some(anti_sum)
            }
        }
    }

    enum Diagonal {
        Main,
        Anti
    }

    fn diagonal_sum(grid: &SudokuGrid, row_computer: impl Fn(usize) -> usize)
            -> usize {
        let size = grid.size();
        let mut sum = 0usize;

        for i in 0..size {
            let row = row_computer(i);

            if let Some(n) = grid.get_cell(i, row).unwrap() {
                sum += n;
            }
        }

        sum
    }

    impl Diagonal {
        fn get_sum(&self, grid: &SudokuGrid) -> usize {
            match self {
                Diagonal::Main => diagonal_sum(grid, |i| i),
                Diagonal::Anti => {
                    let size = grid.size();
                    diagonal_sum(grid, |i| size - i - 1)
                }
            }
        }
    }

    impl Constraint for DiagonalSumConstraint {
        type Reduction = Diagonal;
        type RevertInfo = usize;

        fn check_number(&self, grid: &SudokuGrid, column: usize, row: usize, number: usize) -> bool {
            let size = grid.size();
            let content = grid.get_cell(column, row).unwrap().unwrap_or(0);

            if column == row {
                // cell is on main diagonal

                if let Some(main_sum) = self.main_sum {
                    let sum = Diagonal::Main.get_sum(grid) - content + number;

                    if sum > main_sum {
                        return false;
                    }
                }
            }

            if column == size - row - 1 {
                // cell is on anti diagonal

                if let Some(anti_sum) = self.anti_sum {
                    let sum = Diagonal::Anti.get_sum(grid) - content + number;

                    if sum > anti_sum {
                        return false;
                    }
                }
            }

            true
        }

        fn get_groups(&self, _: &SudokuGrid) -> Vec<Group> {
            Vec::new()
        }

        fn list_reductions(&self, _: &SudokuGrid) -> Vec<Diagonal> {
            let mut v = Vec::new();

            if self.main_sum.is_some() {
                v.push(Diagonal::Main);
            }

            if self.anti_sum.is_some() {
                v.push(Diagonal::Anti);
            }

            v
        }

        fn reduce(&mut self, _: &SudokuGrid, reduction: &Diagonal)
                -> Result<usize, ReductionError> {
            match reduction {
                Diagonal::Main =>
                    self.main_sum.take()
                        .ok_or(ReductionError::InvalidReduction),
                Diagonal::Anti =>
                    self.anti_sum.take()
                        .ok_or(ReductionError::InvalidReduction),
            }
        }

        fn revert(&mut self, _: &SudokuGrid, reduction: &Diagonal,
                sum: usize) {
            match reduction {
                Diagonal::Main =>
                    self.main_sum = Some(sum),
                Diagonal::Anti =>
                    self.anti_sum = Some(sum),
            }
        }
    }

    type DiagonalSumSudoku = Sudoku<CompositeConstraint<DefaultConstraint,
        DiagonalSumConstraint>>;

    fn generate_diagonal_sum_sudoku() -> DiagonalSumSudoku {
        let mut generator = Generator::new_default();
        let sudoku = generator.generate(2, 2, DefaultConstraint).unwrap();
        let constraint =
            CompositeConstraint::new(
                DefaultConstraint,
                DiagonalSumConstraint::new(sudoku.grid()));
        let mut sudoku =
            Sudoku::new_with_grid(sudoku.grid().clone(), constraint);
        let mut reducer = Reducer::new(BacktrackingSolver, rand::thread_rng());
        reducer.reduce(&mut sudoku);
        sudoku
    }

    fn assert_any_generated_diagonal_sum_sudoku_matches(limit: usize,
            predicate: impl Fn(DiagonalSumSudoku) -> bool) {
        for _ in 0..limit {
            if predicate(generate_diagonal_sum_sudoku()) {
                return;
            }
        }

        panic!("No genrated Sudoku matched predicate.");
    }

    #[test]
    fn constraint_is_reduced_maintaining_solveability() {
        let solver = BacktrackingSolver;

        assert_any_generated_diagonal_sum_sudoku_matches(100, |s| {
            let constraint = s.constraint().second();

            if constraint.main_sum.is_some() && constraint.anti_sum.is_some() {
                return false;
            }

            if let Solution::Unique(_) = solver.solve(&s) {
                return true;
            }

            panic!("Reduced Sudoku was not uniquely solveable.")
        })
    }

    #[test]
    fn constraint_is_relevant() {
        let solver = BacktrackingSolver;

        assert_any_generated_diagonal_sum_sudoku_matches(100, |mut s| {
            let constraint = s.constraint_mut().second_mut();

            if constraint.main_sum.is_none() && constraint.anti_sum.is_none() {
                return false;
            }

            constraint.main_sum.take();
            constraint.anti_sum.take();

            if let Solution::Unique(_) = solver.solve(&s) {
                panic!("Not all possible reductions were made.")
            }

            true
        })
    }

    #[test]
    fn reducer_respects_priorization() {
        let sudoku = Sudoku::parse("2x2;
            1,2,3,4,
            3,4,1,2,
            2,3,4,1,
            4,1,2,3", DefaultConstraint).unwrap();
        let mut reducer = Reducer::new_default();
        let mut top_left = 0;
        let mut bottom_right = 0;

        for _ in 0..1000 {
            let mut sudoku = sudoku.clone();
            reducer.reduce_with_priority(&mut sudoku,
                |r: &Reduction<()>| match r {
                    &Reduction::RemoveDigit { column, row } =>
                        column as f64 * 0.05 + row as f64 * 0.2,
                    _ => panic!(
                        "got constraint reduction for default constraint")
                });

            if sudoku.grid().get_cell(0, 0).unwrap().is_some() {
                top_left += 1;
            }

            if sudoku.grid().get_cell(3, 3).unwrap().is_some() {
                bottom_right += 1;
            }
        }

        // Assert some true separtion

        assert!(top_left > 0);
        assert!(bottom_right > 0);
        assert!(5 * top_left < 4 * bottom_right);
    }
}
