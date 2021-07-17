use crate::Sudoku;
use crate::constraint::{
    AdjacentConsecutiveConstraint,
    CompositeConstraint,
    Constraint,
    DefaultConstraint,
    DiagonalsConstraint,
    KillerConstraint,
    KingsMoveConstraint,
    KnightsMoveConstraint,
    SandwichConstraint,
    ThermoConstraint
};
use crate::generator::{Generator, Reducer};
use crate::solver::strategy::specific::{
    KillerCagePossibilitiesStrategy,
    SandwichBunPlacementStrategy,
    SandwichPossibilitiesStrategy,
    ThermometerFollowingStrategy
};
use crate::solver::strategy::{
    BoundedCellsBacktrackingStrategy,
    BoundedOptionsBacktrackingStrategy,
    CompositeStrategy,
    NakedSingleStrategy,
    OnlyCellStrategy,
    StrategicBacktrackingSolver,
    TupleStrategy
};
use crate::solver::{BacktrackingSolver, Solution, Solver};

const BLOCK_WIDTH: usize = 3;
const BLOCK_HEIGHT: usize = 2;
const ITERATIONS_PER_RUN: usize = 30;

fn run_consistency_test<C, G, S>(generator: G, solver: S, iterations: usize)
where
    C: Constraint + Clone + 'static,
    G: Fn() -> Sudoku<C>,
    S: Solver + Clone
{
    for _ in 0..iterations {
        let mut sudoku = generator();
        let expected = Solution::Unique(sudoku.grid().clone());
        let mut reducer = Reducer::new(solver.clone(), rand::thread_rng());
        reducer.reduce(&mut sudoku);
        assert!(!sudoku.grid().is_full());
        let solution = solver.solve(&sudoku);
        assert_eq!(expected, solution);
    }
}

fn generate_stateless<C>(block_width: usize, block_height: usize,
    constraint: C) -> Sudoku<C>
where
    C: Constraint + Clone + 'static
{
    let mut generator = Generator::new_default();
    generator.generate(block_width, block_height, constraint).unwrap()
}

fn generate_stateful<C1, C2, D>(block_width: usize, block_height: usize,
    stateless_constraint: C1, deriver: D)
    -> Sudoku<CompositeConstraint<C1, C2>>
where
    C1: Constraint + Clone + 'static,
    C2: Constraint + Clone + 'static,
    D: Fn(&Sudoku<C1>) -> C2
{
    let base_sudoku =
        generate_stateless(block_width, block_height, stateless_constraint);
    let stateful_constraint = deriver(&base_sudoku);
    let constraint =
        CompositeConstraint::new(
            base_sudoku.constraint().clone(),
            stateful_constraint);
    Sudoku::new_with_grid(base_sudoku.grid().clone(), constraint)
}

fn stateless_backtracking(constraint: impl Constraint + Clone + 'static) {
    run_consistency_test(|| generate_stateless(BLOCK_WIDTH, BLOCK_HEIGHT,
        constraint.clone()), BacktrackingSolver, ITERATIONS_PER_RUN)
}

#[test]
fn default_backtracking() {
    stateless_backtracking(DefaultConstraint)
}

#[test]
fn diagonals_backtracking() {
    stateless_backtracking(
        CompositeConstraint::new(DefaultConstraint, DiagonalsConstraint))
}

#[test]
fn knights_backtracking() {
    stateless_backtracking(
        CompositeConstraint::new(DefaultConstraint, KnightsMoveConstraint))
}

#[test]
fn kings_backtracking() {
    stateless_backtracking(
        CompositeConstraint::new(DefaultConstraint, KingsMoveConstraint))
}

#[test]
fn adjacent_consecutive_backtracking() {
    stateless_backtracking(
        CompositeConstraint::new(
            DefaultConstraint,
            AdjacentConsecutiveConstraint))
}

fn stateless_strategic_backtracking<C>(constraint: C)
where
    C: Constraint + Clone + 'static
{
    let continuation_strategy =
        CompositeStrategy::new(OnlyCellStrategy, NakedSingleStrategy);
    let solver = StrategicBacktrackingSolver::new(
        CompositeStrategy::new(
            CompositeStrategy::new(OnlyCellStrategy, NakedSingleStrategy),
            CompositeStrategy::new(
                TupleStrategy::new(|_| 3),
                CompositeStrategy::new(
                    BoundedOptionsBacktrackingStrategy::new(|_| 2,
                        |_| Some(3), continuation_strategy.clone()),
                    BoundedCellsBacktrackingStrategy::new(|_| 2,
                        |_| Some(3), continuation_strategy)
                )
            )
        )
    );
    run_consistency_test(|| generate_stateless(BLOCK_WIDTH, BLOCK_HEIGHT,
        constraint.clone()), solver, ITERATIONS_PER_RUN)
}

#[test]
fn default_strategic_backtracking() {
    stateless_strategic_backtracking(DefaultConstraint)
}

#[test]
fn diagonals_strategic_backtracking() {
    stateless_strategic_backtracking(
        CompositeConstraint::new(DefaultConstraint, DiagonalsConstraint))
}

#[test]
fn knights_strategic_backtracking() {
    stateless_strategic_backtracking(
        CompositeConstraint::new(DefaultConstraint, KnightsMoveConstraint))
}

#[test]
fn kings_strategic_backtracking() {
    stateless_strategic_backtracking(
        CompositeConstraint::new(DefaultConstraint, KingsMoveConstraint))
}

#[test]
fn adjacent_consecutive_strategic_backtracking() {
    stateless_strategic_backtracking(
        CompositeConstraint::new(
            DefaultConstraint,
            AdjacentConsecutiveConstraint))
}

#[test]
fn killer_strategic_backtracking() {
    let solver = StrategicBacktrackingSolver::new(
        CompositeStrategy::new(
            OnlyCellStrategy, 
            KillerCagePossibilitiesStrategy));
    run_consistency_test(
        || generate_stateful(
            BLOCK_WIDTH, 
            BLOCK_HEIGHT, 
            DefaultConstraint, 
            |s| KillerConstraint::new_singletons(s.grid())),
        solver, ITERATIONS_PER_RUN)
}

#[test]
fn thermo_strategic_backtracking() {
    let solver = StrategicBacktrackingSolver::new(
        CompositeStrategy::new(
            OnlyCellStrategy, 
            ThermometerFollowingStrategy));
    run_consistency_test(
        || generate_stateful(
            BLOCK_WIDTH,
            BLOCK_HEIGHT,
            DefaultConstraint,
            |s| {
                let mut rng = rand::thread_rng();
                ThermoConstraint::generate_for(s.grid(), &mut rng)
            }),
        solver, ITERATIONS_PER_RUN)
}

#[test]
fn sandwich_strategic_backtracking() {
    let solver = StrategicBacktrackingSolver::new(
        CompositeStrategy::new(
            OnlyCellStrategy, 
            CompositeStrategy::new(
                SandwichBunPlacementStrategy,
                SandwichPossibilitiesStrategy
            )));
    run_consistency_test(
        || generate_stateful(
            BLOCK_WIDTH, 
            BLOCK_HEIGHT, 
            DefaultConstraint, 
            |s| SandwichConstraint::new_full(s.grid())),
        solver, ITERATIONS_PER_RUN)
}

#[test]
fn many_strategic_backtracking() {
    let solver = StrategicBacktrackingSolver::new(
        CompositeStrategy::new(
            CompositeStrategy::new(
                OnlyCellStrategy,
                KillerCagePossibilitiesStrategy
            ),
            CompositeStrategy::new(
                ThermometerFollowingStrategy,
                CompositeStrategy::new(
                    SandwichBunPlacementStrategy,
                    SandwichPossibilitiesStrategy
                )
            )
        )
    );
    // Sadly, it becomes impossible to find a Sudoku matching a constraint
    // with literally all irreducible constraints.
    let constraint =
        CompositeConstraint::new(DefaultConstraint, DiagonalsConstraint);
    run_consistency_test(
        || generate_stateful(
            BLOCK_WIDTH,
            BLOCK_HEIGHT,
            constraint.clone(), 
            |s| {
                let grid = s.grid();
                let mut rng = rand::thread_rng();
                let killer = KillerConstraint::new_singletons(grid);
                let thermo = ThermoConstraint::generate_for(grid, &mut rng);
                let sandwich = SandwichConstraint::new_full(grid);
                CompositeConstraint::new(
                    killer,
                    CompositeConstraint::new(thermo, sandwich)
                )
            }),
        solver, ITERATIONS_PER_RUN)
}
