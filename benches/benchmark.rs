use criterion::{criterion_group, criterion_main, Criterion};

use rand::SeedableRng;

use rand_chacha::ChaCha8Rng;

use sudoku_variants::Sudoku;
use sudoku_variants::constraint::{
    AdjacentConsecutiveConstraint,
    CompositeConstraint,
    Constraint,
    DefaultConstraint,
    DiagonalsConstraint,
    KnightsMoveConstraint,
    KingsMoveConstraint
};
use sudoku_variants::generator::{Generator, Reducer};
use sudoku_variants::solver::{BacktrackingSolver, Solver};

use std::time::Duration;

// Sampling parameters
// Note: we use multiple Sudoku in every benchmark for 2 reasons:
// 1: reduce the impact of creating new RNGs and other structs
// 2: avoid randomly getting very quickly/slowly generated Sudoku
// Also note: When solving/reducing Sudoku with additional constraints, there
// are often less clues, leading to higher runtimes. We therefore run those
// benchmarks with less examples.

const EXAMPLE_COUNT: usize = 3;
const MEASUREMENT_TIME_SECS: u64 = 60;
const DEFAULT_SAMPLE_SIZE: usize = 100;
const CONSTRAINED_SAMPLE_SIZE: usize = 10;

fn generate<C: Constraint + Clone>(constraint: &C) -> Vec<Sudoku<C>> {
    let rng = ChaCha8Rng::seed_from_u64(0xCAFE);
    let mut generator = Generator::new(rng);
    (0..3)
        .map(|_| generator.generate(3, 3, constraint.clone()).unwrap())
        .collect()
}

fn reduce_backtracking<C: Constraint + Clone>(mut sudoku: Vec<Sudoku<C>>)
        -> Vec<Sudoku<C>> {
    let rng = ChaCha8Rng::seed_from_u64(0xBA55);
    let mut reducer = Reducer::new(BacktrackingSolver, rng);

    for i in 0..EXAMPLE_COUNT {
        reducer.reduce(sudoku.get_mut(i).unwrap());
    }

    sudoku
}

fn solve_backtracking<C: Constraint + Clone>(sudoku: &Vec<Sudoku<C>>) {
    for i in 0..EXAMPLE_COUNT {
        BacktrackingSolver.solve(sudoku.get(i).unwrap());
    }
}

fn benchmark_constraint<C: Constraint + Clone>(c: &mut Criterion,
        group_name: &str, sample_size: usize, constraint: C) {
    let mut group = c.benchmark_group(group_name);
    group.measurement_time(Duration::from_secs(MEASUREMENT_TIME_SECS));
    group.sample_size(sample_size);

    let mut generated: Vec<Sudoku<C>> = Vec::new();
    group.bench_function("generate", |b|
        b.iter(|| generated = generate(&constraint)));

    let mut reduced: Vec<Sudoku<C>> = Vec::new();
    group.bench_function("reduce backtracking", |b|
        b.iter(|| reduced = reduce_backtracking(generated.clone())));

    group.bench_function("solve backtracking", |b|
        b.iter(|| solve_backtracking(&reduced)));
}

fn benchmark_default(c: &mut Criterion) {
    benchmark_constraint(c, "default", DEFAULT_SAMPLE_SIZE, DefaultConstraint)
}

fn benchmark_diagonals(c: &mut Criterion) {
    benchmark_constraint(c, "diagonals", CONSTRAINED_SAMPLE_SIZE,
        CompositeConstraint::new(DefaultConstraint, DiagonalsConstraint))
}

fn benchmark_knights_move(c: &mut Criterion) {
    benchmark_constraint(c, "knights move", CONSTRAINED_SAMPLE_SIZE,
        CompositeConstraint::new(DefaultConstraint, KnightsMoveConstraint))
}

fn benchmark_kings_move(c: &mut Criterion) {
    benchmark_constraint(c, "kings move", CONSTRAINED_SAMPLE_SIZE,
        CompositeConstraint::new(DefaultConstraint, KingsMoveConstraint))
}

fn benchmark_adjacent_consecutive(c: &mut Criterion) {
    benchmark_constraint(c, "adjacent consecutive", CONSTRAINED_SAMPLE_SIZE,
        CompositeConstraint::new(DefaultConstraint,
            AdjacentConsecutiveConstraint))
}

criterion_group!(all,
    benchmark_default,
    benchmark_diagonals,
    benchmark_knights_move,
    benchmark_kings_move,
    benchmark_adjacent_consecutive
);

criterion_main!(all);
