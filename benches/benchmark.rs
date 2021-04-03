use criterion::{
    criterion_group,
    criterion_main,
    BenchmarkGroup,
    Criterion,
    SamplingMode
};
use criterion::measurement::WallTime;

use sudoku_variants::{Sudoku, SudokuGrid};
use sudoku_variants::constraint::{
    AdjacentConsecutiveConstraint,
    CompositeConstraint,
    Constraint,
    DefaultConstraint,
    DiagonalsConstraint,
    KnightsMoveConstraint,
    KingsMoveConstraint
};
use sudoku_variants::solver::{BacktrackingSolver, Solution, Solver};
use sudoku_variants::solver::strategy::{
    BoundedCellsBacktrackingStrategy,
    BoundedOptionsBacktrackingStrategy,
    CompositeStrategy,
    NakedSingleStrategy,
    OnlyCellStrategy,
    StrategicBacktrackingSolver,
    TupleStrategy
};

use serde::Deserialize;

use std::fs;
use std::time::Duration;

// Note: When solving/reducing Sudoku with additional constraints, there are
// often less clues, leading to higher runtimes. We may therefore want to run
// those benchmarks with less examples.

// Explanation of benchmark classes:
//
// backtracking: A simple BacktrackingSolver which does not use strategies.
// simple strategic backtracking: A StrategicBacktrackingSolver which uses only
//                                the NakedSingleStrategy.
// fastest strategic backtracking: A StrategicBacktrackingSolver which uses the
//                                 combination of strategies that yields the
//                                 best benchmark results.
// complex strategic backtracking: A StrategicBacktrackingSolver which uses all
//                                 available strategies with sensible settings.

const MEASUREMENT_TIME_SECS: u64 = 30;
const DEFAULT_SAMPLE_SIZE: usize = 100;
const CONSTRAINED_SAMPLE_SIZE: usize = 100;

const BENCHDATA_DIR: &'static str = "benchdata/";
const TASK_FILE_EXT: &'static str = ".json";

#[derive(Deserialize)]
struct Task<C: Constraint + Clone> {
    puzzle: Sudoku<C>,
    solution: SudokuGrid
}

#[derive(Deserialize)]
struct Tasks<C: Constraint + Clone> {
    tasks: Vec<Task<C>>,
    only_fast: bool
}

fn solve_task<C: Constraint + Clone, S: Solver>(task: &Task<C>, solver: &S) {
    let computed_solution = solver.solve(&task.puzzle);
    assert_eq!(Solution::Unique(task.solution.clone()), computed_solution);
}

fn solve_tasks<C: Constraint + Clone, S: Solver>(tasks: &Vec<Task<C>>,
        solver: &S) {
    for task in tasks {
        solve_task(task, solver);
    }
}

fn benchmark_solver_constraint<C, S>(group: &mut BenchmarkGroup<WallTime>,
    id: &str, sample_size: usize, solver: &S, fast: bool)
where
    for<'de> C: Constraint + Clone + Deserialize<'de>,
    S: Solver
{
    let mut file = String::from(BENCHDATA_DIR);
    file.push_str(id);
    file.push_str(TASK_FILE_EXT);
    let json = fs::read_to_string(file).unwrap();
    let tasks: Tasks<C> = serde_json::from_str(&json).unwrap();

    if tasks.only_fast && !fast {
        return;
    } 

    group.measurement_time(Duration::from_secs(MEASUREMENT_TIME_SECS));
    group.sample_size(sample_size);
    group.sampling_mode(SamplingMode::Flat);
    group.bench_function(id, |b| b.iter(|| solve_tasks(&tasks.tasks, solver)));
}

type DefaultAndDiagonalsConstraint =
    CompositeConstraint<DefaultConstraint, DiagonalsConstraint>;
type DefaultAndKnightsMoveConstraint =
    CompositeConstraint<DefaultConstraint, KnightsMoveConstraint>;
type DefaultAndKingsMoveConstraint =
    CompositeConstraint<DefaultConstraint, KingsMoveConstraint>;
type DefaultAndAdjacentConsecutiveConstraint =
    CompositeConstraint<DefaultConstraint, AdjacentConsecutiveConstraint>;

fn benchmark_solver<S: Solver>(c: &mut Criterion, group_name: &str,
        solver: S, fast: bool) {
    let mut group = c.benchmark_group(group_name);

    benchmark_solver_constraint::<DefaultConstraint, _>(&mut group, "default",
        DEFAULT_SAMPLE_SIZE, &solver, fast);
    benchmark_solver_constraint::<DefaultAndDiagonalsConstraint, _>(&mut group,
        "diagonals", CONSTRAINED_SAMPLE_SIZE, &solver, fast);
    benchmark_solver_constraint::<DefaultAndKnightsMoveConstraint, _>(
        &mut group, "knights-move", CONSTRAINED_SAMPLE_SIZE, &solver, fast);
    benchmark_solver_constraint::<DefaultAndKingsMoveConstraint, _>(&mut group,
        "kings-move", CONSTRAINED_SAMPLE_SIZE, &solver, fast);
    benchmark_solver_constraint::<DefaultAndAdjacentConsecutiveConstraint, _>(
        &mut group, "adjacent-consecutive", CONSTRAINED_SAMPLE_SIZE, &solver,
            fast);
}

fn benchmark_backtracking(c: &mut Criterion) {
    benchmark_solver(c, "backtracking", BacktrackingSolver, false)
}

fn benchmark_simple_strategic_backtracking(c: &mut Criterion) {
    benchmark_solver(c, "simple strategic backtracking",
        StrategicBacktrackingSolver::new(NakedSingleStrategy), true)
}

fn benchmark_fastest_strategic_backtracking(c: &mut Criterion) {
    benchmark_solver(c, "fastest strategic backtracking",
        StrategicBacktrackingSolver::new(CompositeStrategy::new(
            NakedSingleStrategy, OnlyCellStrategy)), true)
}

fn benchmark_complex_strategic_backtracking(c: &mut Criterion) {
    benchmark_solver(c, "complex strategic backtracking",
        StrategicBacktrackingSolver::new(CompositeStrategy::new(
            CompositeStrategy::new(
                NakedSingleStrategy, OnlyCellStrategy),
            CompositeStrategy::new(
                TupleStrategy::new(|size| size - 2),
                CompositeStrategy::new(
                    BoundedCellsBacktrackingStrategy::new(|size| size - 2,
                        |_| Some(1), OnlyCellStrategy),
                    BoundedOptionsBacktrackingStrategy::new(|_| 2,
                        |_| Some(1), CompositeStrategy::new(
                            NakedSingleStrategy, OnlyCellStrategy
                        )
                    )
                )
            )
        )), true
    )
}

criterion_group!(all,
    benchmark_backtracking,
    benchmark_simple_strategic_backtracking,
    benchmark_fastest_strategic_backtracking,
    benchmark_complex_strategic_backtracking
);

criterion_main!(all);
