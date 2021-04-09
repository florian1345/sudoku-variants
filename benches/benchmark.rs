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
    KillerConstraint,
    KingsMoveConstraint
};
use sudoku_variants::solver::{BacktrackingSolver, Solution, Solver};
use sudoku_variants::solver::strategy::{
    BoundedCellsBacktrackingStrategy,
    BoundedOptionsBacktrackingStrategy,
    CompositeStrategy,
    NakedSingleStrategy,
    NoStrategy,
    OnlyCellStrategy,
    StrategicBacktrackingSolver,
    TupleStrategy
};
use sudoku_variants::solver::strategy::specific::{
    KillerCagePossibilitiesStrategy
};

use serde::Deserialize;

use std::fs;
use std::time::Duration;

const MEASUREMENT_TIME_SECS: u64 = 30;
const BENCHDATA_DIR: &'static str = "benchdata/";
const TASK_FILE_EXT: &'static str = ".json";

#[derive(Deserialize)]
#[serde(rename_all = "snake_case")]
enum SolverType {

    /// Basic backtracking without strategy.
    Basic,

    /// Strategic backtracking with [NoStrategy].
    NoStrategy,

    /// Strategic backtracking with [OnlyCellStrategy].
    OnlyCellStrategy,

    /// Strategic backtracking with [OnlyCellStrategy] and
    /// [NakedSingleStrategy].
    SimpleStrategy,

    /// Strategic backtracking with all general strategies.
    ComplexStrategy,

    /// Strategic backtracking with the [KillerCagePossibilitiesStrategy].
    KillerStrategy
}

#[derive(Deserialize)]
struct Task<C: Constraint + Clone + 'static> {
    puzzle: Sudoku<C>,
    solution: SudokuGrid
}

#[derive(Deserialize)]
struct Tasks<C: Constraint + Clone + 'static> {
    tasks: Vec<Task<C>>,
    solvers: Vec<SolverType>,
    sample_size: usize
}

fn solve_task<C, S>(task: &Task<C>, solver: &S)
where
    C: Constraint + Clone + 'static,
    S: Solver
{
    let computed_solution = solver.solve(&task.puzzle);
    assert_eq!(Solution::Unique(task.solution.clone()), computed_solution);
}

fn solve_tasks<C, S>(tasks: &Vec<Task<C>>, solver: &S)
where
    C: Constraint + Clone + 'static,
    S: Solver
{
    for task in tasks {
        solve_task(task, solver);
    }
}

fn bench_solver<C, S>(group: &mut BenchmarkGroup<WallTime>, tasks: &Tasks<C>,
    id: &str, solver: S)
where
    for<'de> C: Constraint + Clone + Deserialize<'de> + 'static,
    S: Solver
{
    group.bench_function(id,
        |b| b.iter(|| solve_tasks(&tasks.tasks, &solver)));
}

fn benchmark_constraint<C>(c: &mut Criterion, id: &str)
where
    for<'de> C: Constraint + Clone + Deserialize<'de> + 'static
{
    let mut group = c.benchmark_group(id);
    let mut file = String::from(BENCHDATA_DIR);
    file.push_str(id);
    file.push_str(TASK_FILE_EXT);
    let json = fs::read_to_string(file).unwrap();
    let tasks: Tasks<C> = serde_json::from_str(&json).unwrap();

    group.measurement_time(Duration::from_secs(MEASUREMENT_TIME_SECS));
    group.sample_size(tasks.sample_size);
    group.sampling_mode(SamplingMode::Flat);

    for solver in &tasks.solvers {
        match solver {
            SolverType::Basic =>
                bench_solver(&mut group, &tasks, "basic", BacktrackingSolver),
            SolverType::NoStrategy =>
                bench_solver(&mut group, &tasks, "no-strategy",
                    StrategicBacktrackingSolver::new(NoStrategy)),
            SolverType::OnlyCellStrategy =>
                bench_solver(&mut group, &tasks, "only-cell-strategy",
                    StrategicBacktrackingSolver::new(OnlyCellStrategy)),
            SolverType::SimpleStrategy =>
                bench_solver(&mut group, &tasks, "simple-strategy",
                    StrategicBacktrackingSolver::new(
                        CompositeStrategy::new(
                            OnlyCellStrategy,
                            NakedSingleStrategy))),
            SolverType::ComplexStrategy =>
                bench_solver(&mut group, &tasks, "complex-strategy",
                    StrategicBacktrackingSolver::new(
                        CompositeStrategy::new(
                            CompositeStrategy::new(
                                OnlyCellStrategy,
                                NakedSingleStrategy
                            ),
                            CompositeStrategy::new(
                                TupleStrategy::new(|_| 4),
                                CompositeStrategy::new(
                                    BoundedOptionsBacktrackingStrategy::new(
                                        |_| 4, |_| None, OnlyCellStrategy),
                                    BoundedCellsBacktrackingStrategy::new(
                                        |_| 4, |_| None, OnlyCellStrategy)
                                    ))))),
            SolverType::KillerStrategy =>
                bench_solver(&mut group, &tasks, "killer-strategy",
                    StrategicBacktrackingSolver::new(
                        KillerCagePossibilitiesStrategy))
        }
    }
}

type DefaultDiagonalsConstraint =
    CompositeConstraint<DefaultConstraint, DiagonalsConstraint>;
type DefaultKnightsMoveConstraint =
    CompositeConstraint<DefaultConstraint, KnightsMoveConstraint>;
type DefaultKingsMoveConstraint =
    CompositeConstraint<DefaultConstraint, KingsMoveConstraint>;
type DefaultAdjacentConsecutiveConstraint =
    CompositeConstraint<DefaultConstraint, AdjacentConsecutiveConstraint>;
type DefaultKillerConstraint =
    CompositeConstraint<DefaultConstraint, KillerConstraint>;

fn benchmark_default(c: &mut Criterion) {
    benchmark_constraint::<DefaultConstraint>(c, "default")
}

fn benchmark_diagonals(c: &mut Criterion) {
    benchmark_constraint::<DefaultDiagonalsConstraint>(c, "diagonals")
}

fn benchmark_knights_move(c: &mut Criterion) {
    benchmark_constraint::<DefaultKnightsMoveConstraint>(c, "knights-move")
}

fn benchmark_kings_move(c: &mut Criterion) {
    benchmark_constraint::<DefaultKingsMoveConstraint>(c, "kings-move")
}

fn benchmark_adjacent_consecutive(c: &mut Criterion) {
    benchmark_constraint::<DefaultAdjacentConsecutiveConstraint>(c,
        "adjacent-consecutive")
}

fn benchmark_killer(c: &mut Criterion) {
    benchmark_constraint::<DefaultKillerConstraint>(c, "killer")
}

criterion_group!(all,
    benchmark_default,
    benchmark_diagonals,
    benchmark_knights_move,
    benchmark_kings_move,
    benchmark_adjacent_consecutive,
    benchmark_killer
);

criterion_main!(all);
