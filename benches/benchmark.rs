use criterion::{criterion_group, criterion_main, BenchmarkGroup, Criterion};
use criterion::measurement::WallTime;

use toml::Value;
use toml::value::Table;

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
    NakedSingleStrategy,
    StrategicBacktrackingSolver
};

use std::fs;
use std::time::Duration;

// Note: When solving/reducing Sudoku with additional constraints, there are
// often less clues, leading to higher runtimes. We may therefore want to run
// those benchmarks with less examples.

const MEASUREMENT_TIME_SECS: u64 = 120;
const DEFAULT_SAMPLE_SIZE: usize = 100;
const CONSTRAINED_SAMPLE_SIZE: usize = 100;

const BENCHDATA_DIR: &'static str = "benchdata/";
const TASK_FILE_EXT: &'static str = ".toml";

struct Task<C: Constraint + Clone> {
    puzzle: Sudoku<C>,
    solution: SudokuGrid
}

fn get_entry<'a>(table: &'a Table, name: &str) -> &'a Value {
    table.get(name)
        .unwrap_or_else(||
            panic!("Expected {}, but was not present.", name))
}

fn get_array<'a>(table: &'a Table, name: &str) -> &'a Vec<Value> {
    let value = get_entry(table, name);
    value.as_array()
        .unwrap_or_else(||
            panic!("Expected {} as array, but was different type.", name))
}

fn get_string<'a>(table: &'a Table, name: &str) -> &'a str {
    let value = get_entry(table, name);
    value.as_str()
        .unwrap_or_else(||
            panic!("Expected {} as string, but was different type.", name))
}

impl<C: Constraint + Clone> Task<C> {
    fn parse(value: &Value, constraint: C) -> Task<C> {
        if let Value::Table(table) = value {
            let puzzle_code = get_string(table, "puzzle");
            let solution_code = get_string(table, "solution");
            let puzzle = Sudoku::parse(puzzle_code, constraint).unwrap();
            let solution = SudokuGrid::parse(solution_code).unwrap();

            if !puzzle.is_valid_solution(&solution).unwrap() {
                panic!("Invalid solution for task.");
            }

            Task {
                puzzle,
                solution
            }
        }
        else {
            panic!("Tried to parse task from non-table.");
        }
    }
}

fn parse_tasks<C: Constraint + Clone>(toml: String, constraint: C)
        -> Vec<Task<C>> {
    let root = toml.parse::<Value>()
        .expect("Tried to parse task vector from invalid TOML.");
    let root_table = root.as_table()
        .expect("Root object is not a table.");
    let array = get_array(root_table, "tasks");
    array.iter()
        .map(|value| Task::parse(value, constraint.clone()))
        .collect()
}

fn parse_tasks_from_file<C: Constraint + Clone>(file: String, constraint: C)
        -> Vec<Task<C>> {
    let toml = fs::read_to_string(file).unwrap();
    parse_tasks(toml, constraint)
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

fn benchmark_solver_constraint<C: Constraint + Clone, S: Solver>(
        group: &mut BenchmarkGroup<WallTime>, id: &str, sample_size: usize,
        constraint: C, solver: &S) {
    group.measurement_time(Duration::from_secs(MEASUREMENT_TIME_SECS));
    group.sample_size(sample_size);

    let mut file = String::from(BENCHDATA_DIR);
    file.push_str(id);
    file.push_str(TASK_FILE_EXT);
    let tasks: Vec<Task<C>> = parse_tasks_from_file(file, constraint);

    group.bench_function(id, |b| b.iter(|| solve_tasks(&tasks, solver)));
}

fn benchmark_solver<S: Solver>(c: &mut Criterion, group_name: &str,
        solver: S) {
    let mut group = c.benchmark_group(group_name);

    benchmark_solver_constraint(&mut group, "default", DEFAULT_SAMPLE_SIZE,
        DefaultConstraint, &solver);
    benchmark_solver_constraint(&mut group, "diagonals",
        CONSTRAINED_SAMPLE_SIZE,
        CompositeConstraint::new(DefaultConstraint, DiagonalsConstraint),
        &solver);
    benchmark_solver_constraint(&mut group, "knights-move",
        CONSTRAINED_SAMPLE_SIZE,
        CompositeConstraint::new(DefaultConstraint, KnightsMoveConstraint),
        &solver);
    benchmark_solver_constraint(&mut group, "kings-move",
        CONSTRAINED_SAMPLE_SIZE,
        CompositeConstraint::new(DefaultConstraint, KingsMoveConstraint),
        &solver);
    benchmark_solver_constraint(&mut group, "adjacent-consecutive",
        CONSTRAINED_SAMPLE_SIZE,
        CompositeConstraint::new(DefaultConstraint,
            AdjacentConsecutiveConstraint),
        &solver);
}

fn benchmark_backtracking(c: &mut Criterion) {
    benchmark_solver(c, "backtracking", BacktrackingSolver)
}

fn benchmark_simple_strategic_backtracking(c: &mut Criterion) {
    benchmark_solver(c, "simple strategic backtracking",
        StrategicBacktrackingSolver::new(NakedSingleStrategy))
}

criterion_group!(all,
    benchmark_backtracking,
    benchmark_simple_strategic_backtracking
);

criterion_main!(all);
