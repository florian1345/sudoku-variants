use crate::{Sudoku, SudokuGrid};
use crate::constraint::DefaultConstraint;
use crate::solver::{Solution, Solver};
use crate::solver::strategy::{
    OnlyCellStrategy,
    StrategicBacktrackingSolver
};

#[test]
fn only_cell_strategic_backtracking() {
    let sudoku = Sudoku::parse("3x3;
         , , , , ,7,3, , ,\
         ,1,2, , , ,5,4, ,\
         , ,3,4, , , ,1, ,\
         , ,5,6, , , ,8, ,\
         , , , , , , , , ,\
        7, , , , ,2,4, , ,\
        6,4,1, , , ,8, , ,\
        5,3, , , ,6,7, , ,\
         , , , , ,9, , , ", DefaultConstraint).unwrap();
    let solver = StrategicBacktrackingSolver::new(OnlyCellStrategy);
    let expected = SudokuGrid::parse("3x3;
        4,5,6,2,1,7,3,9,8,\
        8,1,2,9,6,3,5,4,7,\
        9,7,3,4,5,8,6,1,2,\
        1,2,5,6,7,4,9,8,3,\
        3,6,4,8,9,1,2,7,5,\
        7,9,8,5,3,2,4,6,1,\
        6,4,1,7,2,5,8,3,9,\
        5,3,9,1,8,6,7,2,4,\
        2,8,7,3,4,9,1,5,6").unwrap();

    assert_eq!(Solution::Unique(expected), solver.solve(&sudoku));
}
