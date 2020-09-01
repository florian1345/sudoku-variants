# sudoku-variants

A flexible Sudoku engine for Rust that supports common variations and custom rules.

# Features

* Parsing and printing Sudoku
* Checking validity of Sudoku and solutions according to standard rules as well as some common variants
* Injection of custom constraints
* Solving Sudoku using a perfect backtracking algorithm
* Generating Sudoku, with a possibility to specify a custom solver that has to be able to solve the result, thus controlling the difficulty

# Planned Improvements

* Allow stateful constraints that can be reduced, such as Killer Sudoku
* Implement some more common constraints (e.g. Killer, Sandwich, Mini-Killer, maybe more)
* Provide a family of solvers that use patterns and logic, much like a human, to allow users to define a difficulty without writing their own solver
* Improve the performance of the perfect backtracking solver
