# sudoku-variants

A flexible Sudoku engine for Rust that supports common variations and custom rules.

# Features

* Parsing and printing Sudoku
* Checking validity of Sudoku and solutions according to standard rules as well as some common variants
* Injection of custom constraints
* Solving Sudoku using a perfect backtracking algorithm
* Generating Sudoku, with a possibility to specify a solver that has to be able to solve the result, thus controlling the difficulty
* Strategies that resemble human reasoning, which can be used to accelerate backtracking or to control the difficulty of generated Sudoku
* Definition of custom strategies

# Planned Improvements

* Allow stateful constraints that can be reduced, such as Killer Sudoku
* Implement some more common constraints (e.g. Killer, Sandwich, Mini-Killer, maybe more)
* Improve the performance of the perfect backtracking solver
* Integrate with the Serde framework
* Enable non-standard topologies of Sudoku fields (e.g. dead cells, grids without blocks)

# Links

* [Crate](https://crates.io/crates/sudoku-variants)
* [Documentation](https://docs.rs/sudoku-variants/)
* [Repository](https://github.com/florian1345/sudoku-variants)
