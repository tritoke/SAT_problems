#!/usr/bin/env python
import csv
import itertools as it
import math
import numpy as np
import pathlib
import sys
import z3


class SudokuSolver:
    def __init__(self, puzzle_file):
        # get side len and puzzle
        self._side_len = self._get_side_len(puzzle_file)
        self._cell_width = int(math.sqrt(self._side_len))
        self.puzzle = self._read_puzzle(puzzle_file)

    def solutions(self):
        """
        Adds the constraints and return an iterator over the solutions
        """
        solver = z3.Solver()
        # create the unconstrained board
        board = self._create_board()
        # constrain each variable to 0/1, emulating boolean semantics
        self._limit_int_to_bool(solver, board)
        # add the elements from the puzzle to the board
        self._add_puzzle_constraints(solver, board)

        # add sudoku rules
        self._add_digit_constraints(solver, board)
        self._add_row_constraints(solver, board)
        self._add_column_constraints(solver, board)
        self._add_cell_constraints(solver, board)

        while solver.check() == z3.sat:
            solution = self._extract_solution(solver.model(), board)
            yield solution
            self._remove_solution(solver, board, solution)

    def _get_side_len(self, puzzle_file):
        with open(puzzle_file) as f:
            return f.readline().count(",") + 1

    def _read_puzzle(self, puzzle_file):
        puzzle = np.zeros((self._side_len, self._side_len), dtype="uint8")

        with open(puzzle_file) as f:
            for row, line in enumerate(csv.reader(f)):
                for col, digit in enumerate(line):
                    if digit.isnumeric():
                        puzzle[row, col] = int(digit)

        return puzzle

    def _create_board(self):
        """
        returns the unconstrained board
        """
        return np.array(
            [
                [
                    [
                        z3.Int(f"BOARD_{row}_{col}_{digit}")
                        for digit in range(1, self._side_len + 1)
                    ]
                    for col in range(1, self._side_len + 1)
                ]
                for row in range(1, self._side_len + 1)
            ]
        )

    def _limit_int_to_bool(self, solver, board):
        """
        allows using ints as booleans
        - useful for encoding cardinality constraints
        """
        for var in board.flat:
            solver.add(var >= 0)
            solver.add(var <= 1)

    def _add_puzzle_constraints(self, solver, board):
        """
        adds the board constraints from a board file
        """
        for row_no, row in enumerate(self.puzzle):
            for cell_no, cell in enumerate(row):
                if cell != 0:
                    # the element at row, col is digit - encode it as a one
                    solver.add(board[row_no, cell_no, cell - 1] == 1)

    def _extract_solution(self, model, board):
        """
        Extracts the solution array from a model
        """
        solved_board = np.zeros((self._side_len, self._side_len), "uint8")
        for x, y, i in it.product(range(self._side_len), repeat=3):
            cell = board[x, y, i]
            if model[cell].as_long() == 1:
                if solved_board[x, y] != 0:
                    print(f"multiple digits in box {x, y}")
                solved_board[x, y] = i + 1

        return solved_board

    @staticmethod
    def print_puzzle(puzzle):
        SIDE_LEN = puzzle.shape[0]
        CELL_WIDTH = int(math.sqrt(SIDE_LEN))

        bottom_cell_border_centre = "═╧═".join("═" * CELL_WIDTH)
        top_cell_border_centre = "═╤═".join("═" * CELL_WIDTH)

        bottom_border_centre = "═╩═".join([bottom_cell_border_centre] * CELL_WIDTH)
        top_border_centre = "═╦═".join([top_cell_border_centre] * CELL_WIDTH)

        top_border = "╔═" + top_border_centre + "═╗\n"
        bottom_border = "╚═" + bottom_border_centre + "═╝"

        row_sep = (
            "╟─" + "─╫─".join(["─┼─".join("─" * CELL_WIDTH)] * CELL_WIDTH) + "─╢\n"
        )

        cell_row_sep = (
            "╠═" + "═╬═".join(["═╪═".join("═" * CELL_WIDTH)] * CELL_WIDTH) + "═╣\n"
        )

        make_cell_rows = lambda rows: row_sep.join(
            (
                "║"
                + "║".join(
                    "│".join(
                        f"{i: ^3}" if i != 0 else " " * 3 for i in row[i : i + CELL_WIDTH]
                    )
                    for i in range(0, SIDE_LEN, CELL_WIDTH)
                )
                + "║\n"
            )
            for row in rows
        )

        puzzle_str = (
            top_border
            + cell_row_sep.join(
                make_cell_rows(puzzle[row : row + CELL_WIDTH])
                for row in range(0, SIDE_LEN, CELL_WIDTH)
            )
            + bottom_border
        )

        print(puzzle_str)

    def _one_hot(self, variables):
        return sum(variables.flat) == 1

    def _add_digit_constraints(self, solver, board):
        """
        only one digit can be in each cell
        """
        for row in board:
            for cell in row:
                solver.add(self._one_hot(cell))

    def _add_row_constraints(self, solver, board):
        """
        each digit can only appear once in each row
        """
        for row in range(self._side_len):
            for digit in range(self._side_len):
                solver.add(self._one_hot(board[row, :, digit]))

    def _add_column_constraints(self, solver, board):
        """
        each digit can only appear once in each column
        """
        for col in range(self._side_len):
            for digit in range(self._side_len):
                solver.add(self._one_hot(board[:, col, digit]))

    def _add_cell_constraints(self, solver, board):
        """
        each digit can only appear once in each cell
        """
        for cell_no in range(self._side_len):
            cell_x, cell_y = divmod(cell_no, self._cell_width)

            start_x = cell_x * self._cell_width
            start_y = cell_y * self._cell_width

            for digit in range(self._side_len):
                solver.add(
                    self._one_hot(
                        board[
                            start_x : start_x + self._cell_width,
                            start_y : start_y + self._cell_width,
                            digit,
                        ]
                    )
                )

    def _remove_solution(self, solver, board, solution):
        solver.add(
            z3.Not(
                z3.And(
                    *(
                        board[row, col, solution[row, col] - 1] == 1
                        for row, col in it.product(range(self._side_len), repeat=2)
                    )
                )
            )
        )


def main():
    puzzle_path = pathlib.Path("./tests")
    if len(sys.argv) == 2:
        puzzle_file = puzzle_path / sys.argv[1]
    else:
        puzzle_file = puzzle_path / "extreme.csv"

    solver = SudokuSolver(puzzle_file)

    SudokuSolver.print_puzzle(solver.puzzle)

    for solution in solver.solutions():
        SudokuSolver.print_puzzle(solution)
        break


if __name__ == "__main__":
    main()
