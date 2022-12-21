#!/usr/bin/env python
import z3
import sys
import pathlib
import numpy as np
from dataclasses import dataclass
from collections import deque


PUZZLE_PATH = pathlib.Path("./puzzles")


def main():
    # get the puzzle to solve
    if len(sys.argv) > 1:
        puzzle_name = sys.argv[1]
    else:
        puzzle_name = "15x15_ship.non"

    puzzle = parse_puzzle(PUZZLE_PATH / puzzle_name)

    # encode the puzzle logic
    solver = z3.Solver()
    board = puzzle.make_board()

    # encode booleans as ints which are either 0 or 1
    for tile in board.flat:
        solver.add(z3.Xor(tile == 0, tile == 1))

    puzzle.add_constraints(solver, board)

    if solver.check() == z3.sat:
        print("Solved")
        print_board(solver.model(), board)
        #print_board(solver.model(), board, fancy=False)
    else:
        print("Couldn't solve.")


@dataclass
class Puzzle:
    lefts: [[int]]
    verts: [[int]]

    def make_board(self) -> np.array:
        return np.array(
            [
                [
                    z3.Int(f"s_{x}_{y}")
                    for x in range(len(self.verts))
                ]
                for y in range(len(self.lefts))
            ]
        )

    def add_constraints(self, solver, board):
        for prefix, groups, vec_enum in zip(["ls", "vs"], [self.lefts, self.verts], [enumerate(board), enumerate(board.T)]):
            for groups, (vec_num, vec) in zip(groups, vec_enum):
                group_sum = 0
                starts = []

                for (i, group) in enumerate(groups):
                    window_start = z3.Int(f"{prefix}_{vec_num}_{i}")
                    starts.append(window_start)

                    solver.add(
                        z3.Or([
                            z3.And(
                                sum(window) == group,
                                window_start == group_sum + j
                            )
                            for (j, window) in enumerate(window_iter(vec[group_sum:], group))
                        ])
                    )

                    group_sum += group + 1

                solver.add(sum(vec) == sum(groups))
                solver.add(z3.And([
                    s1 < s2
                    for s1, s2 in zip(starts, starts[1:])
                ]))

                for start in starts:
                    solver.add(z3.Or([start == 0] + [
                        z3.And(
                            start == i,
                            cell == 0,
                        )
                        for i, cell in zip(range(1, len(vec)), vec)
                    ]))


def window_iter(iterable, window_len):
    window = deque(maxlen=window_len)
    for item in iter(iterable):
        window.append(item)
        # fill the window
        if len(window) < window_len:
            continue

        yield list(window)


def parse_puzzle(path_to_puzzle) -> Puzzle:
    with open(path_to_puzzle) as f:
        left_block, vert_block = f.read().split("\n\n")[:2]

    parse_line = lambda line: [int(i) for i in line.split(",")]
    lefts = [parse_line(line) for line in left_block.splitlines()]
    verts = [parse_line(line) for line in vert_block.splitlines()]

    return Puzzle(lefts, verts)


def print_board(model, board, fancy=True):
    mapping = {
        1: " " if fancy else "1",
        0: "\N{FULL BLOCK}" if fancy else "0"
    }
    for row in board:
        row_repr = "".join(
            mapping[model[cell].as_long()]
            for cell in row
        )

        print(row_repr)

if __name__ == "__main__":
    main()
