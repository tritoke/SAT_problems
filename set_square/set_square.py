#!/usr/bin/env python

from z3 import *
import itertools

grid = [[Int(f"tile_{x}_{y}") for x in range(3)] for y in range(3)]

s = Solver()

# less than 10
for cell in itertools.chain.from_iterable(grid):
    s.add(And(cell > 0, cell < 10))

# unique
for y in range(3):
    for x in range(3):
        s.add(And([grid[y][x] != cell for cell in itertools.chain.from_iterable(grid) if cell is not grid[y][x]]))

# rows
s.add((grid[0][0] + grid[0][1]) - grid[0][2] == 1)
s.add((grid[1][0] - grid[1][1]) * grid[1][2] == 54)
s.add((grid[2][0] * grid[2][1]) - grid[2][2] == 2)

# cols
s.add((grid[0][0] * grid[1][0]) * grid[2][0] == 56)
s.add((grid[0][1] / grid[1][1]) * grid[2][1] == 15)
s.add((grid[0][2] + grid[1][2]) - grid[2][2] == 7)

# fixed cells
s.add(grid[1][1] == 1)
s.add(grid[1][2] == 9)

while s.check() == sat:
    m = s.model()

    for row in grid:
        for cell in row:
            print(m[cell].as_long(), end=" ")
        print()

    s.add(Not(And([cell == m[cell] for cell in itertools.chain.from_iterable(grid)])))
else:
    print("unsat")
