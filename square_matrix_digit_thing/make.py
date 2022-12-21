#!/usr/bin/env python
import z3
import numpy as np

def print_matrix(matrix, model):
    mat = np.array(
        [model[elem].as_long() for elem in matrix.flat],
    ).reshape(matrix.shape)
    print(mat)
    print(np.matmul(mat, mat))

s = z3.Solver()

# create our 2d matrix
matrix = np.array([
    [
        z3.Int(f"mat_{x}_{y}")
        for x in range(2)
    ]
    for y in range(2)
])

# restrict to digits less than 10 for now
for elem in matrix.flat:
    s.add(0 < elem)
    s.add(elem < 10)

# perform the matrix squaring
squared_matrix = np.matmul(matrix, matrix)

# assert the property that the squared matrix
# is a digit doubling of each original digit
# i.e. 3 -> 33
# so squared == 11 * original
for elem, squared_elem in zip(matrix.flat, squared_matrix.flat):
    s.add(squared_elem == elem * 11)

# assert all elements of the first matrix are unique
elem_list = list(matrix.flat)
for index, elem in enumerate(elem_list):
    for other_elem in elem_list[index + 1:]:
        s.add(elem != other_elem)

if not s.check() == z3.sat:
    print("Could not find any solutions")
else:
    while s.check() == z3.sat:
        m = s.model()
        print_matrix(matrix, m)
        print()

        # make it so that this exact matrix can't happen again
        s.add(
            z3.Not(
                z3.And(*(
                    elem == m[elem].as_long()
                    for elem in matrix.flat
                ))
            )
        )
