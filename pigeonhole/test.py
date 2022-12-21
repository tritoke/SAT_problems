#!/usr/bin/env python
import numpy as np
import z3

def at_most_k(variables, k):
    return sum(variables) <= k

def exactly_k(variables, k):
    return sum(variables) == k

def k_pigeonhole(k, n, m):
    """
    n objects
    m boxes
    k objects per box
    """
    assert n >= 1
    assert m >= 1

    print(f"{k}-Pigeonhole for {n} objects and {m} boxes.")

    s = z3.Solver()

    boxes = [
        [
            z3.Int(f"c_{i}_{j}")
            for j in range(1, n + 1) # loop through objects
        ]
        for i in range(1, m + 1) # loop through boxes
    ]

    # assert that the value is either 1 or 0
    for box in boxes:
        for obj in box:
            s.add(obj >= 0)
            s.add(obj <= 1)

    # assert that at most n object can be in each box
    for box in boxes:
        s.add(at_most_k(box, k))

    # assert that at exactly object is contained by exactly one box
    for obj_no in range(n):
        objects = [
            box[obj_no]
            for box in boxes
        ]
        s.add(exactly_k(objects, 1))

    if s.check() == z3.sat:
        m = s.model()
        for box_no, box in enumerate(boxes):
            for obj_no, obj in enumerate(box):
                if m[obj].as_long() == 1:
                    print(f"box {box_no + 1} contains object {obj_no + 1}")
    else:
        print("Not possible.")


def main():
    k_pigeonhole(2, 10, 5)
    k_pigeonhole(2, 11, 5)
    k_pigeonhole(3, 11, 5)


if __name__ == "__main__":
    main()
