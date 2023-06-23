#!/usr/bin/env python

import z3

def one_hot(bools):
    return z3.PbEq([(b, 1) for b in bools], 1)

s = z3.Solver()

people = ["anna", "joe", "amy", "maya", "lara_b", "lara_c"]
room_numbers = list(range(1, len(people) + 1))

# each person's room prefernce order
pref_order = {
    "anna": [3, 5, 6, 1, 4, 2],
    "joe": [5, 4, 3, 6, 2, 1],
    "amy": [5, 6, 4, 3, 1, 2],
    "maya": [6, 5, 2, 4, 3, 1],
    "lara_b": [5, 4, 6, 1, 3, 2],
    "lara_c": [4, 5, 3, 6, 2, 1],
}

# where each person ranks room i - basically a score of how much they like it where lower is better
preferences = {
    person: [pref_order[person].index(i) + 1 for i in room_numbers]
    for person in people
}

rooms = {
    person: z3.Bools([f"{person}_{room}" for room in room_numbers])
    for person in people
}

# everyone should have one, and only one room
for person_rooms in rooms.values():
    s.add(one_hot(person_rooms))

# everyone should have different rooms
for room in room_numbers:
    s.add(one_hot([
        rooms[person][room - 1]
        for person in people
    ]))

score = 0
for person in people:
    for room, person_room in enumerate(rooms[person]):
        score = z3.If(person_room, score + preferences[person][room], score)

stop_if_found = True
for target in range(len(people), len(people) ** 2):
    s.push()
    s.add(score <= target)
    found = False
    while s.check() == z3.sat:
        found = True
        m = s.model()
        room_assignments = {}
        print(f"{target = }")
        for person in people:
            for i, person_room in enumerate(rooms[person]):
                if m[person_room]:
                    print(f"{person} => room {i + 1} - preference {preferences[person][i]}")
                    room_assignments[person] = i + 1
        print()
        s.add(z3.Not(z3.And([
            rooms[person][assignment - 1]
            for person, assignment in room_assignments.items()
        ])))
    else:
        if found and stop_if_found:
            break

    s.pop()
else:
    print("Unsat")
