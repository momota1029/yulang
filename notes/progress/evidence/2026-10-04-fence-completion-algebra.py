#!/usr/bin/env python3
"""Finite-table certificate checks for the structural FMP proof.

Research evidence only: no compiler code, package solver, or source policy.
The arbitrary-tree and coinductive arguments are mathematical review duties.
"""

from itertools import product
import json


VALUES = {
    "E0": (1, 1),
    "U": (1, 2),
    "Dn": (2, 1),
    "B": (2, 2),
    "H": (2, 3),
    "L": (3, 2),
    "C": (3, 3),
}
NAMES = {value: name for name, value in VALUES.items()}
INV = dict(zip(VALUES, ("E0", "Dn", "U", "B", "H", "L", "C")))
PROJECTION = {"E0": "E0", "U": "U", "Dn": "Dn", "B": "L", "L": "L"}

# Rows and columns are in VALUES insertion order. This is the theorem's table.
TABLE = (
    "E0 U Dn B H L C",
    "U U H H H C C",
    "Dn L Dn L C L C",
    "B L H C C C C",
    "H C H C C C C",
    "L L C C C C C",
    "C C C C C C C",
)
PLUS = {
    (left, right): result
    for left, row in zip(VALUES, TABLE)
    for right, result in zip(VALUES, row.split())
}


def add(a, b):
    return PLUS[a, b]


def leq(a, b):
    return all(x <= y for x, y in zip(VALUES[a], VALUES[b]))


def meet(a, b):
    return NAMES[tuple(min(x, y) for x, y in zip(VALUES[a], VALUES[b]))]


def star(a):
    return NAMES[VALUES[a][::-1]]


def related(a, b):
    return leq(a, add("U", b)) and leq(b, add("Dn", a))


def check_algebra():
    for a, b in product(VALUES, repeat=2):
        u, d = VALUES[a]
        v, w = VALUES[b]
        concatenated = (
            min(3, u + (w if u % 2 == 0 else v) - 1),
            min(3, d + (v if d % 2 == 0 else w) - 1),
        )
        assert VALUES[add(a, b)] == concatenated, (a, b, "concatenation")
        assert INV[add(a, b)] == add(INV[b], INV[a]), (a, b, "reversal")
        assert star(add(a, b)) == add(star(a), star(b)), (a, b, "variance")
        assert INV[meet(a, b)] == meet(INV[a], INV[b]), (a, b, "inverse meet")
        assert star(meet(a, b)) == meet(star(a), star(b)), (a, b, "star meet")
        assert add("E0", a) == a == add(a, "E0")
        assert INV[INV[a]] == a == star(star(a))
        assert star(INV[a]) == INV[star(a)]
    for a, b, c in product(VALUES, repeat=3):
        assert add(add(a, b), c) == add(a, add(b, c)), (a, b, c, "associativity")
        assert add(a, meet(b, c)) == meet(add(a, b), add(a, c)), (a, b, c)
        assert add(meet(a, b), c) == meet(add(a, c), add(b, c)), (a, b, c)
        if leq(a, b):
            assert leq(add(a, c), add(b, c)), (a, b, c, "left monotonicity")
            assert leq(add(c, a), add(c, b)), (a, b, c, "right monotonicity")


def check_record_consistency():
    # Check every active parent pair, including B and L mapping to the same L.
    direct = exceptional = 0
    for a, b in product(PROJECTION, repeat=2):
        raw_a, raw_b = PROJECTION[a], PROJECTION[b]
        target = add(INV[raw_a], raw_b)
        if target not in {"H", "C"}:
            parent = add(INV[a], b)
            assert parent in PROJECTION, (a, b, parent)
            assert leq(PROJECTION[parent], target), (a, b, target)
            direct += 1
        else:
            # A selected-field landmark has value E0 or U at the parent.
            assert raw_a in {"Dn", "L"} and raw_b in {"Dn", "L"}
            for landmark in ("E0", "U"):
                bound_a = add(INV[a], landmark)
                bound_b = add(INV[b], landmark)
                assert bound_a in PROJECTION and bound_b in PROJECTION
                via_landmark = add(PROJECTION[bound_a], INV[PROJECTION[bound_b]])
                assert leq(via_landmark, target), (a, b, landmark, target)
            exceptional += 1
    return {"active_parent_pairs": direct + exceptional,
            "direct_parent_pairs": direct, "landmark_parent_pairs": exceptional}


def check_record_comparison():
    count = 0
    for s, t in product(VALUES, repeat=2):
        if not related(s, t):
            continue
        count += 1
        # G3: every T upper-near landmark is also upper-near in S.
        if leq(t, "U"):
            assert leq(s, "U")
        # G4 reverse direction: raw S support implies raw T support.
        if s in PROJECTION:
            assert t in PROJECTION, (s, t, "raw support")
            assert leq(PROJECTION[t], add("Dn", PROJECTION[s])), (s, t, "reverse")
        # G4 forward direction. Other contributors are restored via a landmark.
        if t in {"E0", "U"}:
            assert s in PROJECTION
            assert leq(PROJECTION[s], add("U", PROJECTION[t]))
        elif t in {"Dn", "B", "L"}:
            for landmark_t, landmark_s in product(("E0", "U"), repeat=2):
                parent_to_landmark = add(INV[t], landmark_t)
                assert parent_to_landmark in PROJECTION
                child_to_landmark = PROJECTION[parent_to_landmark]
                via_landmark = add(landmark_s, INV[child_to_landmark])
                assert leq(via_landmark, add("U", PROJECTION[t])), (s, t, "forward")
    return {"related_value_pairs": count}


def main():
    check_algebra()
    report = {"result": "PASS", "distance_values": 7, "algebra_pairs": 49,
              "algebra_triples": 343,
              "record_consistency": check_record_consistency(),
              "record_comparison": check_record_comparison(),
              "scope": "finite distance identities and Record local case splits only"}
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
