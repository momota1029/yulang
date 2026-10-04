#!/usr/bin/env python3
"""Exhaustive point-row scheme-freshening probe.

This checks the conditional finite point-row presentation in
coupled-effect-interface-core-draft.md: each source occurrence may match any
same-head target occurrence, and all alternatives remain in the joint formula.
It exercises two independently freshened uses under a correlated receiver
constraint. It is not an effect-subtyping rule, Function comparison, source
generator, or principal-scheme theorem.

Run: python3 tools/research_principal_row_match.py
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product


@dataclass(frozen=True, order=True)
class Assignment:
    receiver: int
    use1_a: int
    use1_b: int
    use2_a: int
    use2_b: int


def assignments() -> tuple[Assignment, ...]:
    return tuple(Assignment(*xs) for xs in product((0, 1), repeat=5))


def row_match(assignment: Assignment, a: int, b: int) -> bool:
    """One F<r> occurrence is covered by either F<a> or F<b>."""
    return a == assignment.receiver or b == assignment.receiver


def independently_freshened_scheme(assignment: Assignment) -> bool:
    return row_match(assignment, assignment.use1_a, assignment.use1_b) and row_match(
        assignment, assignment.use2_a, assignment.use2_b
    )


def occurrence_level_matching(assignment: Assignment) -> bool:
    """Direct finite witness search, independent of the disjunctive formula."""
    receiver = assignment.receiver
    use1_targets = (assignment.use1_a, assignment.use1_b)
    use2_targets = (assignment.use2_a, assignment.use2_b)
    return any(x == receiver for x in use1_targets) and any(
        x == receiver for x in use2_targets
    )


def correlated_receiver_constraint(assignment: Assignment) -> bool:
    """A joint client observes the two uses and requires both A views differ."""
    return assignment.use1_a != assignment.use2_a and assignment.use1_b != assignment.use2_b


def eager_first_match_mutant(assignment: Assignment) -> bool:
    """Unsoundly commits every use to the left target before seeing clients."""
    return (
        assignment.use1_a == assignment.receiver
        and assignment.use2_a == assignment.receiver
    )


def three_use_exhaustion() -> tuple[int, int, int]:
    """Scale fresh row alternatives to three uses and three ground classes."""
    checked = admitted = restricted = 0
    for row in product(range(3), repeat=7):
        receiver, a0, b0, a1, b1, a2, b2 = row
        targets = ((a0, b0), (a1, b1), (a2, b2))
        formula = all(receiver in pair for pair in targets)
        direct_witness = any(
            all(targets[i][choice] == receiver for i, choice in enumerate(choices))
            for choices in product((0, 1), repeat=3)
        )
        assert formula == direct_witness
        checked += 1
        if not formula:
            continue
        admitted += 1
        # A client correlates endpoints from different fresh uses. This keeps
        # the point-row choices conditional until after all uses are joined.
        client = (
            targets[0][0] != targets[1][0]
            and targets[1][1] != targets[2][1]
        )
        if client:
            restricted += 1
            eager = all(pair[0] == receiver for pair in targets)
            assert not eager
    assert checked == 3**7
    assert admitted > 0 and restricted > 0
    return checked, admitted, restricted


def main() -> None:
    universe = assignments()
    assert len(universe) == 32

    # The retained disjunction and explicit occurrence witnesses denote the
    # same complete assignment relation, including cross-use observations.
    for item in universe:
        assert independently_freshened_scheme(item) == occurrence_level_matching(item)

    admitted = tuple(item for item in universe if independently_freshened_scheme(item))
    assert len(admitted) == 18
    restricted = tuple(
        item
        for item in admitted
        if correlated_receiver_constraint(item)
    )
    assert len(restricted) == 4

    mutant_restricted = tuple(
        item
        for item in universe
        if eager_first_match_mutant(item) and correlated_receiver_constraint(item)
    )
    assert not mutant_restricted

    # Report the lexicographically least witness lost only by eager choice.
    lost = min(restricted)
    assert not eager_first_match_mutant(lost)
    assert row_match(lost, lost.use1_a, lost.use1_b)
    assert row_match(lost, lost.use2_a, lost.use2_b)
    three = three_use_exhaustion()

    print(f"complete assignments checked: {len(universe)}")
    print(f"assignments admitted by two independently freshened row constraints: {len(admitted)}")
    print(f"assignments after correlated receiver restriction: {len(restricted)}")
    print(f"assignments retained by eager-left-match mutant after restriction: {len(mutant_restricted)}")
    print(
        f"three-use, three-class assignments: {three[0]}; admitted: {three[1]}; "
        f"after client join: {three[2]}"
    )
    print(
        "lexicographically least lost assignment in the stated binary universe "
        "(receiver, use1 targets, use2 targets): "
        f"{(lost.receiver, (lost.use1_a, lost.use1_b), (lost.use2_a, lost.use2_b))}"
    )
    print(
        "scope: conditional point-row disjunction and injective fresh-use behavior; "
        "no Function/effect semantics, source generation, or principal-scheme theorem"
    )


if __name__ == "__main__":
    main()
