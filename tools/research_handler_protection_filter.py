#!/usr/bin/env python3
"""Check the protection-only filter over supplied existing Inc_C witnesses.

The source-supplied release predicate is deliberately an input. This model
checks only how a released protection witness composes with the current
Protected/Grant/Visible equations; it does not derive attribution, release
timing, or protection witnesses from Yulang source.
"""

from dataclasses import dataclass
from itertools import product


@dataclass(frozen=True)
class IncidenceWitness:
    # A proof-witness index, not a semantic event/provenance identity.
    witness: int
    boundary: str
    profile_position: str
    incident: bool
    released: bool
    explicitly_admits: bool
    receiver_is_candidate_owner: bool


def protected(witnesses: tuple[IncidenceWitness, ...]) -> bool:
    return any(w.incident and not w.released for w in witnesses)


def grant(witnesses: tuple[IncidenceWitness, ...]) -> bool:
    # Release changes protection only. It does not remove Inc_C or Γ evidence.
    return any(
        w.incident and w.receiver_is_candidate_owner and w.explicitly_admits
        for w in witnesses
    )


def visible(active_handler: bool, active_owner: bool, covers: bool,
            witnesses: tuple[IncidenceWitness, ...]) -> bool:
    return (active_handler and active_owner and covers
            and (not protected(witnesses) or grant(witnesses)))


def wrong_filter_both_sides(active_handler: bool, active_owner: bool,
                            covers: bool,
                            witnesses: tuple[IncidenceWitness, ...]) -> bool:
    """Deliberately wrong: delete released Inc_C witnesses before both queries."""
    remaining = tuple(w for w in witnesses if not w.released)
    return (active_handler and active_owner and covers
            and (not protected(remaining) or grant(remaining)))


def main() -> None:
    checked = 0
    for states in product(product((False, True), repeat=3), repeat=3):
        witnesses = tuple(
            IncidenceWitness(
                witness=i,
                boundary=f"b{i}",
                profile_position=f"p{i}",
                incident=incident,
                released=released,
                explicitly_admits=admits,
                receiver_is_candidate_owner=True,
            )
            for i, (incident, released, admits) in enumerate(states)
        )
        for active_handler, active_owner, covers in product((False, True), repeat=3):
            before = witnesses
            result = visible(active_handler, active_owner, covers, witnesses)
            assert witnesses == before

            eligible = active_handler and active_owner and covers
            if not eligible:
                assert not result
            elif any(w.incident and not w.released for w in witnesses):
                assert result == grant(witnesses)
            else:
                # Once every applicable protection is released, ordinary
                # active-handler search needs no callback grant.
                assert result

            # Toggling release status cannot alter the grant relation.
            flipped = tuple(
                IncidenceWitness(w.witness, w.boundary, w.profile_position,
                                 w.incident, not w.released,
                                 w.explicitly_admits, w.receiver_is_candidate_owner)
                for w in witnesses
            )
            assert grant(flipped) == grant(witnesses)
            checked += 1

    # Two same-event Inc_C witnesses: a marked local boundary grants the
    # operation, while an independent inherited boundary remains protective.
    # Releasing protection must retain the local grant so it can discharge the
    # inherited protection under the existing no-origin-veto rule.
    overlap = (
        IncidenceWitness(0, "local", "marked-output", True, True, True, True),
        IncidenceWitness(1, "inherited", "input", True, False, False, False),
    )
    assert protected(overlap)
    assert grant(overlap)
    assert visible(True, True, True, overlap)
    assert not wrong_filter_both_sides(True, True, True, overlap)

    # Two derivations may have the same boundary/profile projection but differ
    # in whether they are selected by the source release rule. Keep the
    # unreleased proof witness; don't erase the tuple after one route qualifies.
    same_projection = (
        IncidenceWitness(0, "b", "p", True, True, False, False),
        IncidenceWitness(1, "b", "p", True, False, False, False),
    )
    assert protected(same_projection)
    assert not visible(True, True, True, same_projection)

    print(f"existing Inc_C witness combinations checked: {checked}")
    print("protection-only filtering preserves Grant and ordinary eligibility: confirmed")
    print("filtering released witnesses from both Protected and Grant is rejected: confirmed")
    print("overlapping proof witnesses retain unreleased protection independently: confirmed")
    print("scope: supplied Inc_C/release/admission evidence; no source attribution or timing derivation")


if __name__ == "__main__":
    main()
