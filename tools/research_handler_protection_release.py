#!/usr/bin/env python3
"""Finite characterization of protection-only release at a typed slot.

This is a research model, not a source attribution rule.  Source component,
event lineage, row support, typed paths, and protection witnesses are supplied
as separate coordinates.  A marked output slot changes only whether its
matching protection witness participates in later handler eligibility.
"""

from dataclasses import dataclass
from itertools import product


@dataclass(frozen=True)
class Contribution:
    event: str
    source_component: str
    family: str
    lineage: tuple[str, ...]
    typed_path: tuple[str, ...]


@dataclass(frozen=True)
class Protection:
    event: str
    boundary: str
    slot: str


@dataclass(frozen=True)
class Case:
    contributions: tuple[Contribution, ...]
    protections: tuple[Protection, ...]
    marked_slot: str
    marked_component: str
    active_handlers: frozenset[str]
    covered_families: frozenset[str]


def release(case: Case) -> tuple[Contribution, ...]:
    """Compute the contribution view; this function never rewrites inputs."""
    # No contribution field or evidence is modified. The marker changes only
    # how an existing protection witness participates in eligibility.
    return case.contributions


def eligible(case: Case, contribution: Contribution, handler: str) -> bool:
    if handler not in case.active_handlers:
        return False
    if contribution.family not in case.covered_families:
        return False
    release_applies = (
        contribution.source_component == case.marked_component
    )
    still_protected = any(
        p.event == contribution.event
        and p.boundary == handler
        and not (release_applies and p.slot == case.marked_slot)
        for p in case.protections
    )
    return not still_protected


def family_wide_release(case: Case, contribution: Contribution, handler: str) -> bool:
    """Deliberately wrong: release every same-family protection."""
    if handler not in case.active_handlers:
        return False
    if contribution.family not in case.covered_families:
        return False
    still_protected = any(
        p.event == contribution.event
        and p.boundary == handler
        and not any(
            c.source_component == case.marked_component
            and c.family == contribution.family
            and p.slot == case.marked_slot
            for c in case.contributions
        )
        for p in case.protections
    )
    return not still_protected


def assert_frame(case: Case, after: tuple[Contribution, ...]) -> None:
    before_by_event = {c.event: c for c in case.contributions}
    after_by_event = {c.event: c for c in after}
    assert after_by_event == before_by_event
    assert {c.family for c in after} == {c.family for c in case.contributions}
    assert {c.typed_path for c in after} == {c.typed_path for c in case.contributions}
    assert {c.lineage for c in after} == {c.lineage for c in case.contributions}


def main() -> None:
    checked = 0
    for selected_component, handler_active in product(("e", "local"), (False, True)):
        contributions = (
            Contribution("input", selected_component, "foo",
                         ("origin-e" if selected_component == "e" else "origin-local",),
                         ("arg", "effect")),
            Contribution("same-family", "local", "foo", ("origin-local",),
                         ("body", "effect")),
        )
        # The model intentionally has one protection witness per event; stacked
        # or overlapping boundary composition is a separate open obligation.
        protections = (
            Protection("input", "receiver", "out"),
            Protection("same-family", "receiver", "out"),
        )
        active = frozenset({"receiver"}) if handler_active else frozenset()
        case = Case(contributions, protections, "out", "e", active,
                    frozenset({"foo"}))
        after = release(case)
        assert_frame(case, after)
        input_event = next(c for c in after if c.event == "input")
        local_event = next(c for c in after if c.event == "same-family")

        # Releasing the e-attributed receiver witness never relabels either
        # contribution, changes support, or releases a same-family local event.
        input_is_e = selected_component == "e"
        if not handler_active:
            assert not eligible(case, input_event, "receiver")
            assert not eligible(case, local_event, "receiver")
        elif input_is_e:
            assert eligible(case, input_event, "receiver")
        else:
            assert not eligible(case, input_event, "receiver")
        if handler_active:
            assert not eligible(case, local_event, "receiver")
        checked += 1

    # Resumed/shallow and higher-order latent cases are distinct dynamic
    # contributions that retain the same source lineage and typed result path.
    original = Contribution("q0", "e", "foo", ("source-e",), ("result", "latent"))
    resumed = Contribution("q1", "e", "foo", ("source-e", "resume-1"),
                           ("result", "latent"))
    assert original.event != resumed.event
    assert original.source_component == resumed.source_component
    assert original.family == resumed.family
    assert original.typed_path == resumed.typed_path
    # Mutation checks make the preservation boundary executable.
    witness = Case(
        (original, Contribution("local", "local", "foo", ("local",), ("body",))),
        (Protection("q0", "receiver", "out"), Protection("local", "receiver", "out")),
        "out", "e", frozenset({"receiver"}), frozenset({"foo"}),
    )
    local = next(c for c in witness.contributions if c.event == "local")
    assert not eligible(witness, local, "receiver")
    assert family_wide_release(witness, local, "receiver")
    assert eligible(witness, original, "receiver")
    def sticky_protection_mutant(c: Case, q: Contribution, handler: str) -> bool:
        if handler not in c.active_handlers or q.family not in c.covered_families:
            return False
        return not any(
            p.event == q.event and p.boundary == handler for p in c.protections
        )

    assert eligible(witness, original, "receiver")
    assert not sticky_protection_mutant(witness, original, "receiver")
    assert_frame(witness, release(witness))
    print(f"protection-release cases checked: {checked}")
    print("same-family local contribution remains protected and unchanged: confirmed")
    print("resumed event identity and source lineage remain separate: confirmed")
    print("family-wide and sticky-protection mutants rejected: confirmed")
    print("scope: one protection witness per event, supplied attribution/path evidence; no nested composition or Rel_C adequacy")


if __name__ == "__main__":
    main()
