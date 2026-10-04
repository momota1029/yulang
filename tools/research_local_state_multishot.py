#!/usr/bin/env python3
"""Finite challenge model for captured local State across raw resumptions.

Research only. The model combines the candidate visible-slot replacement law
from `research_local_state_restart.py` with the ordinary-computation contract
that a resumed continuation receives a reachable live state. It does not select
the missing Yulang State equations or model inference constraints.

Run: python3 tools/research_local_state_multishot.py
"""

from dataclasses import dataclass
from itertools import product


VALUES = (0, 1, 2)
ACTIVATIONS = ("outer", "inner")


@dataclass(frozen=True, order=True)
class Cell:
    slot: str
    activation: str


@dataclass(frozen=True)
class CapturedRead:
    cell: Cell


@dataclass(frozen=True)
class Store:
    cells: tuple[tuple[Cell, int], ...]

    def get(self, cell: Cell) -> int:
        return dict(self.cells)[cell]

    def replace(self, cell: Cell, value: int) -> "Store":
        updated = dict(self.cells)
        updated[cell] = value
        return Store(tuple(sorted(updated.items())))


def resume_assignment_then_read(
    captured: CapturedRead, live: Store, replacement: int
) -> tuple[Store, int]:
    """Candidate suffix: local replacement, then read through captured alias."""
    next_store = live.replace(captured.cell, replacement)
    return next_store, next_store.get(captured.cell)


def exhaustive_branch_isolation() -> int:
    cells = tuple(Cell("buffer", activation) for activation in ACTIVATIONS)
    checked = 0
    for initial_values in product(VALUES, repeat=len(cells)):
        base = Store(tuple(sorted(zip(cells, initial_values))))
        for target, sibling in product(cells, repeat=2):
            captured = CapturedRead(target)
            for left, right in product(VALUES, repeat=2):
                left_store, left_value = resume_assignment_then_read(captured, base, left)
                right_store, right_value = resume_assignment_then_read(captured, base, right)
                # Multi-shot branches begin from the supplied live state. One
                # branch's replacement cannot mutate the other branch's store.
                assert left_value == left
                assert right_value == right
                assert left_store.get(target) == left  # delayed left-branch read
                assert right_store.get(target) == right
                assert base.get(target) == initial_values[cells.index(target)]
                if target != sibling:
                    assert left_store.get(sibling) == base.get(sibling)
                    assert right_store.get(sibling) == base.get(sibling)
                checked += 1
    assert checked == 3**2 * 2**2 * 3**2
    return checked


def minimized_mutant_witnesses() -> tuple[tuple[int, int, int], tuple[int, int, int]]:
    for initial, replacement in product(VALUES, repeat=2):
        if initial != replacement:
            captured_snapshot = initial
            current_store_value = replacement
            stale_read = captured_snapshot
            assert stale_read != current_store_value
            stale = (initial, replacement, stale_read)
            break
    else:
        raise AssertionError("no snapshot-capture witness")

    for initial, first, second in product(VALUES, repeat=3):
        if first == second:
            continue
        # Deliberately wrong: both multi-shot branches share one mutable cell.
        shared_store = {"buffer": initial}
        shared_store["buffer"] = first
        branch_one_expected = shared_store["buffer"]
        shared_store["buffer"] = second
        branch_one_late_read = shared_store["buffer"]
        if branch_one_expected != branch_one_late_read:
            shared = (initial, first, second)
            break
    else:
        raise AssertionError("no cross-branch shared-store witness")
    return stale, shared


def main() -> None:
    checked = exhaustive_branch_isolation()
    stale, shared = minimized_mutant_witnesses()
    print(f"captured-read/resumption branch cases checked: {checked}")
    print("replacement visible through the captured slot in each branch: pass")
    print(f"snapshot-capture mutant witness: initial/replacement/read={stale}")
    print(f"cross-branch shared-store mutant: initial/first/second={shared}")
    print(
        "scope: candidate local State replacement plus supplied live-state "
        "resumptions only; no source equation, handler dispatch, or type theorem"
    )


if __name__ == "__main__":
    main()
