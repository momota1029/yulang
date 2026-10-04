#!/usr/bin/env python3
"""Finite source-state probe for visible StateSlot restart and capture.

The model takes the already specified declaration-origin StateSlotId,
alias/capture transport, and pure-continuation-restart description, then makes
one explicit *candidate* source-state assumption: a runtime activation is
identified separately from the static slot, and restart substitutes the new
value into the live activation. The repository does not yet specify these
source-step equations. It deliberately excludes handlers, raw resumption,
general first-class refs, and source type interpretation.

The exhaustive traces check that slot-keyed replacement is visible through
captured aliases, while two tempting mutants (capture-by-value and using the
static slot ID as the runtime cell key) fail on minimized traces.

Run: python3 tools/research_local_state_restart.py
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product


VALUES = (0, 1)
SLOTS = ("s0", "s1")
ACTIVATIONS = ("a0", "a1")


@dataclass(frozen=True, order=True)
class RuntimeCell:
    # Declaration-origin identity and runtime activation are separate.
    slot: str
    activation: str


@dataclass(frozen=True)
class Alias:
    cell: RuntimeCell


@dataclass(frozen=True)
class SnapshotAlias:
    value: int


def capture(alias: Alias) -> Alias:
    """Capture the visible slot reference, retaining its runtime identity."""
    return Alias(alias.cell)


def restart_update(
    store: dict[RuntimeCell, int],
    target: Alias,
    replacement: int,
) -> dict[RuntimeCell, int]:
    """Pure continuation restart represented by replacing the live cell."""
    updated = dict(store)
    updated[target.cell] = replacement
    return updated


def exhaust_capture_and_activation_laws() -> int:
    checked = 0
    cells = tuple(RuntimeCell(s, a) for s, a in product(SLOTS, ACTIVATIONS))
    aliases = tuple(Alias(cell) for cell in cells)
    # Every initial store, captured alias, update target, and replacement.
    for values in product(VALUES, repeat=len(cells)):
        store = dict(zip(cells, values))
        for source_alias, target, replacement in product(aliases, aliases, VALUES):
            captured = capture(source_alias)
            after = restart_update(store, target, replacement)
            # Every alias to the updated runtime cell observes the replacement.
            for observer in aliases:
                observed = after[observer.cell]
                expected = replacement if observer.cell == target.cell else store[observer.cell]
                assert observed == expected
            # Same static declaration in another activation is not the cell.
            sibling_activation = RuntimeCell(
                target.cell.slot,
                ACTIVATIONS[1] if target.cell.activation == ACTIVATIONS[0] else ACTIVATIONS[0],
            )
            assert after[sibling_activation] == store[sibling_activation]
            # Capturing then using an alias preserves its complete target.
            assert captured == source_alias
            assert after[captured.cell] == after[source_alias.cell]
            checked += 1
    assert checked == 2**4 * 4 * 4 * 2
    return checked


def minimal_capture_by_value_failure() -> tuple[int, int]:
    # Smallest stale-capture trace: initialize, capture, update, read.
    for initial, replacement in product(VALUES, repeat=2):
        captured = SnapshotAlias(initial)
        current = replacement  # continuation restart updates the visible slot
        if captured.value != current:
            return captured.value, current
    raise AssertionError("capture-by-value mutant unexpectedly passed")


def minimal_static_id_as_cell_failure() -> tuple[RuntimeCell, RuntimeCell, int, int]:
    # Wrongly keying by StateSlotId merges two dynamic activations.
    for slot, first, second, before, replacement in product(
        SLOTS, ACTIVATIONS, ACTIVATIONS, VALUES, VALUES
    ):
        if first == second:
            continue
        left, right = RuntimeCell(slot, first), RuntimeCell(slot, second)
        store = {left: before, right: before}
        after = restart_update(store, Alias(left), replacement)
        mutant = {slot: before}
        mutant[slot] = replacement
        if after[right] != mutant[slot]:
            return left, right, after[right], mutant[slot]
    raise AssertionError("static-ID-key mutant unexpectedly passed")


def main() -> None:
    checked = exhaust_capture_and_activation_laws()
    old, new = minimal_capture_by_value_failure()
    left, right, correct_sibling, mutant_sibling = minimal_static_id_as_cell_failure()
    assert old != new
    assert left.slot == right.slot and left.activation != right.activation
    assert correct_sibling != mutant_sibling
    print(f"visible alias/restart/activation states checked: {checked}")
    print("slot-keyed replacement remains visible through captured aliases: pass")
    print(f"minimal capture-by-value failure: captured={old}, after-update={new}")
    print(
        "minimal static-ID/runtime-cell conflation: "
        f"cells=({left}, {right}), sibling correct={correct_sibling}, "
        f"mutant={mutant_sibling}"
    )
    print(
        "scope: finite visible local StateSlot core only; no handler/resumption, "
        "type relation, general ref, or source-wide EnvStore theorem"
    )


if __name__ == "__main__":
    main()
