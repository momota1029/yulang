#!/usr/bin/env python3
"""Probe scalar widening through a package's retained callable consumer.

Two source challenges contain correlated scalar/callable pairs. The callback
returns the package unchanged, and a later client invokes its callable with
the returned scalar. A local scalar-saturation rule widens only the returned
integer while preserving callable identity. This checker asks whether that
local widening remains projection-exact after the dependent future call.

The finite result is intentionally only a characterization: a widened scalar
can change the future request selected by the retained callable. The checked
relation still contains every source observation, but strict equality fails.
An over-broad package mutant also swaps the callable owner while retaining the
original challenge, yielding a separate wrong-origin event.

Run: python3 tools/research_callback_nested_value_projection.py
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product


FIBER = ("nu-mixed", "K-mixed", "D-mixed")
SCOPE = "callback-package-result"
PACKAGE_PATH = "J_call/result/package"
CALLABLE_PATH = "J_call/result/package/function"
SCALARS = (0, 1)
OWNERS = ("callable-left", "callable-right")
OWNER_SCALAR = {"callable-left": 0, "callable-right": 1}
INTERFACE = "Fun(Int, [Read, Write], Int)"
OPERATION_BY_SCALAR = {0: "Read", 1: "Write"}


@dataclass(frozen=True, order=True)
class PackageValue:
    scalar: int
    callable_owner: str


@dataclass(frozen=True, order=True)
class Observation:
    fiber: tuple[str, str, str]
    binder_scope: str
    package_path: str
    callable_path: str
    input_scalar: int
    input_callable_owner: str
    result_scalar: int
    result_callable_owner: str
    result_callable_interface: str
    invoked_argument: int
    operation: str
    request_origin: str
    event_id: str
    continuation_owner: str


@dataclass(frozen=True, order=True)
class Lifted:
    old: Observation
    # These new coordinates are total functions of the complete old tuple.
    challenge_projection: tuple[object, ...]
    result_projection: tuple[object, ...]


def later_call(owner: str, argument: int) -> tuple[str, str, str, str]:
    """The retained callable's behavior exposes its argument in the trace."""
    operation = OPERATION_BY_SCALAR[argument]
    event = f"event:{owner}:arg-{argument}"
    origin = f"request-origin:{owner}:arg-{argument}"
    continuation = f"continuation:{owner}"
    return operation, origin, event, continuation


def observe(challenge: PackageValue, result: PackageValue) -> Observation:
    operation, origin, event, continuation = later_call(
        result.callable_owner, result.scalar
    )
    return Observation(
        FIBER,
        SCOPE,
        PACKAGE_PATH,
        CALLABLE_PATH,
        challenge.scalar,
        challenge.callable_owner,
        result.scalar,
        result.callable_owner,
        INTERFACE,
        result.scalar,
        operation,
        origin,
        event,
        continuation,
    )


def source_identity(challenge: PackageValue) -> frozenset[Observation]:
    """Identity returns the same package; the later call uses its scalar."""
    return frozenset({observe(challenge, challenge)})


def ground_only_saturation(challenge: PackageValue) -> frozenset[Observation]:
    """Widen scalar data while keeping this challenge's callable owner."""
    return frozenset(
        observe(challenge, PackageValue(scalar, challenge.callable_owner))
        for scalar in SCALARS
    )


def whole_package_saturation(challenge: PackageValue) -> frozenset[Observation]:
    """Mutant: independently widen both result coordinates, same challenge."""
    return frozenset(
        observe(challenge, PackageValue(scalar, owner))
        for scalar, owner in product(SCALARS, OWNERS)
    )


def typed_projection(row: Observation) -> tuple[object, ...]:
    """Erase scalar coordinates but retain later typed effect evidence."""
    return (
        row.fiber,
        row.binder_scope,
        row.package_path,
        row.callable_path,
        row.input_callable_owner,
        row.result_callable_owner,
        row.result_callable_interface,
        row.operation,
        row.request_origin,
        row.event_id,
        row.continuation_owner,
    )


def total_lift(row: Observation) -> Lifted:
    return Lifted(
        row,
        (row.input_callable_owner, row.package_path, row.event_id),
        (row.result_scalar, row.result_callable_owner, row.continuation_owner),
    )


def erase_lift(rows: frozenset[Lifted]) -> frozenset[Observation]:
    return frozenset(row.old for row in rows)


def exhaustive_check() -> tuple[
    int,
    int,
    int,
    tuple[PackageValue, Observation],
    tuple[PackageValue, Observation],
]:
    # The finite source domain contains two correlated package shapes; scalar
    # and callable owner are not independently challengeable in source.
    challenges = tuple(
        PackageValue(OWNER_SCALAR[owner], owner) for owner in OWNERS
    )
    cases = 0
    source_in_checked = 0
    equal_after_projection = 0
    scalar_extra_count = 0
    package_extra_count = 0
    minimal_scalar_extra: tuple[PackageValue, Observation] | None = None
    minimal_package_extra: tuple[PackageValue, Observation] | None = None

    for challenge in challenges:
        actual = source_identity(challenge)
        ground = ground_only_saturation(challenge)
        broad = whole_package_saturation(challenge)
        actual_projection = {typed_projection(row) for row in actual}
        ground_projection = {typed_projection(row) for row in ground}
        broad_projection = {typed_projection(row) for row in broad}

        assert actual <= ground <= broad
        assert actual_projection <= ground_projection <= broad_projection
        assert all(row.input_callable_owner == challenge.callable_owner for row in broad)

        lifted = frozenset(total_lift(row) for row in ground)
        assert erase_lift(lifted) == ground
        assert all(row.old.fiber == FIBER and row.old.binder_scope == SCOPE for row in lifted)
        assert all(row.old.input_callable_owner == challenge.callable_owner for row in lifted)

        source_in_checked += int(actual_projection <= ground_projection)
        equal_after_projection += int(actual_projection == ground_projection)
        scalar_extras = [row for row in ground if typed_projection(row) not in actual_projection]
        package_extras = [row for row in broad if typed_projection(row) not in ground_projection]
        if scalar_extras:
            scalar_extra_count += len(scalar_extras)
            extra = min(scalar_extras)
            if minimal_scalar_extra is None or (
                challenge.callable_owner,
                extra.result_scalar,
            ) < (
                minimal_scalar_extra[0].callable_owner,
                minimal_scalar_extra[1].result_scalar,
            ):
                minimal_scalar_extra = (challenge, extra)
        if package_extras:
            package_extra_count += len(package_extras)
            extra = min(package_extras)
            if minimal_package_extra is None or (
                challenge.callable_owner,
                extra.result_callable_owner,
                extra.result_scalar,
            ) < (
                minimal_package_extra[0].callable_owner,
                minimal_package_extra[1].result_callable_owner,
                minimal_package_extra[1].result_scalar,
            ):
                minimal_package_extra = (challenge, extra)
        cases += 1

    assert cases == 2
    assert source_in_checked == cases
    assert equal_after_projection == 0
    assert scalar_extra_count == 2
    assert package_extra_count == 4
    assert minimal_scalar_extra is not None
    assert minimal_package_extra is not None
    return (
        cases,
        source_in_checked,
        scalar_extra_count,
        minimal_scalar_extra,
        minimal_package_extra,
    )


def main() -> None:
    cases, included, scalar_extras, scalar_failure, package_failure = exhaustive_check()
    challenge, extra = scalar_failure
    package_challenge, package_extra = package_failure
    assert challenge == PackageValue(0, "callable-left")
    assert extra.result_scalar == 1
    assert extra.result_callable_owner == "callable-left"
    assert extra.operation == "Write"
    assert extra.input_callable_owner == "callable-left"
    print(f"correlated package challenges checked: {cases}")
    print(f"source projection included in ground-only checked projection: {included}/{cases}")
    print(f"ground-only checked projection has extra future-call observations: {scalar_extras}")
    print("old-tuple total-coordinate extension erases back to the same checked relation: pass")
    print(
        "minimum ground-only extra: fixed input=(0, callable-left), result scalar=1; "
        "retained callable emits Write, while source identity emits Read"
    )
    print(
        "minimum whole-package owner-swap extra: "
        f"input=({package_challenge.scalar}, {package_challenge.callable_owner}), "
        f"result=({package_extra.result_scalar}, {package_extra.result_callable_owner}), "
        f"origin={package_extra.request_origin}"
    )
    print(
        "scope: two correlated package challenges, one later call, one fixed fiber; "
        "no production membership rule, arbitrary handler trace, or theorem"
    )


if __name__ == "__main__":
    main()
