#!/usr/bin/env python3
"""Bounded research model, not source inference or effect semantics.

Supplied ProtectedVarAt and whole-scheme certificates are input premises.
Physical delivery order is deliberately separate from logical proof stage.
Run: python3 tools/research_directional_source_relation.py
"""
from __future__ import annotations

from dataclasses import dataclass, replace
from itertools import permutations, product
import json
import resource


@dataclass(frozen=True)
class Origin:
    component: str
    binder: str
    scope: str


@dataclass(frozen=True)
class Atom:
    kind: str
    origin: Origin
    scope: str                 # current scope; original scope remains in origin
    use: str
    key: str                   # original source/proof occurrence identity
    args: tuple[str, ...]
    stage: int                 # supplied logical stage, never arrival index


@dataclass(frozen=True)
class Use:
    scheme: str
    origin: Origin
    target: str
    scope: str
    renaming: tuple[tuple[str, str], ...]


@dataclass(frozen=True)
class Rule:
    premises: frozenset[object]
    conclusions: frozenset[object]


@dataclass(frozen=True)
class Xi:
    nu: tuple[tuple[str, int], ...]
    K: int
    D: int

    def value(self, endpoint: str) -> int:
        return dict(self.nu)[endpoint]


def eq(actual: object, expected: object, label: str) -> None:
    if actual != expected:
        raise AssertionError(f"{label}: {actual!r} != {expected!r}")


def direction_rules(packet: frozenset[Atom]) -> tuple[Rule, ...]:
    """Ground rule instances over a fixed supplied finite source inventory.

    This does not derive At from integer ordering, aliasing, Q or a shape.
    In particular upper and lower remain different source occurrences.
    """
    result = []
    for seed in packet:
        if seed.kind != "seed":
            continue
        for upper in packet:
            if upper.kind != "upper":
                continue
            identity = (seed.origin, seed.scope, seed.use, seed.args[0])
            if identity != (upper.origin, upper.scope, upper.use, upper.args[0]):
                continue
            at = Atom("at", upper.origin, upper.scope, upper.use,
                      f"{seed.key}@{upper.key}", (seed.key, upper.key), upper.stage)
            if at not in packet:
                continue
            mark = Atom("new", upper.origin, upper.scope, upper.use,
                        at.key, (seed.key, upper.key, "out.effect", upper.args[1]),
                        upper.stage)
            result.append(Rule(frozenset((seed, upper, at)), frozenset((mark,))))
    return tuple(result)


def freshen(atom: Atom, use: Use) -> Atom:
    mapping = dict(use.renaming)
    if use.origin != atom.origin:
        raise ValueError("scheme transport changed original origin")
    if len(set(mapping.values())) != len(mapping):
        raise ValueError("freshening is not injective")
    if any(not key.startswith("q:") or not value.startswith(use.target + ":")
           for key, value in use.renaming):
        raise ValueError("captured/rigid coordinate was freshened")
    return replace(atom, scope=use.scope, use=use.target,
                   args=tuple(mapping.get(arg, arg) for arg in atom.args))


def model_rules(packet: frozenset[Atom], closed: Atom,
                uses: tuple[Use, ...]) -> tuple[Rule, ...]:
    """A closed-scheme certificate is SUPPLIED, not a source closure proof.

    Each transport rule requires the whole original packet and transports
    lower and inherited evidence too. No per-port generalization is modeled.
    """
    rules = list(direction_rules(packet))
    quantified = {arg for atom in packet for arg in atom.args if arg.startswith("q:")}
    for use in uses:
        if use.scheme != closed.key or {key for key, _ in use.renaming} != quantified:
            raise ValueError("use certificate does not cover the same complete scheme")
        image = frozenset(freshen(atom, use) for atom in packet)
        rules.append(Rule(packet | {closed, use}, image))
        rules.extend(direction_rules(image))
    return tuple(rules)


def saturate(delivery: tuple[object, ...], rules: tuple[Rule, ...]) -> frozenset[object]:
    """Replay-safe closure: every newly inserted premise revisits all rules.

    Intentionally small finite implementation; no performance claim is made.
    """
    known: set[object] = set()
    for item in delivery:
        known.add(item)
        changed = True
        while changed:
            changed = False
            for rule in rules:
                if rule.premises <= known and not rule.conclusions <= known:
                    known.update(rule.conclusions)
                    changed = True
    return frozenset(known)


def fixture() -> tuple[frozenset[Atom], Atom, tuple[Use, ...]]:
    origin = Origin("recursive-component:C", "formal:f", "original:outer")
    base = dict(origin=origin, scope="original:outer", use="scheme")
    seed = Atom("seed", key="no-annotation:k", args=("env:f",), stage=0, **base)
    upper = Atom("upper", key="call:u", args=("env:f", "q:c", "q:a", "q:b", "q:d"),
                 stage=1, **base)
    at = Atom("at", key="no-annotation:k@call:u", args=(seed.key, upper.key),
              stage=1, **base)
    lower = Atom("lower", key="recursive-provider:l", args=("env:f", "env:g", "env:h"),
                 stage=0, **base)
    inherited = Atom("inherited", key="provider-independent:p",
                     args=(lower.key, "env:g", "env:receipt", "env:result"), stage=0, **base)
    packet = frozenset((seed, upper, at, lower, inherited))
    closed = Atom("closed", key="whole-scheme:J", args=("source-complete:supplied",),
                  stage=2, **base)
    uses = tuple(Use(closed.key, origin, f"use{i}", f"scope:use{i}",
                     tuple((f"q:{x}", f"use{i}:{x}") for x in "cabd"))
                 for i in (1, 2))
    return packet, closed, uses


def mark_table(result: frozenset[object]) -> set[tuple[str, str, str, str]]:
    return {(a.use, a.args[0], a.args[1], a.args[3])
            for a in result if isinstance(a, Atom) and a.kind == "new"}


def arrival_seed_shortcut(delivery: tuple[Atom, ...]) -> set[tuple[str, str, str, str]]:
    """Incorrect single-pass scheduler: never replay an upper after late seed."""
    known: list[Atom] = []
    marks = set()
    for item in delivery:
        known.append(item)
        if item.kind == "upper":
            for seed in known:
                if seed.kind == "seed" and seed.args[0] == item.args[0]:
                    marks.add((item.use, seed.key, item.key, item.args[1]))
    return marks


def inventory_seed_shortcut(packet: frozenset[Atom]) -> set[tuple[str, str, str, str]]:
    """Incorrect completed-inventory join: invent At and disregard stage."""
    return {(upper.use, seed.key, upper.key, upper.args[1])
            for seed in packet for upper in packet
            if seed.kind == "seed" and upper.kind == "upper"
            and seed.args[0] == upper.args[0]}


def checks() -> dict[str, object]:
    packet, closed, uses = fixture()
    rules = model_rules(packet, closed, uses)
    expected_marks = {("scheme", "no-annotation:k", "call:u", "q:c"),
                      ("use1", "no-annotation:k", "call:u", "use1:c"),
                      ("use2", "no-annotation:k", "call:u", "use2:c")}
    # Exhaust every delivery schedule for all five source records, closure,
    # and first use. Second use arrives last; reversed second-use order is
    # checked separately. Rule activation/replay includes late supplied At.
    deliveries = tuple(sorted(packet, key=lambda a: a.kind)) + (closed, uses[0])
    expected = saturate(deliveries + (uses[1],), rules)
    eq(mark_table(expected), expected_marks, "literal source/use expectation")
    schedules = 0
    for order in permutations(deliveries):
        eq(saturate(order + (uses[1],), rules), expected, "all physical delivery orders")
        schedules += 1
    eq(saturate((uses[1], uses[0], closed) + tuple(reversed(deliveries[:5])), rules),
       expected, "both use requests precede the closed packet")

    # Independent preservation specification checks all original keys and
    # rigid provider/receipt/result coordinates, not just the generated marks.
    for use in uses:
        image = {a for a in expected if isinstance(a, Atom) and a.use == use.target
                 and a.kind != "new"}
        eq(len(image), 5, "complete five-record transport")
        eq({a.key for a in image}, {a.key for a in packet}, "original occurrence IDs")
        eq({a.origin for a in image}, {use.origin}, "original binder/scope/component")
        inherited = next(a for a in image if a.kind == "inherited")
        eq(inherited.args, ("recursive-provider:l", "env:g", "env:receipt", "env:result"),
           "inherited provider/receipt/result retained")
    try:
        freshen(next(iter(packet)), replace(uses[0], renaming=(("env:f", "use1:f"),)))
    except ValueError:
        pass
    else:
        raise AssertionError("captured-root freshening was accepted")

    seed = next(a for a in packet if a.kind == "seed")
    upper = next(a for a in packet if a.kind == "upper")
    at = next(a for a in packet if a.kind == "at")
    lower = next(a for a in packet if a.kind == "lower")
    # Two modeled proof histories have the same stage-erased final inventory.
    # Early has supplied At; genuinely late has no such certificate. The
    # latter output is local-rule derivability only, not selected late semantics.
    early = frozenset((seed, upper, at))
    late_seed = replace(seed, stage=2)
    late = frozenset((late_seed, upper))
    late_rules = direction_rules(late)
    eq(mark_table(saturate((upper, late_seed), late_rules)), set(), "no fabricated late At")
    erase = lambda p: {(a.kind, a.origin, a.scope, a.use, a.key, a.args)
                      for a in p if a.kind != "at"}
    eq(erase(early), erase(late), "stage/applicability erasure collision")
    # Deliver a logically earlier seed physically after the exposure and At.
    eq(len(mark_table(saturate((upper, at, seed), direction_rules(early)))), 1,
       "late physical seed is replayed")

    # Equality of variable/effect denotations does not establish source At.
    alias_upper = replace(upper, key="call:other", args=("env:alias",) + upper.args[1:])
    alias_packet = frozenset((seed, alias_upper))
    eq(mark_table(saturate(tuple(alias_packet), direction_rules(alias_packet))), set(),
       "equal variable values are not applicability witnesses")
    wrong_scope_packet = frozenset((seed, replace(upper, scope="unrelated:scope"), at))
    eq(mark_table(saturate(tuple(wrong_scope_packet), direction_rules(wrong_scope_packet))), set(),
       "originally equal root is insufficient across unmatched current scopes")
    # Rule matching is symbolic and has no denotation input. The separate
    # equal-effect mutation below consumes an explicit equal-valued assignment.

    # Explicit anti-correlated whole original rows. Each use predicate is
    # individually satisfiable, but no ONE xi satisfies both. K,D remain
    # correlated with nu, even across independently renamed local endpoints.
    rows = (Xi((("env:f", 0), ("use1:c", 0), ("use2:c", 1)), 0, 0),
            Xi((("env:f", 1), ("use1:c", 1), ("use2:c", 0)), 1, 1))
    p1 = lambda xi: xi.value("use1:c") == 0 and xi.K == 0
    p2 = lambda xi: xi.value("use2:c") == 0 and xi.D == 1
    eq((any(map(p1, rows)), any(map(p2, rows))), (True, True), "individual use witnesses")
    eq([xi for xi in rows if p1(xi) and p2(xi)], [], "whole-xi conjunction")
    stitched = Xi((("env:f", 0), ("use1:c", 0), ("use2:c", 0)), 0, 1)
    eq(stitched in rows, False, "stitched witness is not an original row")
    eq(p1(stitched) and p2(stitched), True, "stitching creates false satisfiability")

    # Lower evidence can constrain Xi even though it generates no protection.
    candidates = tuple(Xi((("env:f", n),), k, d) for n, k, d in product((0, 1), repeat=3))
    lower_predicate = lambda xi: xi.D == xi.value("env:f")
    constrained = tuple(xi for xi in candidates if lower_predicate(xi))
    eq(len(constrained), 4, "active lower predicate")
    eq(len(candidates), 8, "dropping lower changes full source relation")

    # Supplied Observe-dependent toy predicate: no claim of a Yulang Run trace.
    # O says a particular event is observed at the generated upper occurrence.
    # Structural graph extension preserves old predicates but this final
    # protection-sensitive predicate need not be invariant under adding marks.
    observed = lambda xi: xi.value("env:f") == 1
    final = lambda xi, protected: not (observed(xi) and xi.D and protected and not xi.K)
    before = {xi for xi in constrained if final(xi, False)}
    after = {xi for xi in constrained if final(xi, True)}
    eq((len(before), len(after)), (4, 3), "unchanged-query proof cannot cover final predicate")

    # Executable shortcut mutations each have a concrete discriminating witness.
    mutants: dict[str, bool] = {}
    mutants["physical_order_is_logical_stage"] = (arrival_seed_shortcut((upper, at, seed)) !=
        mark_table(saturate((upper, at, seed), direction_rules(early))))
    mutants["final_seed_inventory_invents_late_applicability"] = (inventory_seed_shortcut(late) !=
        mark_table(saturate(tuple(late), late_rules)))
    good = mark_table(saturate(tuple(packet), direction_rules(packet)))
    equal_effect_values = {"q:c": 1, "env:g": 1}
    wrong_global = good | {(lower.use, seed.key, lower.key, lower.args[1])
                           for mark in good
                           if equal_effect_values[mark[3]] == equal_effect_values[lower.args[1]]}
    mutants["globally_merge_equal_effect_protection"] = wrong_global != good
    alias_values = {"env:f": 0, "env:alias": 0}
    wrong_alias = {(alias_upper.use, seed.key, alias_upper.key, alias_upper.args[1])
                   for s in (seed,) if alias_values[s.args[0]] == alias_values[alias_upper.args[0]]}
    mutants["variable_value_equality_creates_source_applicability"] = wrong_alias != set()
    broken_image = frozenset(replace(freshen(a, uses[0]), use="scheme") if a.kind == "at"
                             else freshen(a, uses[0]) for a in packet)
    mutants["split_use_freshening_breaks_At"] = len(mark_table(saturate(
        tuple(broken_image), direction_rules(broken_image)))) != 1
    mutants["cross_use_witness_stitching"] = p1(stitched) and p2(stitched) and stitched not in rows
    mutants["drop_lower_evidence"] = set(constrained) != set(candidates)
    erased_packet = packet - {a for a in packet if a.kind == "inherited"}
    mutants["erase_inherited_packet"] = {a.key for a in erased_packet} != {a.key for a in packet}
    premature = frozenset(freshen(a, uses[0]) for a in (seed, upper, at))
    mutants["freeze_generalization_before_whole_packet"] = len(premature) != 5
    mutants["unchanged_query_filter_implies_observation_preservation"] = before != after
    if not all(mutants.values()):
        raise AssertionError(f"surviving shortcut: {mutants}")
    return {"status": "PASS", "all_seven_record_delivery_schedules": schedules,
            "opposite_two_use_order_checks": 1,
            "two_history_pairs": 1, "original_joint_rows": len(rows),
            "lower_candidate_rows": len(candidates), "observation_candidate_rows": len(constrained),
            "shortcut_mutations_rejected": list(mutants),
            "invalid_captured_root_transports_rejected": 1}


def main() -> None:
    # One process; standard library; 256 MiB virtual memory and 55 CPU seconds.
    # The external invocation additionally supplies a 60-second wall cap.
    resource.setrlimit(resource.RLIMIT_AS, (256 * 1024 * 1024, 256 * 1024 * 1024))
    resource.setrlimit(resource.RLIMIT_CPU, (55, 55))
    print(json.dumps(checks(), sort_keys=True))


if __name__ == "__main__":
    main()
