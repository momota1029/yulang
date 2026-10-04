#!/usr/bin/env python3
"""Probe immutable guard-context transport across residual decomposition.

This finite model assigns scope outcomes to paths in one structural
comparison. It checks that Function/Record decomposition and deferred open
residual solving keep the original context, and that guard failure remains
distinct from structural failure.

The path guard is synthetic and does not model lexical binders, production
generation, effects, or recursive descriptor graphs. It is a mutation-sensitive
characterization of the context-carry invariant only.

Run: python3 -B tools/research_residual_guard_context.py
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations


@dataclass(frozen=True, order=True)
class Atom:
    name: str


@dataclass(frozen=True, order=True)
class Var:
    name: str


@dataclass(frozen=True, order=True)
class Function:
    argument: "Type"
    result: "Type"


@dataclass(frozen=True, order=True)
class Record:
    fields: tuple[tuple[str, "Type"], ...]


Type = Atom | Var | Function | Record
Outcome = str
PATHS = (
    "root",
    "root.fun.arg",
    "root.fun.arg.record[a]",
    "root.fun.res",
    "root.fun.res.record[a]",
)


@dataclass(frozen=True)
class GuardContext:
    label: str
    allowed_paths: frozenset[str]


@dataclass(frozen=True)
class Residual:
    left: Type
    right: Type
    context: GuardContext
    path: str


@dataclass(frozen=True)
class Terminal:
    outcome: Outcome


@dataclass(frozen=True)
class Normalized:
    obligations: tuple[Residual | Terminal, ...]
    residuals: tuple[Residual, ...]
    visited: tuple[tuple[Type, Type, GuardContext, str], ...]
    outcome: Outcome


def guard_allows(context: GuardContext, path: str) -> bool:
    return path in context.allowed_paths


def structural_compare(
    left: Type,
    right: Type,
    context: GuardContext,
    path: str = "root",
) -> Outcome:
    if not guard_allows(context, path):
        return "GuardFailure"
    if isinstance(left, Atom) and isinstance(right, Atom):
        return "Success" if left == right else "StructuralFailure"
    if isinstance(left, Function) and isinstance(right, Function):
        argument = structural_compare(
            right.argument, left.argument, context, path + ".fun.arg"
        )
        if argument != "Success":
            return argument
        return structural_compare(left.result, right.result, context, path + ".fun.res")
    if isinstance(left, Record) and isinstance(right, Record):
        left_fields = dict(left.fields)
        if any(name not in left_fields for name, _ in right.fields):
            return "StructuralFailure"
        for name, child in right.fields:
            result = structural_compare(
                left_fields[name], child, context, path + f".record[{name}]"
            )
            if result != "Success":
                return result
        return "Success"
    return "StructuralFailure"


def substitute(ty: Type, assignment: dict[str, Type]) -> Type:
    if isinstance(ty, Var):
        return assignment[ty.name]
    if isinstance(ty, Function):
        return Function(substitute(ty.argument, assignment), substitute(ty.result, assignment))
    if isinstance(ty, Record):
        return Record(tuple((name, substitute(child, assignment)) for name, child in ty.fields))
    return ty


def normalize(left: Type, right: Type, context: GuardContext) -> Normalized:
    residuals: list[Residual] = []
    obligations: list[Residual | Terminal] = []
    visited: list[tuple[Type, Type, GuardContext, str]] = []

    def visit(lower: Type, upper: Type, path: str) -> Outcome:
        visited.append((lower, upper, context, path))
        if not guard_allows(context, path):
            obligations.append(Terminal("GuardFailure"))
            return "GuardFailure"
        if isinstance(lower, Var) or isinstance(upper, Var):
            residual = Residual(lower, upper, context, path)
            residuals.append(residual)
            obligations.append(residual)
            return "Success"
        if isinstance(lower, Atom) and isinstance(upper, Atom):
            result = "Success" if lower == upper else "StructuralFailure"
            if result != "Success":
                obligations.append(Terminal(result))
            return result
        if isinstance(lower, Function) and isinstance(upper, Function):
            argument = visit(upper.argument, lower.argument, path + ".fun.arg")
            if argument != "Success":
                return argument
            return visit(lower.result, upper.result, path + ".fun.res")
        if isinstance(lower, Record) and isinstance(upper, Record):
            lower_fields = dict(lower.fields)
            if any(name not in lower_fields for name, _ in upper.fields):
                obligations.append(Terminal("StructuralFailure"))
                return "StructuralFailure"
            for name, child in upper.fields:
                result = visit(
                    lower_fields[name], child, path + f".record[{name}]"
                )
                if result != "Success":
                    return result
            return "Success"
        obligations.append(Terminal("StructuralFailure"))
        return "StructuralFailure"

    outcome = visit(left, right, "root")
    return Normalized(tuple(obligations), tuple(residuals), tuple(visited), outcome)


def solve_normalized(
    form: Normalized,
    assignment: dict[str, Type],
    *,
    reset_residual_context: GuardContext | None = None,
) -> Outcome:
    for obligation in form.obligations:
        if isinstance(obligation, Terminal):
            return obligation.outcome
        residual = obligation
        context = reset_residual_context or residual.context
        result = structural_compare(
            substitute(residual.left, assignment),
            substitute(residual.right, assignment),
            context,
            residual.path,
        )
        if result != "Success":
            return result
    return "Success"


def check_all_guard_masks():
    left = Function(Atom("Int"), Var("x"))
    right = Function(Atom("Int"), Record((("a", Atom("Int")),)))
    assignment = {"x": Record((("a", Atom("Int")),))}
    checked = 0
    outcomes = {"Success": 0, "GuardFailure": 0, "StructuralFailure": 0}
    for count in range(len(PATHS) + 1):
        for allowed in combinations(PATHS, count):
            context = GuardContext("same-context", frozenset(allowed))
            direct = structural_compare(
                substitute(left, assignment), substitute(right, assignment), context
            )
            form = normalize(left, right, context)
            normalized = solve_normalized(form, assignment)
            assert all(item[2] is context for item in form.visited)
            assert all(residual.context is context for residual in form.residuals)
            assert normalized == direct, (allowed, direct, normalized, form)
            outcomes[direct] += 1
            checked += 1
    assert checked == 2 ** len(PATHS) == 32
    return checked, outcomes


def minimum_context_reset_witness():
    lower = Function(Atom("Int"), Var("x"))
    upper = Function(Atom("Int"), Record((("a", Atom("Int")),)))
    assignment = {"x": Record((("a", Atom("Int")),))}
    original = GuardContext("original", frozenset(PATHS))
    reset = GuardContext(
        "reset-mutant", frozenset(path for path in PATHS if path != PATHS[-1])
    )
    form = normalize(lower, upper, original)
    direct = structural_compare(
        substitute(lower, assignment), substitute(upper, assignment), original
    )
    retained = solve_normalized(form, assignment)
    mutant = solve_normalized(form, assignment, reset_residual_context=reset)
    assert direct == retained == "Success"
    assert mutant == "GuardFailure"
    assert len(form.residuals) == 1
    assert form.residuals[0].path == "root.fun.res"
    assert form.residuals[0].context is original
    return lower, upper, assignment, original, reset, direct, mutant


def check_failure_distinction():
    mismatch = (Atom("Int"), Atom("Bool"))
    denied = GuardContext("denied-root", frozenset())
    admitted = GuardContext("admitted-root", frozenset({"root"}))
    guard_failure = structural_compare(*mismatch, denied)
    structural_failure = structural_compare(*mismatch, admitted)
    assert guard_failure == "GuardFailure"
    assert structural_failure == "StructuralFailure"
    return guard_failure, structural_failure


def check_deferred_failure_precedence():
    # Function argument comparison creates an open residual before the result
    # comparison encounters a known head mismatch. The residual's field guard
    # is checked first after assignment, so it must keep precedence.
    lower = Function(Var("x"), Atom("Int"))
    upper = Function(Var("y"), Atom("Bool"))
    assignment = {
        "x": Record((("a", Atom("Int")),)),
        "y": Record((("a", Atom("Int")),)),
    }
    checked = 0
    outcomes = {"Success": 0, "GuardFailure": 0, "StructuralFailure": 0}
    for count in range(len(PATHS) + 1):
        for allowed in combinations(PATHS, count):
            context = GuardContext("deferred-order", frozenset(allowed))
            direct = structural_compare(
                substitute(lower, assignment), substitute(upper, assignment), context
            )
            form = normalize(lower, upper, context)
            normalized = solve_normalized(form, assignment)
            assert normalized == direct, (allowed, direct, normalized, form)
            outcomes[direct] += 1
            checked += 1

    # Small witness for the old fail-fast model: it stopped at the later
    # concrete result mismatch and erased the earlier residual guard check.
    context = GuardContext(
        "deny-earlier-field",
        frozenset({"root", "root.fun.arg", "root.fun.res"}),
    )
    form = normalize(lower, upper, context)
    direct = structural_compare(
        substitute(lower, assignment), substitute(upper, assignment), context
    )
    assert form.outcome == "StructuralFailure"  # symbolic, fail-fast summary
    assert direct == solve_normalized(form, assignment) == "GuardFailure"
    assert len(form.residuals) == 1
    assert form.obligations[0] == form.residuals[0]
    assert form.obligations[-1] == Terminal("StructuralFailure")
    return checked, outcomes, lower, upper, assignment, context, form, direct


def main() -> None:
    checked, outcomes = check_all_guard_masks()
    lower, upper, assignment, original, reset, direct, mutant = minimum_context_reset_witness()
    guard_failure, structural_failure = check_failure_distinction()
    precedence_checked, precedence_outcomes, plower, pupper, passignment, pcontext, pform, poutcome = (
        check_deferred_failure_precedence()
    )
    print(f"path-guard masks checked: {checked}; outcomes: {outcomes}")
    print("direct and same-context residual judgment agree for every mask")
    print(
        "context-reset mutant: "
        f"{lower} <: {upper}, x={assignment['x']}, context={original.label}; "
        f"direct={direct}, reset-to-{reset.label}={mutant}"
    )
    print(
        "failure ordering retained: denied root gives "
        f"{guard_failure}; admitted mismatched heads give {structural_failure}"
    )
    print(
        f"deferred-failure precedence: {precedence_checked} path masks, "
        f"outcomes={precedence_outcomes}; "
        f"{plower} <: {pupper}, assignment={passignment}, "
        f"context={pcontext.label}; ordered result={poutcome}, "
        f"terminal symbolic result={pform.outcome}"
    )
    print(
        "scope: five synthetic comparison paths in one acyclic Function/Record "
        "bound; no lexical scope semantics, production guard generator, "
        "recursive graph, effects, or solver integration"
    )


if __name__ == "__main__":
    main()
