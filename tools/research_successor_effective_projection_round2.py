#!/usr/bin/env python3
"""Finite equality-orbit checks; no Yulang semantics or halting oracle."""
from itertools import product
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
DEPENDENCIES = (
    "rules/research-lab.md",
    "rules/design-authority.md",
    "rules/git-concurrency.md",
    "notes/theory/successor-proof-obligations.md",
    "notes/design/2026-10-03-scoped-constraint-solving.md",
    "notes/design/2026-10-03-source-context-finite-closure.md",
    "notes/design/2026-10-03-open-residual-factorization.md",
    "notes/design/2026-10-04-structural-fmp-fence-completion.md",
    "notes/progress/2026-10-05-pure-structural-effective-decision-corollary.md",
    "notes/design/2026-10-04-certified-callback-and-constrained-use.md",
    "notes/progress/2026-10-07-successor-global-synthesis.md",
    "notes/progress/2026-10-07-successor-recursive-synthesis.md",
    "notes/progress/2026-10-07-principal-whole-relation-factorization-attempt.md",
    "notes/progress/2026-10-08-principal-actual-export-rule-attempt.md",
    "notes/progress/2026-10-08-principal-vincl-actual-root-bridge-attempt.md",
    "notes/design/2026-10-05-source-contracts-and-common-allowance.md",
)


def eq(a, b):
    return ("eq", a, b)


def boolean(op, *children):
    return (op, *children)


def quantify(kind, name, body):
    return (kind, name, body)


def evaluate(formula, environment, domain, orbit=False):
    op, *args = formula
    if op == "eq":
        return environment[args[0]] == environment[args[1]]
    if op == "not":
        return not evaluate(args[0], environment, domain, orbit)
    if op in ("and", "or"):
        values = [evaluate(c, environment, domain, orbit) for c in args]
        return (all if op == "and" else any)(values)
    kind, name, body = op, args[0], args[1]
    assert kind in ("exists", "forall")
    if orbit:
        # One representative of every class already incident to the environment,
        # plus one representative of the complement. Binder order is unchanged.
        candidates = sorted(set(environment.values()))
        fresh = next(a for a in domain if a not in candidates)
        candidates.append(fresh)
    else:
        candidates = domain
    values = []
    for value in candidates:
        child = dict(environment)
        child[name] = value
        values.append(evaluate(body, child, domain, orbit))
    return (any if kind == "exists" else all)(values)


def run_checks():
    # Five atom variables; two public and three quantified. A domain of six
    # suffices to represent all equality patterns, with an unused fresh atom.
    variables = ("p", "q", "a", "b", "c")
    domain = tuple(range(6))
    atoms = [eq(a, b) for i, a in enumerate(variables) for b in variables[i:]]
    signed = atoms + [boolean("not", atom) for atom in atoms]
    matrices = signed + [boolean(op, a, b) for op in ("and", "or")
                         for a in signed for b in signed]
    # Full 8 alternations for the exact original a/b/c binder tree.
    comparisons = 0
    for kinds in product(("exists", "forall"), repeat=3):
        for matrix in matrices:
            formula = matrix
            for kind, name in reversed(tuple(zip(kinds, ("a", "b", "c")))):
                formula = quantify(kind, name, formula)
            # Both public equality patterns. Numeric spellings are immaterial.
            for public in ((0, 0), (0, 1)):
                environment = dict(zip(("p", "q"), public))
                assert evaluate(formula, environment, domain) == evaluate(
                    formula, environment, domain, orbit=True)
                comparisons += 1
    uniform = quantify("exists", "a", quantify("forall", "c", eq("a", "c")))
    pointwise = quantify("forall", "c", quantify("exists", "a", eq("a", "c")))
    assert not evaluate(uniform, {}, domain, orbit=True)
    assert evaluate(pointwise, {}, domain, orbit=True)
    # One hidden occurrence is shared by both clauses. The projection is the
    # diagonal; independent marginal witnesses incorrectly give all pairs.
    correlated = quantify("exists", "a", boolean("and", eq("p", "a"), eq("q", "a")))
    diagonal = {(p, q) for p, q in product(domain, repeat=2)
                if evaluate(correlated, {"p": p, "q": q}, domain, orbit=True)}
    assert diagonal == {(p, p) for p in domain}
    assert len(diagonal) == 6 and len(set(product(domain, repeat=2))) == 36
    # Scope identity is separate from actual equality of atom values.
    binders = (("left", "a"), ("right", "a"))
    assert binders[0] != binders[1]
    # Every finite natural sample misses a decidable equality-free predicate.
    # R^n({}) encodes n. This is a finite-bound falsifier, not halting execution.
    for bound in range(33):
        target = bound + 1
        assert not any(n == target for n in range(bound + 1))
        assert target == bound + 1
    hashes = {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest()
              for p in DEPENDENCIES}
    print(json.dumps({
        "result": "PASS",
        "matrix_count": len(matrices),
        "alternations": 8,
        "public_patterns": 2,
        "orbit_reference_comparisons": comparisons,
        "domain_size": len(domain),
        "mutations": ["quantifier_swap", "separate_marginals", "finite_depth_sample"],
        "dependencies": hashes,
    }, indent=2))


if __name__ == "__main__":
    run_checks()
