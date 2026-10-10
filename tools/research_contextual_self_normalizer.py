#!/usr/bin/env python3
"""Exact bare identity-self factoring; research only, not a recursive solver.

See notes/progress/2026-10-10-contextual-self-edge-normalizer.md. One ID,
fixed family, natural full-pair counts, unguarded finite derivations. Constants,
all nonunit expression bracketing and lexical let/bound sharing survive.
Unlike debt.Grammar, this transformation admits raw/PUSH facts and mix.
The stable dependency supplies only operation/values, with no count clipping.
The finite-fixture checker below requires a proved finite pre-fixed witness;
it is neither an algorithm for finding one nor a general termination claim.
"""
from itertools import product
import hashlib
import json
from pathlib import Path
import time

import research_mixed_debt_observer as debt

DEPENDENCY_SHA = 'c6f3d36462469494dcdaa5fd6e22029bcea0f5d48a258e5eb55bc41a65dfaf6c'
I = ('const', 0, 0, 0)


def validate_expression(e, names, scope=frozenset()):
    """The exact full tuple DSL, excluding observer holes in productions."""
    arities = {'const': 4, 'ref': 2, 'replay': 3, 'mix': 2, 'swap': 2,
               'both_from_right': 2, 'identity': 2, 'prefix': 4,
               'suffix': 3, 'let': 4, 'bound': 2}
    if not isinstance(e, tuple) or not e or e[0] not in arities or len(e) != arities[e[0]]:
        raise ValueError('invalid exact tuple expression')
    tag = e[0]
    if tag == 'const':
        for count in e[1:]: debt.nat(count)
    elif tag == 'ref':
        if not isinstance(e[1], str) or e[1] not in names:
            raise ValueError('unknown nonterminal')
    elif tag == 'bound':
        if not isinstance(e[1], str) or e[1] not in scope:
            raise ValueError('unbound lexical variable')
    elif tag == 'let':
        if (not isinstance(e[1], str) or not e[1]
                or not isinstance(e[2], str) or e[2] not in names):
            raise ValueError('invalid shared supplier')
        validate_expression(e[3], names, scope | {e[1]})
    elif tag == 'prefix':
        debt.nat(e[1]); debt.nat(e[2])
        validate_expression(e[3], names, scope)
    elif tag == 'suffix':
        debt.nat(e[1]); validate_expression(e[2], names, scope)
    else:
        for child in e[1:]: validate_expression(child, names, scope)


def snapshot(rules):
    """Materialize the outer iterators once; inner expressions must be tuples."""
    rules = tuple((name, tuple(productions)) for name, productions in rules)
    names = tuple(name for name, _ in rules)
    if (any(not isinstance(name, str) or not name for name in names)
            or len(set(names)) != len(names)):
        raise ValueError('invalid or duplicate nonterminal')
    for _, productions in rules:
        for expression in productions: validate_expression(expression, set(names))
    return rules


def is_identity_self(name, e):
    """Recognize only a bare M-self: actual I, not merely mix(label)==I."""
    ref = ('ref', name)
    return (e == ('mix', ref) or e == ('replay', ref, I)
            or e == ('replay', I, ref))


def is_plain_self(name, e):
    return e == ('ref', name)


def factor_identity_self(rules):
    """Pure finite transformation preserving every node's exact value set.

    For each owner with a bare identity self, remove those productions.
    Retain each other E and add mix(E). No stored-fact-normality premise,
    quotient, debt cap, source restriction or recursive saturation is used.
    Keep the original immutable snapshot for future producer changes/rollback.
    """
    original = snapshot(rules)
    output = []
    for name, productions in original:
        flagged = any(is_identity_self(name, e) for e in productions)
        remaining = tuple(e for e in productions
                          if not is_identity_self(name, e) and not is_plain_self(name, e))
        if flagged:
            derived = tuple(child for e in remaining for child in (e, ('mix', e)))
        else:
            derived = remaining
        output.append((name, derived))
    return tuple(output)


def add_original(original, name, expression):
    """Return a new original snapshot; callers derive its whole graph again."""
    original = snapshot(original)
    if name not in dict(original): raise ValueError('unknown owner')
    return snapshot((n, ps + (expression,) if n == name else ps) for n, ps in original)


def map_expression(e, mapping):
    """Row vertex renaming only; constants and lexical binder names unchanged."""
    tag = e[0]
    if tag == 'ref': return ('ref', mapping[e[1]])
    if tag == 'let': return ('let', e[1], mapping[e[2]], map_expression(e[3], mapping))
    if tag in ('const', 'bound'): return e
    if tag == 'prefix': return (*e[:3], map_expression(e[3], mapping))
    if tag == 'suffix': return (*e[:2], map_expression(e[2], mapping))
    return (tag, *(map_expression(child, mapping) for child in e[1:]))


def quotient_original(original, mapping):
    """Union original producers at new vertices, then callers must refactor.

    This implements a supplied pure row quotient, not an SCC decision or a
    production attachment map. Alias mapping does not touch attachment IDs.
    """
    original = snapshot(original)
    if set(mapping) != set(dict(original)):
        raise ValueError('quotient must map every original vertex')
    merged = {}
    for name, ps in original:
        merged.setdefault(mapping[name], []).extend(map_expression(e, mapping) for e in ps)
    return snapshot(merged.items())


def exact_finite_fixture(rules, witness):
    """Check a supplied finite pre-fixed set, then exhaust its exact closure.

    A witness is a finite upper bound proved closed under these productions.
    Closure checking makes every iterate a subset of that finite witness;
    monotone iteration therefore terminates without an iteration/debt cutoff.
    This helper is used only for the mathematically finite fixtures below.
    """
    rules = snapshot(rules)
    witness = {n: frozenset(ws) for n, ws in witness.items()}
    if set(witness) != set(dict(rules)): raise ValueError('missing fixture witness')
    for n, ps in rules:
        for e in ps:
            if not debt.values(e, witness, 'ref') <= witness[n]:
                raise ValueError('fixture witness is not pre-fixed')
    env = {n: set() for n, _ in rules}
    while True:
        changed = False
        for n, ps in rules:
            for e in ps:
                new = debt.values(e, env, 'ref') - env[n]
                if new:
                    env[n].update(new); changed = True
        if not changed: return {n: frozenset(ws) for n, ws in env.items()}


def active(e, x):
    return next(iter(debt.values(e, {'x': {x}}, 'hole')))[1] > 0


def separating_active_probe(a, b):
    """Finite boolean active-presence probe separating any distinct triples."""
    if a == b: raise ValueError('equal raw triples')
    x = ('hole', 'x')
    if a[0] != b[0]:
        extracted = ('mix', ('both_from_right', ('swap', x)))
        return ('replay', ('const', 0, 2 * min(a[0], b[0]) + 1, 0), extracted)
    if a[2] != b[2]:
        extracted = ('mix', ('both_from_right', x))
        return ('replay', ('const', 0, 2 * min(a[2], b[2]) + 1, 0), extracted)
    k = a[0] + a[2] + 1
    lower_output = min(a[1], b[1]) + 1
    return ('replay', ('replay', ('const', 0, k, 0), x),
            ('const', lower_output, 0, 0))


def main():
    start = time.monotonic()
    actual_sha = hashlib.sha256(Path(debt.__file__).read_bytes()).hexdigest()
    if actual_sha != DEPENDENCY_SHA: raise ValueError('stable dependency changed')
    checks = cases = 0
    def check(condition):
        nonlocal checks
        checks += 1
        assert condition, checks
    def compare(original, witness, expected=None):
        nonlocal cases
        cases += 1
        original = snapshot(original)
        transformed = factor_identity_self(original)
        before = exact_finite_fixture(original, witness)
        after = exact_finite_fixture(transformed, witness)
        check(before == after)
        if expected is not None: check(after == expected)
        check(all(not is_identity_self(n, e) for n, ps in transformed for e in ps))
        check(factor_identity_self(transformed) == transformed)
        for n, ps in original:
            left = sum(not is_identity_self(n, e) and not is_plain_self(n, e) for e in ps)
            check(len(dict(transformed)[n]) <= 2 * left)
        return transformed, after
    X = ('ref', 'X'); raw = ('const', 0, 1, 1)
    base = (('X', (raw, ('replay', X, I))),)
    two = {'X': frozenset(((0, 1, 1), (0, 0, 0)))}
    transformed, env = compare(base, two, two)
    naive = (('X', (raw,)),)
    check(exact_finite_fixture(naive, two) != env)
    check(dict(transformed)['X'][0] is raw)  # original tuple/payload retained
    for unit in (('replay', X, I), ('replay', I, X), ('mix', X)):
        compare((('X', (unit, raw)),), two, two)
    balanced_label = ('replay', X, raw)
    check(debt.mix(raw[1:]) == (0, 0, 0))
    check(not is_identity_self('X', balanced_label))
    compare((('X', (I, balanced_label)),), {'X': {(0, 0, 0)}})
    d = (1, 0, 0)
    check(debt.operation('replay', (d, raw[1:]), balanced_label) == (0, 0, 1))
    check(debt.mix(d) == d)
    compare((('X', (('mix', X),)),), {'X': set()}, {'X': frozenset()})
    compare((('X', ()),), {'X': set()}, {'X': frozenset()})
    compare((('X', (raw, ('replay', X, X), ('mix', X))),), two, two)
    compare((('X', (raw, ('ref', 'Y'), ('mix', X))),
             ('Y', (X,))), {'X': two['X'], 'Y': two['X']})
    # Late raw producer must be rewrapped from the original snapshot.
    original = snapshot((('X', (I, ('mix', X))),))
    old = factor_identity_self(original)
    extended = add_original(original, 'X', raw)
    compare(extended, two, two)
    check(original == snapshot((('X', (I, ('mix', X))),)))
    # Old I is already normal, so append-only happens to have I; use debt raw
    # seed with nonidentity mix output to expose the incorrect lifecycle.
    raw_debt = ('const', 1, 0, 1)
    debt_witness = {'X': {(0, 0, 0), (1, 0, 1), (0, 0, 2)}}
    late = add_original(original, 'X', raw_debt)
    late_graph, late_env = compare(late, debt_witness)
    append_only = add_original(old, 'X', raw_debt)
    check((0, 0, 2) in late_env['X'])
    check((0, 0, 2) not in exact_finite_fixture(append_only, debt_witness)['X'])
    # Supplied SCC quotient creates a bare self from a cross edge. Its new
    # raw producer belongs to an originally separate, unflagged owner.
    cross = snapshot((('A', (('replay', ('ref', 'B'), I),)),
                      ('B', (raw_debt, ('ref', 'A')))))
    q = quotient_original(cross, {'A': 'Q', 'B': 'Q'})
    check(is_identity_self('Q', dict(q)['Q'][0]))
    q_witness = {'Q': {(1, 0, 1), (0, 0, 2)}}
    q_graph, _ = compare(q, q_witness)
    check(('mix', raw_debt) in dict(q_graph)['Q'])
    # Quotienting already-derived owners also misses rewrapping the new raw
    # producer when one owner was flagged before the merge.
    before_merge = snapshot((('A', (I, ('mix', ('ref', 'A')))), ('B', (raw_debt,))))
    merged = quotient_original(before_merge, {'A': 'Q', 'B': 'Q'})
    merged_witness = {'Q': debt_witness['X']}
    _, merged_env = compare(merged, merged_witness)
    wrong_merge = quotient_original(factor_identity_self(before_merge), {'A': 'Q', 'B': 'Q'})
    check((0, 0, 2) not in exact_finite_fixture(wrong_merge, merged_witness)['Q'])
    check((0, 0, 2) in merged_env['Q'])
    # Injective fresh vertex renaming commutes exactly, preserving constants.
    renaming = {'X': 'X_fresh'}
    check(factor_identity_self(quotient_original(extended, renaming)) ==
          quotient_original(factor_identity_self(extended), renaming))
    check(dict(quotient_original(extended, renaming))['X_fresh'][-1] is raw)
    # Correlated bound choices survive root factoring; independent ref uses
    # remain independent. Add shadowed let suppliers with restored scope.
    l = ('const', 1, 0, 0); r = ('const', 0, 0, 1); t = ('bound', 't')
    shared = ('let', 't', 'T', ('replay', t, ('swap', t)))
    independent = ('replay', ('ref', 'T'), ('swap', ('ref', 'T')))
    shadow = ('let', 't', 'A', ('replay', ('let', 't', 'B', t), t))
    shared_rules = (('T', (l, r)), ('A', (l,)), ('B', (('const', 0, 0, 2),)),
                    ('S', (shared, ('mix', ('ref', 'S')))),
                    ('N', (independent, ('mix', ('ref', 'N')))),
                    ('H', (shadow, ('mix', ('ref', 'H')))))
    sharing_witness = {'T': {(1, 0, 0), (0, 0, 1)}, 'A': {(1, 0, 0)},
                       'B': {(0, 0, 2)}, 'S': {(0, 0, 2)},
                       'N': {(2, 0, 0), (0, 0, 2)}, 'H': {(0, 0, 3)}}
    _, sharing_env = compare(shared_rules, sharing_witness)
    check(sharing_env['S'] < sharing_env['N'])
    check(sharing_env['H'] == frozenset(((0, 0, 3),)))
    compare((('E', ()), ('X', (('let', 't', 'E', raw), ('mix', X)))),
            {'E': set(), 'X': set()})
    # An infinite raw supplier is accepted structurally. Never saturate it:
    # U has exactly (0,1,1+j), j>=0, by its suffix recurrence.
    infinite = snapshot((('U', (raw, ('suffix', 1, ('ref', 'U')))),
                         ('X', (('ref', 'U'), ('mix', X)))))
    infinite_factored = factor_identity_self(infinite)
    check(dict(infinite_factored)['U'] == dict(infinite)['U'])
    check(dict(infinite_factored)['X'] == (('ref', 'U'), ('mix', ('ref', 'U'))))
    # Arbitrary raw/PUSH wrappers and retained bracketed operations, finite DAG.
    wrappers = (('prefix', 2, 3, ('ref', 'T')),
                ('suffix', 4, ('ref', 'T')),
                ('replay', ('swap', ('ref', 'T')), ('both_from_right', ('ref', 'T'))))
    seeds = (raw, raw_debt, ('const', 2, 3, 1))
    source_values = {e[1:] for e in seeds}
    output_values = set().union(*(debt.values(e, {'T': source_values}, 'ref') for e in wrappers))
    output_values |= {debt.mix(w) for w in tuple(output_values)}
    compare((('T', seeds), ('X', wrappers + (('mix', X),))),
            {'T': source_values, 'X': output_values})
    # Small finite-closing exhaustive family; no arbitrary recursive search.
    for p, n, rcount in product(range(3), repeat=3):
        seed = ('const', p, n, rcount)
        w = seed[1:]
        witness = {'X': {w, debt.mix(w)}}
        for unit in (('mix', X), ('replay', X, I), ('replay', I, X)):
            compare((('X', (unit, seed)),), witness)
    compare((('X', (X,)),), {'X': set()})
    compare((('X', (X, raw, ('mix', X))),), two, two)
    triples = tuple(product(range(4), repeat=3))
    for a in triples:
        check(debt.mix(debt.mix(a)) == debt.mix(a))
        for b in triples:
            if a != b:
                probe = separating_active_probe(a, b)
                check(active(probe, a) != active(probe, b))
    # Rollback is immutable pair restoration, not mutation of a memo/flag.
    saved = (original, old)
    current = (late, late_graph)
    current = saved
    check(current[0] == original and current[1] == factor_identity_self(current[0]))
    invalid = [(('X', (('const', 0, -1, 0),)),),
               (('X', (('ref', 'missing'),)),),
               (('X', (('bound', 'missing'),)),),
               (('X', (('hole', 'x'),)),),
               (('X', (('let', 't', 'X', ('bound', 'wrong')),)),)]
    for bad in invalid:
        try: factor_identity_self(bad)
        except ValueError: check(True)
        else: check(False)
    print(json.dumps({'result': 'PASS', 'assertions': checks, 'finite_fixture_cases': cases,
                      'active_presence_separation_pairs': len(triples) * (len(triples) - 1),
                      'numeric_iteration_cutoff': False, 'debt_clipping': False,
                      'general_recursive_solver': False, 'source_oracle_certified': False,
                      'wall_seconds': round(time.monotonic() - start, 4)}, sort_keys=True))


if __name__ == '__main__': main()
