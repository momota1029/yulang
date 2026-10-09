#!/usr/bin/env python3
"""Research-only directed-weight/row/Function transition characterization.

Not an Oracle invocation, effect-support evaluator, compiler test, or proof of
source formation. See the paired progress note for shared assumptions/omissions.
Run by the primary: timeout 30s python3 -B tools/research_formal_filter_transition_contract.py
"""
from collections import deque
from dataclasses import dataclass
from itertools import product, permutations
import time


ALL = frozenset(("E", "F"))  # finite concrete alphabet, not Oracle wildcard
E = frozenset(("E",))
FAMILIES = {0: E, 1: E}  # equal sets, distinct source-owned attachment IDs
LIMIT = 4096
DEADLINE = None


@dataclass(frozen=True)
class Weight:
    # id, leading pops, active pushes; IDs refer to immutable FAMILIES records.
    left: tuple = ()
    right: tuple = ()  # id, pops
    filter: frozenset = ALL


def guard(n):
    assert n <= LIMIT, "finite task-domain budget exceeded"
    assert DEADLINE is None or time.monotonic() < DEADLINE, "wall budget exceeded"


def compact(words):
    """Candidate count update: compose_same_id_counts specialization."""
    counts = {}
    for identity, op in words:
        p, n = counts.get(identity, (0, 0))
        if op == "+":
            n += 1
        elif n:
            n -= 1
        else:
            p += 1
        counts[identity] = p, n
    return tuple((i, p, n) for i, (p, n) in sorted(counts.items()) if p or n)


def literal_reduce(words):
    """Reference: rewrite adjacent same-ID push/pop in separate literal words."""
    streams = {identity: [] for identity, _ in words}
    for identity, op in words:
        streams[identity].append(op)
    result = []
    for identity, stream in sorted(streams.items()):
        changed = True
        while changed:
            changed = False
            for k in range(len(stream) - 1):
                if stream[k:k + 2] == ["+", "-"]:
                    del stream[k:k + 2]
                    changed = True
                    break
        if stream:
            assert stream == ["-"] * stream.count("-") + ["+"] * stream.count("+")
            result.append((identity, stream.count("-"), stream.count("+")))
    return tuple(result)


def words(weight):
    return tuple(token for i, p, n in weight.left
                 for token in ((i, "-"),) * p + ((i, "+"),) * n)


def mix_count(left, right, filter_set):
    if not left or not right:
        return Weight(left, right, filter_set)
    l = {i: (p, n) for i, p, n in left}
    r = {}
    for i, pops in right:
        p, n = l.pop(i, (0, 0))
        cancel = min(n, pops)
        n -= cancel
        p += pops - cancel
        if n:
            l[i] = p, n
        elif p:
            r[i] = p
    return Weight(tuple((i, p, n) for i, (p, n) in sorted(l.items())),
                  tuple(sorted(r.items())), filter_set)


def replay(a, b, mutant=None):
    stream = words(a) + words(b)
    if mutant == "global-family-cancel":
        stream = tuple((0, op) for _, op in stream)
    left = compact(stream)
    r = {}
    for i, pops in b.right + a.right:  # later upper wrappers prepend
        r[i] = r.get(i, 0) + pops
    return mix_count(left, tuple(sorted(r.items())), a.filter & b.filter)


def replay_literal(a, b):
    left = literal_reduce(words(a) + words(b))
    right_tokens = [i for i, p in b.right + a.right for _ in range(p)]
    right = tuple((i, right_tokens.count(i)) for i in sorted(set(right_tokens)))
    if not left or not right:
        return Weight(left, right, a.filter & b.filter)
    stream = list(words(Weight(left)))
    remaining_right = []
    for i, p in right:
        reduced = literal_reduce(tuple(stream) + ((i, "-"),) * p)
        stream = list(words(Weight(reduced)))
        entry = next((entry for entry in reduced if entry[0] == i), None)
        if entry and entry[2] == 0:
            remaining_right.extend([i] * entry[1])
            stream = [token for token in stream if token[0] != i]
    return Weight(literal_reduce(tuple(stream)),
                  tuple((i, remaining_right.count(i)) for i in sorted(set(remaining_right))),
                  a.filter & b.filter)


def swapped(w):
    # Oracle drops active left pushes AND left filter under ordinary variance.
    return Weight(tuple((i, p, 0) for i, p in w.right),
                  tuple((i, p) for i, p, _ in w.left if p), ALL)


def swapped_literal(w):
    lp = [(i, "-") for i, p in w.right for _ in range(p)]
    rp = [i for i, op in words(w) if op == "-"]
    return Weight(literal_reduce(tuple(lp)),
                  tuple((i, rp.count(i)) for i in sorted(set(rp))), ALL)


EMPTY = Weight()
PUSH = Weight(((0, 0, 1),))
POP = Weight(((0, 1, 0),), (), E)
POP_ERASED = Weight(POP.left, POP.right, ALL)


def is_row(node):
    return node.startswith(("v:", "e:"))


FUNCTIONS = {
    "fun:L": ("arg:L", "ae:L", "e:latent", "ret:L"),
    "fun:U": ("arg:U", "ae:U", "sink:latent", "ret:U"),
}


def function_children(fact, reverse):
    l, u, w = fact
    if l not in FUNCTIONS or u not in FUNCTIONS:
        return ()
    a, ae, re, r = FUNCTIONS[l]
    ua, uae, ure, ur = FUNCTIONS[u]
    return ((ua, a, reverse(w)), (uae, ae, reverse(w)),
            (re, ure, w), (r, ur, w))


@dataclass(frozen=True)
class Snapshot:
    facts: frozenset
    filters: frozenset  # (row, allowed finite set), stored separately from bounds
    checks: frozenset  # ("stack", attachment ID, filter) / ("con", node, filter)
    violations: frozenset


def erased(w):
    return Weight(w.left, w.right, ALL)


def concrete_family(node):
    if node.startswith("con:E#"):
        return E
    if node.startswith("con:F#"):
        return frozenset(("F",))
    return None


def run_worklist(events, mutant=None, aliases=None):
    """Incremental insertion: check/register F, erase F, then replay bounds.

    The shape/filter rules are supplied from the pinned Oracle, not validated
    by agreement with run_reference. Extrusion/provenance/subsumption omitted.
    """
    aliases = aliases or {}
    facts, memo, filters, checks, violations = set(), set(), set(), set(), set()
    pending = deque()
    peak = 0

    def stack_check(w, f):
        if f != ALL:
            for i, _, n in w.left:
                if n:
                    checks.add(("stack", i, f))
                    if not FAMILIES[i] <= f:
                        violations.add(("stack", i, f))

    def pos_check(node, f):
        if f == ALL:
            return
        if is_row(node):
            register(node, f)
        elif node in FUNCTIONS:
            # Oracle Pos::Fun is a no-op, not a port traversal.
            if mutant == "recurse-function-filter":
                for child in FUNCTIONS[node]:
                    pos_check(child, f)
        else:
            family = concrete_family(node)
            if family is not None:
                checks.add(("con", node, f))
                if not family <= f:
                    violations.add(("con", node, f))

    def weighted_check(node, w, f):
        if f != ALL:
            stack_check(w, f)
            pos_check(node, w.filter & f)

    def register(row, f):
        key = row, f
        if f == ALL or key in filters:
            return
        filters.add(key)
        for lower, target, w in tuple(facts):
            if target == row:
                weighted_check(lower, w, f)

    for event in events:
        pending.append(event)
        while pending:
            peak = max(peak, len(pending))
            guard(peak)
            l, u, w = pending.popleft()
            l, u = aliases.get(l, l), aliases.get(u, u)
            if mutant == "effect-only-wrap" and l == "v:return" and u == "fun:U":
                w = EMPTY
            key = (l, u) if mutant == "context-erasure" else (l, u, w)
            if key in memo:
                continue
            memo.add(key)
            guard(len(memo))
            # Row-row gets both insertion orientations in Oracle. The fixtures
            # exclude same-row constraints and weighted cycles.
            if is_row(u):
                weighted_check(l, w, w.filter)
            if is_row(l):
                stack_check(w, w.filter)
                register(l, w.filter)
            stored = w
            if is_row(l) or is_row(u):
                keep_upper = mutant == "retain-upper-filter" and is_row(l)
                keep_lower = mutant == "retain-lower-filter" and is_row(u)
                if not (keep_upper or keep_lower):
                    stored = erased(w)
            fact = l, u, stored
            old = tuple(facts)
            facts.add(fact)
            guard(len(facts) + len(filters) + len(checks) + len(violations))
            if is_row(u) and mutant != "skip-future-filter":
                for row, f in tuple(filters):
                    if row == u:
                        weighted_check(l, stored, f)
            pending.extend(function_children(fact, swapped))
            for a, b, previous in old:
                if b == l and is_row(l):
                    pending.append((a, u, replay(previous, stored, mutant)))
                if u == a and is_row(u):
                    pending.append((l, b, replay(stored, previous, mutant)))
    return Snapshot(frozenset(facts), frozenset(filters), frozenset(checks),
                    frozenset(violations)), peak


def run_reference(events, aliases=None):
    """Batch saturation with literal weights and separately saturated filters.

    Independently scheduled/reduced, but uses the same source shape, insertion
    and checking schema as the incremental implementation.
    """
    aliases = aliases or {}
    tasks = {(aliases.get(l, l), aliases.get(u, u), w) for l, u, w in events}
    filters, checks, violations = set(), set(), set()
    while True:
        before = tasks.copy(), filters.copy(), checks.copy(), violations.copy()
        facts = {(l, u, erased(w) if is_row(l) or is_row(u) else w)
                 for l, u, w in tasks}

        def inspect_stack(w, f):
            if f == ALL:
                return
            for i, _, n in w.left:
                if n > 0:
                    checks.add(("stack", i, f))
                    if FAMILIES[i] - f:
                        violations.add(("stack", i, f))

        def inspect_pos(node, f):
            if f == ALL:
                return
            if is_row(node):
                filters.add((node, f))
            elif node not in FUNCTIONS:
                family = concrete_family(node)
                if family is not None:
                    checks.add(("con", node, f))
                    if family - f:
                        violations.add(("con", node, f))

        def inspect_weighted(node, w, f):
            inspect_stack(w, f)
            inspect_pos(node, w.filter & f)

        for l, u, w in tuple(tasks):
            if is_row(u):
                inspect_weighted(l, w, w.filter)
            if is_row(l):
                inspect_stack(w, w.filter)
                inspect_pos(l, w.filter)
        # Registered variable filters are persistent and visit all stored lowers.
        for row, f in tuple(filters):
            for l, u, w in facts:
                if u == row:
                    inspect_weighted(l, w, f)
        for fact in facts:
            tasks.update(function_children(fact, swapped_literal))
        for a, middle, w in facts:
            if is_row(middle):
                for other, b, v in facts:
                    if middle == other:
                        tasks.add((a, b, replay_literal(w, v)))
        guard(len(tasks) + len(filters) + len(checks) + len(violations))
        if before == (tasks, filters, checks, violations):
            return Snapshot(frozenset(facts), frozenset(filters), frozenset(checks),
                            frozenset(violations))


def outputs(snapshot):
    return {fact for fact in snapshot.facts
            if not is_row(fact[0]) and not is_row(fact[1])}


def main():
    global DEADLINE
    DEADLINE = time.monotonic() + 29
    alphabet = ((0, "+"), (0, "-"), (1, "+"), (1, "-"))
    word_checks = replay_checks = 0
    for n in range(5):
        for stream in product(alphabet, repeat=n):
            assert compact(stream) == literal_reduce(stream)
            word_checks += 1
    short = [stream for n in range(3) for stream in product(alphabet, repeat=n)]
    right = [stream for n in range(3) for stream in product((0, 1), repeat=n)]
    for x, y, rs in product(short, short, right):
        a = Weight(compact(x), (), E)
        b = Weight(compact(y), tuple((i, rs.count(i)) for i in sorted(set(rs))), ALL)
        assert replay(a, b) == replay_literal(a, b)
        assert swapped(a) == swapped_literal(a)
        replay_checks += 1
    # Filter is registered on v:return, erased from its stored upper, and
    # never recursively applied to ports of a later Function lower.
    late = (("v:return", "fun:U", POP),
            ("con:E#attached", "e:latent", PUSH),
            ("con:E#unattached", "e:latent", EMPTY),
            ("fun:L", "v:return", EMPTY))
    lower_late = (("fun:L", "v:return", POP),
                  ("con:E#attached", "e:latent", PUSH),
                  ("con:E#unattached", "e:latent", EMPTY),
                  ("v:return", "fun:U", EMPTY))
    contexts = (("e:alias", "sink:row", POP),
                ("e:shared", "sink:row", Weight(((1, 1, 0),), (), E)),
                ("con:E#attached", "e:shared", PUSH))
    aliases = {"e:alias": "e:shared"}
    future_bad = (("e:checked", "sink:row", POP),
                  ("con:F#late", "e:checked", EMPTY))
    lower_bad = (("con:F#lower", "e:checked", POP),
                 ("e:checked", "sink:row", EMPTY))
    push_filtered = Weight(PUSH.left, (), frozenset(("F",)))
    stack_upper = (("e:checked", "sink:row", push_filtered),
                   ("con:F#lower", "e:checked", EMPTY))
    stack_lower = (("con:F#lower", "e:checked", push_filtered),
                   ("e:checked", "sink:row", EMPTY))
    bridge = (("e:source", "e:target", POP),
              ("con:F#late", "e:source", EMPTY),
              ("e:target", "sink:row", EMPTY))
    fixtures = ((late, {}), (lower_late, {}), (contexts, aliases),
                (future_bad, {}), (lower_bad, {}), (stack_upper, {}),
                (stack_lower, {}), (bridge, {}))
    graph_checks = max_facts = max_pending = 0
    for fixture, mapping in fixtures:
        expected = run_reference(fixture, mapping)
        for order in permutations(fixture):
            actual, peak = run_worklist(order, aliases=mapping)
            assert actual == expected, (fixture, order, actual, expected)
            max_facts = max(max_facts, len(actual.facts))
            max_pending = max(max_pending, peak)
            graph_checks += 1
    late_reference = run_reference(late)
    assert ("v:return", E) in late_reference.filters
    assert not any(row == "e:latent" for row, _ in late_reference.filters)
    assert ("v:return", "fun:U", POP_ERASED) in late_reference.facts
    assert ("con:E#attached", "sink:latent", EMPTY) in outputs(late_reference)
    assert ("con:E#unattached", "sink:latent", POP_ERASED) in outputs(late_reference)
    lower_reference = run_reference(lower_late)
    assert not lower_reference.filters  # checking Pos::Fun does not descend
    assert ("fun:L", "v:return", POP_ERASED) in lower_reference.facts
    assert ("con:E#unattached", "sink:latent", POP_ERASED) in outputs(lower_reference)
    assert ("con", "con:F#late", E) in run_reference(future_bad).violations
    assert ("con", "con:F#lower", E) in run_reference(lower_bad).violations
    assert ("stack", 0, frozenset(("F",))) in run_reference(stack_upper).violations
    assert ("stack", 0, frozenset(("F",))) in run_reference(stack_lower).violations
    # Existing provider bounds remain untouched; no reversed provider fact forms.
    assert ("con:E#attached", "e:latent", PUSH) in late_reference.facts
    assert not any(l == "sink:latent" for l, _, _ in late_reference.facts)
    witnesses = {
        "context-erasure": (contexts, aliases),
        "global-family-cancel": (contexts, aliases),
        "effect-only-wrap": (late, {}),
        "retain-upper-filter": (late, {}),
        "retain-lower-filter": (lower_late, {}),
        "skip-future-filter": (future_bad, {}),
        "recurse-function-filter": (late, {}),
    }
    for mutation, (fixture, mapping) in witnesses.items():
        actual, _ = run_worklist(fixture, mutation, mapping)
        assert actual != run_reference(fixture, mapping), mutation
        if mutation in ("retain-upper-filter", "retain-lower-filter"):
            assert outputs(actual) != outputs(run_reference(fixture, mapping)), mutation
        if mutation == "skip-future-filter":
            assert ("con", "con:F#late", E) not in actual.violations
        if mutation == "recurse-function-filter":
            assert ("e:latent", E) in actual.filters
    print(f"PASS bounded transition consistency: words={word_checks}, replay={replay_checks}, "
          f"event_orders={graph_checks}, mutations_detected={len(witnesses)}, "
          f"max_facts={max_facts}, max_pending={max_pending}; no support-projection claim")


if __name__ == "__main__":
    main()
