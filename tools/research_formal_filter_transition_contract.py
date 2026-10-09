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


def run_worklist(events, mutant=None, aliases=None):
    """Candidate incremental bounds: retain/replay every contextual task."""
    aliases = aliases or {}
    facts, memo = set(), set()
    pending = deque()
    peak = 0
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
            fact = l, u, w
            old = tuple(facts)
            facts.add(fact)
            guard(len(facts))
            pending.extend(function_children(fact, swapped))
            for a, b, previous in old:
                if b == l and is_row(l):
                    pending.append((a, u, replay(previous, w, mutant)))
                if u == a and is_row(u):
                    pending.append((l, b, replay(w, previous, mutant)))
    return facts, peak


def run_reference(events, aliases=None):
    """Reference batch saturation, literal weight reduction, no task memo."""
    aliases = aliases or {}
    facts = {(aliases.get(l, l), aliases.get(u, u), w) for l, u, w in events}
    while True:
        previous = set(facts)
        for fact in previous:
            facts.update(function_children(fact, swapped_literal))
        for a, middle, w in previous:
            if is_row(middle):
                for other, b, v in previous:
                    if middle == other:
                        facts.add((a, b, replay_literal(w, v)))
        guard(len(facts))
        if facts == previous:
            return facts


def outputs(facts):
    return {fact for fact in facts if not is_row(fact[0]) and not is_row(fact[1])}


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
    # Unknown returned value acquires a Function after the output view exists.
    late = (("v:return", "fun:U", POP),
            ("con:E#attached", "e:latent", PUSH),
            ("con:E#unattached", "e:latent", EMPTY),
            ("fun:L", "v:return", EMPTY))
    # Distinct routes sharing the same canonical row must keep both contexts.
    contexts = (("e:alias", "sink:row", POP),
                ("e:shared", "sink:row", Weight(((1, 1, 0),), (), E)),
                ("con:E#attached", "e:shared", PUSH))
    aliases = {"e:alias": "e:shared"}
    graph_checks = max_facts = max_pending = 0
    for fixture, mapping in ((late, {}), (contexts, aliases)):
        expected = outputs(run_reference(fixture, mapping))
        for order in permutations(fixture):
            actual, peak = run_worklist(order, aliases=mapping)
            assert outputs(actual) == expected
            max_facts = max(max_facts, len(actual))
            max_pending = max(max_pending, peak)
            graph_checks += 1
    late_reference = outputs(run_reference(late))
    assert ("con:E#attached", "sink:latent", Weight((), (), E)) in late_reference
    assert ("con:E#unattached", "sink:latent", POP) in late_reference
    # Existing provider facts remain untouched; no reversed provider fact forms.
    assert ("con:E#attached", "e:latent", PUSH) in run_reference(late)
    assert not any(l == "sink:latent" for l, _, _ in run_reference(late))
    witnesses = {
        "context-erasure": (contexts, aliases),
        "global-family-cancel": (contexts, aliases),
        "effect-only-wrap": (late, {}),
    }
    for mutation, (fixture, mapping) in witnesses.items():
        actual, _ = run_worklist(fixture, mutation, mapping)
        assert outputs(actual) != outputs(run_reference(fixture, mapping)), mutation
    print(f"PASS bounded transition consistency: words={word_checks}, replay={replay_checks}, "
          f"event_orders={graph_checks}, mutations_detected={len(witnesses)}, "
          f"max_facts={max_facts}, max_pending={max_pending}; no support-projection claim")


if __name__ == "__main__":
    main()
