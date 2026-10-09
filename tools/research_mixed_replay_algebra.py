#!/usr/bin/env python3
"""Bounded consistency check for the large-debt, one-hole context lemma.

Research only. Natural counts, one ID, common active family, All filters.
The literal reference shares pinned operation premises; it is not Oracle.
"""

from itertools import product
import json


def compose(x, y):
    p, n = x
    q, m = y
    return p + max(q - n, 0), m + max(n - q, 0)


def mix(w):
    p, n, r = w
    if r == 0 or p + n == 0:
        return w
    p, n = compose((p, n), (r, 0))
    return (p, n, 0) if n else (0, 0, p)


def replay(x, y):
    p, n = compose(x[:2], y[:2])
    return mix((p, n, x[2] + y[2]))


def apply(w, op):
    tag, c = op
    p, n, r = w
    if tag == "swap":
        return r, 0, p
    if tag == "both":
        return r, 0, r
    if tag == "prefix":
        a, b = compose(c[:2], (p, n))
        return a, b, r
    if tag == "suffix":
        return p, n, r + c[2]
    return replay(c, w) if tag == "left" else replay(w, c)


def reduce_word(word):
    out = []
    for token in word:
        if token == "D" and out and out[-1] == "U":
            out.pop()
        else:
            out.append(token)
    return tuple(out)


def encode(w):
    p, n, r = w
    return tuple("D" * p + "U" * n), tuple("D" * r)


def decode(w):
    left, right = w
    return left.count("D"), left.count("U"), len(right)


def literal_mix(w):
    left, right = w
    if not left or not right:
        return w
    reduced = reduce_word(left + right)
    return (reduced, ()) if "U" in reduced else ((), reduced)


def literal_apply(w, op):
    tag, counts = op
    left, right = w
    cl, cr = encode(counts)
    if tag == "swap":
        return right, tuple(t for t in left if t == "D")
    if tag == "both":
        return right, right
    if tag == "prefix":
        return reduce_word(cl + left), right
    if tag == "suffix":
        return left, cr + right
    if tag == "left":
        return literal_mix((reduce_word(cl + left), right + cr))
    return literal_mix((reduce_word(left + cl), cr + right))


def evaluate(q, copied, context):
    w = (q, 0, q) if copied else (0, 0, q)
    ref = encode(w)
    for op in context:
        w = apply(w, op)
        ref = literal_apply(ref, op)
        assert w == decode(ref), (q, copied, context, w, ref)
    w = mix(w)
    ref = literal_mix(ref)
    assert w == decode(ref)
    return w


def signature(w):
    p, n, r = w
    return n > 0, p + n > 0, r > 0


def clip(w, k):
    return min(w[0], k), w[1], min(w[2], k)


def clipping_checks():
    constants = ((0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 2, 0),
                 (0, 0, 1), (1, 1, 0), (1, 2, 1))
    operations = tuple((side, c) for side in ("left", "right") for c in constants)
    operations += (("swap", (0, 0, 0)), ("both", (0, 0, 0)),
                   ("prefix", (0, 2, 0)), ("suffix", (0, 0, 2)))
    unary = binary = homomorphisms = 0
    for k in range(1, 5):
        debts = tuple((p, 0, r) for p, r in product(range(7), repeat=2))
        for x, y in product(debts, repeat=2):
            assert clip(replay(x, y), k) == clip(replay(clip(x, k), clip(y, k)), k)
            homomorphisms += 1
        for w in debts:
            for op in operations:
                if op[1][1] == 0:
                    assert clip(apply(w, op), k) == clip(apply(clip(w, k), op), k)
                    homomorphisms += 1
    # Fixed contexts containing PUSH, with clipping after every operation.
    for length in range(3):
        for context in product(operations, repeat=length):
            s = sum(c[1] for _, c in context)
            k = s + 1
            for p, r in product(range(7), repeat=2):
                exact = (p, 0, r)
                small = clip(exact, k)
                for op in context:
                    exact = apply(exact, op)
                    small = clip(apply(small, op), k)
                assert signature(mix(exact)) == signature(mix(small)), (context, p, r)
                unary += 1
    # Two independent hole values; the shared-hole subset is included.
    debts = tuple((p, 0, r) for p, r in product((0, 1, 4, 7), repeat=2))
    transforms = (("prefix", (0, 0, 0)), ("swap", (0, 0, 0)), ("both", (0, 0, 0)))
    for x, y in product(debts, repeat=2):
        for a, b in product(range(3), repeat=2):
            k = a + b + 1
            for tx, ty, outer in product(transforms, repeat=3):
                exact_x = apply(apply(x, tx), ("prefix", (0, a, 0)))
                exact_y = apply(apply(y, ty), ("prefix", (0, b, 0)))
                small_x = clip(apply(clip(apply(clip(x, k), tx), k), ("prefix", (0, a, 0))), k)
                small_y = clip(apply(clip(apply(clip(y, k), ty), k), ("prefix", (0, b, 0))), k)
                exact = mix(apply(replay(exact_x, exact_y), outer))
                small = clip(mix(apply(clip(replay(small_x, small_y), k), outer)), k)
                assert signature(exact) == signature(small), (x, y, a, b, tx, ty, outer)
                binary += 1
    # K=S fails for presence: S versus S+1 debt after S pushes.
    for s in range(1, 5):
        ctx = (("left", (0, s, 0)), ("swap", (0, 0, 0)))
        assert signature(evaluate(s, False, ctx)) != signature(evaluate(s + 1, False, ctx))
        assert clip((0, 0, s), s) == clip((0, 0, s + 1), s)
    return {"debt_homomorphism_checks": homomorphisms,
            "unary_clipping_checks": unary, "binary_clipping_checks": binary,
            "cap_S_presence_mutation": "killed"}


def main():
    constants = ((0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0))
    operations = tuple((side, c) for side in ("left", "right") for c in constants)
    operations += (("swap", (0, 0, 0)), ("prefix", (1, 0, 0)),
                   ("prefix", (0, 1, 0)), ("suffix", (0, 0, 1)))
    contexts = comparisons = tail_checks = 0
    for length in range(4):
        for context in product(operations, repeat=length):
            contexts += 1
            mass = sum(sum(c) for _, c in context)
            for copied in (False, True):
                values = [evaluate(q, copied, context) for q in range(mass + 5)]
                comparisons += len(values)
                tail = values[mass + 1:]
                k = 2 if copied else 1
                first, second = tail[:2]
                delta = tuple(b - a for a, b in zip(first, second))
                assert delta in ((k, 0, 0), (0, 0, k)), (context, mass, tail)
                for j, w in enumerate(tail):
                    assert w == tuple(a + j * d for a, d in zip(first, delta))
                    assert signature(w) == signature(first)
                    tail_checks += 1
    # Named falsifier: replacing all positive right debts by R_1 changes
    # the active observer even in a fixed context of mass two.
    witness = (("right", (0, 2, 0)),)
    assert signature(evaluate(1, False, witness))[0]
    assert not signature(evaluate(2, False, witness))[0]
    print(json.dumps({"result": "PASS", "contexts": contexts,
                      "candidate_literal_comparisons": comparisons,
                      "eventual_affine_checks": tail_checks,
                      "max_context_length": 3, "operations": len(operations),
                      "positive_debt_collapse_mutation": "killed",
                      **clipping_checks()}, sort_keys=True))


if __name__ == "__main__":
    main()
