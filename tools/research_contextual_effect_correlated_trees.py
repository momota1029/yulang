#!/usr/bin/env python3
"""Bracket-preserving one-ID research model. Not Oracle or source execution.

Residual changes are terminal except for swap, which discards active payloads.
No unequal same-ID payloads are ever replayed; that source case is omitted.
"""
from dataclasses import dataclass
from itertools import product
import json

E = frozenset({'E'})
EMPTY = frozenset()
ALL = frozenset({'E', 'F'})

@dataclass(frozen=True)
class W:
    p: int = 0
    n: int = 0
    r: int = 0
    family: frozenset = E

def comp(p, n, q, m):
    return (p, n-q+m) if q <= n else (p+q-n, m)

def replay(a, b):
    assert a.family == b.family == E, 'changing-payload replay outside model'
    p, n = comp(a.p, a.n, b.p, b.n)
    r = a.r + b.r
    if (p or n) and r:
        p, n = comp(p, n, r, 0)
        if n:
            r = 0
        else:
            p, r = 0, p
    return W(p, n, r)

def literal_replay(a, b):
    assert a.family == b.family == E
    left = list('-'*a.p + '+'*a.n + '-'*b.p + '+'*b.n)
    reduced = []
    for token in left:
        if token == '-' and reduced and reduced[-1] == '+':
            reduced.pop()
        else:
            reduced.append(token)
    right = ['-'] * (a.r + b.r)
    if reduced and right:
        for token in right:
            if reduced and reduced[-1] == '+':
                reduced.pop()
            else:
                reduced.append(token)
        right = []
        if '+' not in reduced:
            right, reduced = reduced, []
    return W(reduced.count('-'), reduced.count('+'), len(right))

def swap(a):
    return W(a.r, 0, a.p)

def head_consume(a, immutable=False):
    # One-ID, written H={E}, nullary family fragment. If active, H intersects S.
    retained = E & a.family if a.n else E
    return W(a.p, a.n, a.r,
             a.family if immutable or not a.n else a.family - retained)

def filter_pass(a, permitted=EMPTY):
    return not a.n or a.family <= permitted

def compact_left_presence(a, active_only=False):
    # Fixed declared fact (i,{F}) and written head E: E retained iff i present.
    return bool(a.n) if active_only else bool(a.p or a.n)

def summary(a):
    return (bool(a.p), bool(a.n), bool(a.r),
            tuple(sorted(a.family)) if a.n else (), filter_pass(a),
            compact_left_presence(a))

ID = ('e',)
D = ('D',)
P = ('P',)

def tree(k, c):
    # X_c ::= e | replay(D,replay(X_c,P_c)); actual grouping retained.
    pc = ID
    for _ in range(c):
        pc = ('replay', pc, P)
    t = ID
    for _ in range(k):
        t = ('replay', D, ('replay', t, pc))
    return t

def eval_tree(t, ref=False):
    op = t[0]
    if op == 'e': return W()
    if op == 'D': return W(p=1)
    if op == 'P': return W(n=1)
    if op == 'swap': return swap(eval_tree(t[1], ref))
    assert op == 'replay'
    fn = literal_replay if ref else replay
    return fn(eval_tree(t[1], ref), eval_tree(t[2], ref))

def observer_tree(t):
    return ('replay', t, ('swap', t))

def vector(a):
    return [a.p, a.n, a.r, ''.join(sorted(a.family))]

def main():
    # Restricted, explicit synthetic schema. No seed or random selection.
    checked = 0
    for k, c in product(range(13), range(4)):
        t = tree(k,c)
        w = eval_tree(t)
        assert w == eval_tree(t, True) == W(p=k,n=c*k)
        ct = observer_tree(t)
        z = eval_tree(ct)
        assert z == eval_tree(ct, True)
        expected = W(p=k,n=(c-1)*k) if c > 1 else W(r=(2-c)*k)
        # k=0 and pure-right zero have the same representation.
        assert z == expected, (k,c,z,expected)
        after = head_consume(z)
        assert filter_pass(after)
        if z.n:
            assert after.family == EMPTY
        checked += 2

    # Minimize counts subject to the correlated pair p=n and n=2p.
    pairs = []
    for k in range(1,13):
        a, b = eval_tree(tree(k,1)), eval_tree(tree(k,2))
        assert summary(a) == summary(b)
        za = head_consume(eval_tree(observer_tree(tree(k,1))))
        zb = head_consume(eval_tree(observer_tree(tree(k,2))))
        assert filter_pass(za) == filter_pass(zb) == True
        assert compact_left_presence(za) is False
        assert compact_left_presence(zb) is True
        # After swap both are inactive, but leading pending POP presence differs.
        sa, sb = swap(za), swap(zb)
        assert not sa.n and not sb.n
        assert filter_pass(sa) == filter_pass(sb)
        assert compact_left_presence(sa) is True
        assert compact_left_presence(sb) is False
        pairs.append((sum((a.p,a.n,b.p,b.n)),k,a,b,za,zb,sa,sb))
    witness = min(pairs, key=lambda x:x[:2])
    _, k, a,b,za,zb,sa,sb = witness
    assert k == 1

    # Named shortcut mutations; each must be rejected by a local witness.
    raw_b = eval_tree(observer_tree(tree(1,2)))
    assert not filter_pass(head_consume(raw_b,immutable=True))
    assert filter_pass(head_consume(raw_b))
    assert compact_left_presence(sa) != compact_left_presence(sa,active_only=True)
    # Reassociate only the root tree for the minimal p=n input.
    # C(D;P) = (D;P);swap(D;P), source-exact R. Moving parentheses: D;(P;R).
    d,p,r = W(p=1),W(n=1),W(r=1)
    assert replay(replay(d,p),r) == W(r=1)
    assert replay(d,replay(p,r)) == W(p=1)
    assert compact_left_presence(replay(replay(d,p),r)) is False
    assert compact_left_presence(replay(d,replay(p,r))) is True

    print(json.dumps({
        'claim':'bounded synthetic-schema characterization; not source reachability',
        'k_range':[0,12], 'c_range':[0,3], 'tree_evaluations_compared':checked,
        'paired_depths':12,'minimized_depth':k,
        'inputs':[vector(a),vector(b)],
        'after_replay_residual':[vector(za),vector(zb)],
        'after_swap':[vector(sa),vector(sb)],
        'mutations_killed':['immutable active family','active-only compact presence',
                            'root reassociation'],
        'seed':'none; exhaustive rectangular range'
    }, sort_keys=True))

if __name__ == '__main__': main()
