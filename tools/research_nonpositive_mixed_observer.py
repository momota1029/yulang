#!/usr/bin/env python3
"""Research-only exact finite observer for nonpositive-displacement suppliers.

Producer implementation, independent review pending; no compiler routing or
source restriction. Governing algorithm: sections 2--6 of
notes/progress/2026-10-10-complete-mixed-effect-obstruction.md, frozen SHA256
6eb765b84731a899a3a94d197059e2061529bc248a53d6d1af593ff4a09d9924.
Baseline f75c8d2fc27c8e5f61e13632b234d56314d2a62c.
Algebra dependency research_mixed_debt_observer.py SHA256
c6f3d36462469494dcdaa5fd6e22029bcea0f5d48a258e5eb55bc41a65dfaf6c.

All public representative tuples use raw (p,n,r) coordinates, but saturation
caps d=p-n and r ONLY. K markers represent counts at least K, not exact debt.
The immutable grammar snapshot retains original syntax for every larger future
query. add returns a new snapshot; retaining the old one is model recovery,
not production rollback. No guard prunes supplier productions.

Queries use finite tuple syntax and named holes, with arbitrary natural leaf
and prefix counts. Every occurrence of one hole name shares a whole selection;
different names choose independently, even when bound to the same supplier.
Grammar let/bound explicitly shares a whole child value. Queries express finite
sharing by repeated hole names, rather than grammar let/bound syntax. Traces
include every syntax occurrence, not just holes or the root. They contain exact
active counts, comparisons of p and r to every constant 0..T, left entry, and
identity. No arbitrary predicate on representative debt is exposed as exact.
No unbounded debt-equality, source filter, residual gamma, callback-end-to-end,
production, source-Oracle, or complete mixed Effect decision claim is made.
"""
from dataclasses import dataclass
from itertools import product
import json

from research_mixed_debt_observer import (
    nat, operation, child_occurrences, literal, decode, observe,
    local_terminal as debt_local_terminal,
)


def validate(e, names, grammar=False, scope=frozenset()):
    """Return (hole occurrences, operation occurrences, PUSH mass, grammar N)."""
    if not isinstance(e, tuple) or not e or not isinstance(e[0], str):
        raise ValueError('expression must be a nonempty tagged tuple')
    tag = e[0]
    arities = {'const':4, 'ref':2, 'hole':2, 'replay':3, 'mix':2,
               'swap':2, 'both_from_right':2, 'identity':2, 'prefix':4,
               'suffix':3, 'let':4, 'bound':2}
    if tag not in arities or len(e) != arities[tag]:
        raise ValueError('unsupported operation or invalid arity')
    if tag == 'const':
        for x in e[1:]: nat(x)
        if grammar and e[1] < e[2]:
            raise ValueError('positive-displacement grammar constant')
        return 0,0,e[2],e[2]
    if tag in ('ref','hole'):
        if (tag != ('ref' if grammar else 'hole') or
                not isinstance(e[1],str) or e[1] not in names):
            raise ValueError('unknown or unsupported reference')
        return int(tag == 'hole'),0,0,0
    if tag == 'bound':
        if not grammar or not isinstance(e[1],str) or e[1] not in scope:
            raise ValueError('unbound or unsupported variable')
        return 0,0,0,0
    if tag == 'let':
        if (not grammar or not isinstance(e[1],str) or not e[1] or
                not isinstance(e[2],str) or e[2] not in names):
            raise ValueError('invalid shared binding')
        return validate(e[3],names,grammar,scope | {e[1]})
    push = 0
    if tag == 'prefix':
        nat(e[1]); nat(e[2]); push = e[2]
        if grammar and e[1] < e[2]:
            raise ValueError('positive-displacement grammar prefix')
    if tag == 'suffix': nat(e[1])
    children = [validate(c,names,grammar,scope) for _,c in child_occurrences(e)]
    return (sum(v[0] for v in children), 1+sum(v[1] for v in children),
            push+sum(v[2] for v in children), max([push]+[v[3] for v in children]))


def cap_debt(w, k):
    p,n,r = w
    if p < n: raise ValueError('supplier violates nonpositive displacement')
    return n+min(p-n,k),n,min(r,k)


def values(e, env, k, bound=None):
    """Production evaluation in the joint finite quotient."""
    bound = {} if bound is None else bound
    tag = e[0]
    if tag == 'let':
        out = set()
        for w in env[e[2]]:
            out.update(values(e[3],env,k,{**bound,e[1]:w}))
    elif tag == 'bound': out = {bound[e[1]]}
    elif tag == 'const': out = {e[1:]}
    elif tag == 'ref': out = env[e[1]]
    else:
        out = {operation(tag,ws,e) for ws in product(*(
            values(c,env,k,bound) for _,c in child_occurrences(e)))}
    return {cap_debt(w,k) for w in out}


def threshold_observe(w, threshold):
    """(exact active, p comparisons, r comparisons, left entry, identity).

    Comparison entries indexed by c in 0..threshold: -1 means count<c,
    0 count=c, 1 count>c. Only these bounded observations are exact.
    """
    n,_,_,left,identity = observe(w)
    def comparisons(x): return tuple((x>c)-(x<c) for c in range(threshold+1))
    return n,comparisons(w[0]),comparisons(w[2]),left,identity


def local_terminal(observation, family, allowed=None, subtract=()):
    """Fixed finite-family terminal helper; not a source-filter producer."""
    n,p,r,left,identity = observation
    return debt_local_terminal((n,p[0]>0,r[0]>0,left,identity),family,allowed,subtract)


@dataclass(frozen=True)
class Grammar:
    """Immutable original syntax; no permanent query-dependent truncation."""
    rules: tuple

    def __post_init__(self):
        rules = tuple((name,tuple(ps)) for name,ps in self.rules)
        names = [name for name,_ in rules]
        if (any(not isinstance(name,str) or not name for name in names) or
                len(names) != len(set(names))):
            raise ValueError('invalid or duplicate nonterminal')
        for _,ps in rules:
            for e in ps: validate(e,set(names),True)
        object.__setattr__(self,'rules',rules)

    @property
    def active_bound(self):
        names = set(dict(self.rules))
        return max([0]+[validate(e,names,True)[3] for _,ps in self.rules for e in ps])

    def add(self, name, expression):
        if name not in dict(self.rules): raise ValueError('unknown nonterminal')
        return Grammar(tuple((n,ps+(expression,) if n == name else ps) for n,ps in self.rules))

    def saturate(self, k):
        nat(k)
        n_bound = self.active_bound
        if k <= n_bound: raise ValueError('cap must exceed grammar active bound')
        env = {name:set() for name,_ in self.rules}
        rounds = additions = 0
        while True:
            rounds += 1
            changed = False
            for name,ps in self.rules:
                for e in ps:
                    new = values(e,env,k)-env[name]
                    if new:
                        env[name].update(new)
                        additions += len(new)
                        changed = True
            if not changed: break
        carrier = (k+1)**2*(n_bound+1)
        assert all(len(v) <= carrier and all(0 <= w[1] <= n_bound for w in v)
                   for v in env.values())
        return {name:frozenset(ws) for name,ws in env.items()}, {
            'rounds':rounds,'additions':additions,'active_bound':n_bound,
            'carrier_per_nonterminal':carrier,'representatives_not_exact_debt':True}

    def query_traces(self, expression, holes, threshold=0):
        nat(threshold)
        holes = dict(holes)
        names = dict(self.rules)
        if any(not isinstance(h,str) or not h or not isinstance(nt,str) or nt not in names
               for h,nt in holes.items()):
            raise ValueError('invalid hole binding')
        m,h,b,_ = validate(expression,set(holes))
        n_bound = self.active_bound
        mass = b+m*n_bound
        k = max(n_bound+1,threshold+(2*h+1)*mass+2)
        env,stats = self.saturate(k)
        def used(e):
            if e[0] == 'hole': return {e[1]}
            return set().union(*(used(c) for _,c in child_occurrences(e)))
        keys = tuple(sorted(used(expression)))
        traces = set()
        for choice in product(*(env[holes[key]] for key in keys)):
            selected = dict(zip(keys,choice))
            trace = []
            def evaluate(e,path):
                if e[0] == 'const': w = e[1:]
                elif e[0] == 'hole': w = selected[e[1]]
                else:
                    ws = [evaluate(c,path+(i,)) for i,c in child_occurrences(e)]
                    w = operation(e[0],ws,e)  # No context cap.
                trace.append((path,threshold_observe(w,threshold)))
                return w
            evaluate(expression,())
            traces.add(tuple(sorted(trace)))
        return frozenset(traces), {'hole_occurrences':m,'operation_occurrences':h,
            'push_mass':b,'context_active_bound':mass,'threshold':threshold,'cap':k,**stats}

    def query(self, expression, holes, threshold=0):
        traces,stats = self.query_traces(expression,holes,threshold)
        return frozenset(dict(t)[()] for t in traces),stats


def literal_trace(e, env, threshold, path=()):
    """Independent actual-token evaluation at every finite observer node."""
    trace = [(path,threshold_observe(decode(literal(e,env)),threshold))]
    for i,c in child_occurrences(e):
        trace.extend(literal_trace(c,env,threshold,path+(i,)))
    return tuple(sorted(trace))


def main():
    checks = literal_evaluations = 0
    def check(condition):
        nonlocal checks
        checks += 1
        assert condition, checks
    I=('const',0,0,0); D=('const',1,1,0)
    R=lambda x:('const',0,0,x)
    H=lambda name:('hole',name)
    T=('ref','T')
    # Productive and unproductive self cycles, plus nonself cycles.
    active=Grammar((('T',(('replay',T,T),D)),))
    check(active.active_bound == 1)
    check(active.saturate(2)[0]['T'] == frozenset(((1,1,0),)))
    dead=Grammar((('T',(('replay',T,T),)),))
    check(not dead.saturate(1)[0]['T'])
    check(not dead.query(H('x'),{'x':'T'})[0])
    check(len(dead.query(I,{'unused':'T'})[0]) == 1)
    cycle=Grammar((('A',(('identity',('ref','B')),)),
                   ('B',(('identity',('ref','A')),D))))
    check(cycle.saturate(2)[0]['A'] == frozenset(((1,1,0),)))
    deadcycle=Grammar((('A',(('ref','B'),)),('B',(('ref','A'),))))
    check(all(not v for v in deadcycle.saturate(1)[0].values()))
    # Recursive raw suffix, directed mix, both, swap, balanced prefix, identity.
    recursive=Grammar((('T',(D,R(1),('suffix',1,T),('mix',T),
        ('both_from_right',T),('swap',T),('prefix',1,1,T),('identity',T))),))
    recursive_env,_=recursive.saturate(3)
    check((1,1,3) in recursive_env['T'])
    check((3,0,3) in recursive_env['T'])
    check((0,0,3) in recursive_env['T'])
    check(all(p>=n and n<=1 and p-n<=3 and r<=3 for p,n,r in recursive_env['T']))
    # Sharing whole children differs from independent repeated references.
    bound=('bound','v')
    pair=Grammar((('T',(I,R(2))),
        ('S',(('let','v','T',('replay',('prefix',1,1,bound),('swap',bound))),)),
        ('U',(('replay',('prefix',1,1,T),('swap',T)),))))
    shared=pair.saturate(3)[0]
    check(shared['S'] < shared['U'])
    query_shared=('replay',('prefix',0,1,H('x')),('swap',H('x')))
    query_independent=('replay',('prefix',0,1,H('x')),('swap',H('y')))
    check(pair.query(query_shared,{'x':'T'})[0] <
          pair.query(query_independent,{'x':'T','y':'T'})[0])
    # Late productions extend observations while the original snapshot survives.
    old=Grammar((('T',(I,)),)); new=old.add('T',D)
    check(old.rules == (('T',(I,)),))
    check(old.query(H('x'),{'x':'T'})[0] < new.query(H('x'),{'x':'T'})[0])
    for bad in [('const',0,1,0),('prefix',0,1,T),('bound','missing')]:
        try: old.add('T',bad)
        except ValueError: check(old.rules == (('T',(I,)),))
        else: check(False)
    # Every future query restarts from original syntax, with its own PUSH budget.
    grows=Grammar((('T',(R(1),('suffix',1,T))),))
    small,small_stats=grows.query(('replay',('const',0,2,0),H('x')),{'x':'T'})
    large,large_stats=grows.query(('replay',('const',0,10,0),H('x')),{'x':'T'})
    check(large_stats['cap'] > small_stats['cap'])
    check({v[0] for v in small} == {0,1})
    check({v[0] for v in large} == set(range(10)))
    check(grows.rules[0][1][0] == R(1))
    # Huge debt stays a marker; all requested active/threshold observations exact.
    huge=10**80
    big=Grammar((('T',(('const',huge+2,2,huge),)),))
    expr=('mix',('prefix',0,7,('suffix',3,H('x'))))
    got,stats=big.query_traces(expr,{'x':'T'},3)
    def raw_trace(e,env,path=()):
        if e[0]=='const': w=e[1:]
        elif e[0]=='hole': w=env[e[1]]
        else: w=operation(e[0],[raw_trace(c,env,path+(i,))[0] for i,c in child_occurrences(e)],e)
        trace=[(path,threshold_observe(w,3))]
        for i,c in child_occurrences(e): trace.extend(raw_trace(c,env,path+(i,))[1])
        return w,trace
    check(got == frozenset((tuple(sorted(raw_trace(expr,{'x':(huge+2,2,huge)})[1])),)))
    check(stats['representatives_not_exact_debt'])
    # Named shortcut mutation: capping raw p destroys an exact active observation.
    mutation=('prefix',0,4,H('x'))
    correct,_=big.query(mutation,{'x':'T'})
    check({v[0] for v in correct} == {2})
    original=(102,2,0); k=3
    correct_value=operation('prefix',(cap_debt(original,k),),mutation)
    bad_value=operation('prefix',((min(original[0],k),original[1],0),),mutation)
    check(correct_value[1] == 2 and bad_value[1] == 3)
    # Grammar n can originate in prefixes; K>N is mandatory.
    prefixes=Grammar((('T',(I,('prefix',3,3,T))),))
    check(prefixes.active_bound == 3)
    try: prefixes.saturate(3)
    except ValueError: check(True)
    else: check(False)
    check((3,3,0) in prefixes.saturate(4)[0]['T'])
    check(local_terminal(threshold_observe((1,1,0),0),{'a','b'},{'b'},{'a'}) ==
          (1,True,frozenset({'b'}),False))
    # Exhaustive finite DAG literal reference with actual tokens, including
    # positive active supplier seeds, raw wrappers, and all primitive operations.
    constants=(I,D,('const',3,2,1),R(2))
    ref=('ref','A')
    productions=(('replay',ref,ref),('mix',ref),('swap',ref),
        ('both_from_right',ref),('identity',ref),('prefix',2,2,ref),('suffix',2,ref))
    dag=Grammar((('A',constants),('B',productions)))
    tokens_a={literal(c,{}) for c in constants}
    tokens_b=set()
    for e in productions:
        if e[0]=='replay':
            for x,y in product(tokens_a,repeat=2):
                tokens_b.add(literal(('replay',('ref','x'),('ref','y')),{'x':x,'y':y}))
        else:
            for x in tokens_a: tokens_b.add(literal(e,{'A':x}))
    for k in (3,5,9):
        check(dag.saturate(k)[0]['B'] == frozenset(cap_debt(decode(t),k) for t in tokens_b))
    for push in range(4):
        for outer in ('identity','mix','swap','both_from_right'):
            for side in ('left','right'):
                p=('const',0,push,0)
                core=('replay',p,H('x')) if side=='left' else ('replay',H('x'),p)
                expression=(outer,('suffix',1,core))
                traces,_=dag.query_traces(expression,{'x':'B'},2)
                expected=frozenset(literal_trace(expression,{'x':w},2) for w in tokens_b)
                check(traces == expected)
                literal_evaluations += len(tokens_b)
    # Named repeated holes retain joint trace correlations with token witnesses.
    expr=('replay',('prefix',0,3,H('x')),('both_from_right',H('x')))
    traces,stats=dag.query_traces(expr,{'x':'B'},1)
    check(traces == frozenset(literal_trace(expr,{'x':w},1) for w in tokens_b))
    literal_evaluations += len(tokens_b)
    check((stats['hole_occurrences'],stats['operation_occurrences'],stats['push_mass']) == (2,3,3))
    # Let witnesses are token selections keyed by syntax occurrence.
    sharing=('let','t','A',('replay',('bound','t'),('swap',('bound','t'))))
    let_dag=Grammar((('A',constants),('B',(sharing,))))
    expected={decode(literal(sharing,{},choices={():w})) for w in tokens_a}
    check(let_dag.saturate(9)[0]['B'] == frozenset(cap_debt(w,9) for w in expected))
    empty_binding=Grammar((('E',()),('T',(('let','t','E',I),))))
    check(not empty_binding.saturate(1)[0]['T'])
    # Existing debt grammar's original rejection remains intact.
    from research_mixed_debt_observer import Grammar as DebtGrammar
    for e in (D,('mix',('ref','T')),('prefix',1,1,('ref','T'))):
        try: DebtGrammar((('T',(e,)),))
        except ValueError: check(True)
        else: check(False)
    print(json.dumps({'result':'PASS','assertions':checks,
        'literal_observer_evaluations':literal_evaluations,
        'finite_DAG_exact_values':len(tokens_b),'numeric_iteration_cap':False,
        'source_oracle_certified':False,'production_algorithm':False,
        'independently_reviewed':False},sort_keys=True))


if __name__ == '__main__': main()
