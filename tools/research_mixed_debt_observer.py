#!/usr/bin/env python3
"""Research implementation: finite debt grammar, finite observer.

Governing premises: notes/progress/2026-10-10-mixed-replay-observer-construction.md
sections 2–5, published main commit 3b32ed3afa49c7d4105da46ba7783524c9fdb35b.
One ID, natural counts, fixed family; no actual source/gamma/rollback claim.
Immutable tuples: const(p,n,r), ref(name), hole(name), replay(x,y), unary
mix/swap/both_from_right/identity, prefix(p,n,x), suffix(r,x), and grammar-only
let(variable,nonterminal,body)/bound(variable). Refs choose independently;
let binds one chosen debt state to every bound occurrence. Named observer holes
share one selection. Grammar excludes PUSH, holes, and mix. Query debt saturation
uses B+1; the finite continuation then evaluates exact counts without clipping.
query_traces reports observations at every stable syntax occurrence path.

Prior auxiliary snapshot (not governing main note): baseline
 e2f29d0a30f81616b4963cb1b2a42d9a798af2b3; algebra SHA-256
954dcda5f7f884f2489fbd58c21fb1ba3214ccee915366baa5f7ce0029a21330;
auxiliary note SHA-256
14cc550ba447df7debd4bf405f6fc549d147ed40e34cd1513999f9f60e551b47.
Check: timeout 30s bash -c 'ulimit -v 262144; exec python3 -B tools/research_mixed_debt_observer.py'
Expected deterministic evidence: 147 assertions, 440 literal observer
evaluations over 11 exact finite-DAG values. Counts are printed by main. Literal
reference shares stated semantics but no count operations. Independent review
of the solver and terminal repairs passed; a subsequent primary-only reference
repair keys let witnesses by syntax occurrence. The results note records the
reviewed snapshot and verification boundary. No source Oracle, production tests,
benchmark, or full source-filter evidence.
"""
from dataclasses import dataclass
from itertools import product
import json


def nat(x):
    if type(x) is not int or x < 0:
        raise ValueError('counts must be natural integers')
    return x


def validate(e, names, grammar=False, scope=frozenset()):
    if not isinstance(e, tuple) or not e or not isinstance(e[0], str):
        raise ValueError('expression must be a nonempty tagged tuple')
    tag = e[0]
    arities = {'const': 4, 'ref': 2, 'hole': 2, 'replay': 3,
               'swap': 2, 'both_from_right': 2, 'identity': 2,
               'mix': 2, 'prefix': 4, 'suffix': 3, 'let': 4, 'bound': 2}
    if tag not in arities or len(e) != arities[tag]:
        raise ValueError('unsupported operation or invalid arity')
    if tag == 'bound':
        if not grammar or not isinstance(e[1],str) or e[1] not in scope:
            raise ValueError('unbound or unsupported variable')
        return 0
    if tag == 'let':
        if (not grammar or not isinstance(e[1],str) or not e[1]
                or not isinstance(e[2],str) or e[2] not in names):
            raise ValueError('invalid shared binding')
        return validate(e[3], names, grammar, scope | {e[1]})
    if tag == 'const':
        for c in e[1:]:
            nat(c)
        if grammar and e[2]:
            raise ValueError('PUSH in recursive grammar')
        return e[2]
    if tag in ('ref', 'hole'):
        if tag != ('ref' if grammar else 'hole') or not isinstance(e[1], str) or e[1] not in names:
            raise ValueError('unknown or unsupported reference')
        return 0
    if grammar and tag == 'mix':
        raise ValueError('unsupported grammar operation')
    if tag == 'prefix':
        nat(e[1]); nat(e[2])
        if grammar and e[2]:
            raise ValueError('PUSH in recursive grammar')
        return e[2] + validate(e[3], names, grammar, scope)
    if tag == 'suffix':
        nat(e[1])
        return validate(e[2], names, grammar, scope)
    return sum(validate(child, names, grammar, scope) for child in e[1:])


def compose(a, b):
    p,n = a; q,m = b
    return p + max(q-n, 0), m + max(n-q, 0)


def mix(w):
    p,n,r = w
    if not r or not p+n:
        return w
    p,n = compose((p,n), (r,0))
    return (p,n,0) if n else (0,0,p)


def operation(tag, children, e):
    w = children[0]; p,n,r = w
    if tag == 'replay':
        v = children[1]
        a,b = compose(w[:2], v[:2])
        return mix((a,b,r+v[2]))
    if tag == 'mix': return mix(w)
    if tag == 'swap': return r,0,p
    if tag == 'both_from_right': return r,0,r
    if tag == 'identity': return w
    if tag == 'prefix':
        a,b = compose(e[1:3], w[:2])
        return a,b,r
    if tag == 'suffix': return p,n,r+e[1]
    raise ValueError('unsupported operation')


def values(e, env, reference_tag, cap=None, bound=None):
    """Set interpretation: refs independent, let/bound explicitly correlated."""
    bound = {} if bound is None else bound
    tag = e[0]
    if tag == 'let':
        out = set()
        for w in env[e[2]]:
            out.update(values(e[3],env,reference_tag,cap,{**bound,e[1]:w}))
    elif tag == 'bound': out = {bound[e[1]]}
    elif tag == 'const': out = {e[1:]}
    elif tag == reference_tag: out = env[e[1]]
    else:
        children = e[3:] if tag == 'prefix' else e[2:] if tag == 'suffix' else e[1:]
        out = {operation(tag, ws, e) for ws in product(*(values(c,env,reference_tag,cap,bound) for c in children))}
    if cap is not None:
        return {(min(p,cap),n,min(r,cap)) for p,n,r in out}
    return out


@dataclass(frozen=True)
class Grammar:
    """Immutable exact model snapshot, not a runtime rollback mechanism."""
    rules: tuple

    def __post_init__(self):
        # Materialize iterators exactly once and recursively require tuples.
        rules = tuple((name, tuple(productions)) for name,productions in self.rules)
        names = [name for name,_ in rules]
        if any(not isinstance(n,str) or not n for n in names) or len(set(names)) != len(names):
            raise ValueError('invalid or duplicate nonterminal')
        for _,productions in rules:
            for e in productions: validate(e, set(names), True)
        object.__setattr__(self, 'rules', rules)

    def add(self, name, expression):
        if name not in dict(self.rules): raise ValueError('unknown nonterminal')
        return Grammar(tuple((n, ps+(expression,) if n==name else ps) for n,ps in self.rules))

    def saturate(self, k):
        nat(k)
        if k < 1: raise ValueError('cap must be positive')
        env = {n:set() for n,_ in self.rules}
        rounds = additions = 0
        while True:
            rounds += 1
            changed = False
            for n,ps in self.rules:
                for e in ps:
                    new = values(e, env, 'ref', k) - env[n]
                    if new:
                        env[n].update(new); additions += len(new); changed = True
            if not changed: break
        assert all(len(v) <= (k+1)**2 for v in env.values())
        return {n:frozenset(v) for n,v in env.items()}, {'rounds':rounds,'additions':additions}

    def query_traces(self, expression, holes):
        """Set of correlated traces: ((occurrence_path, observation), ...).

        Paths are tuples of child tuple indices, root (). Observations are
        (exact active n, left debt present, right debt present, left entry,
        identity). Debt magnitudes in representatives are query markers only.
        """
        holes = dict(holes)
        names = dict(self.rules)
        if any(not isinstance(h,str) or not isinstance(nt,str) or nt not in names for h,nt in holes.items()):
            raise ValueError('invalid hole binding')
        b = validate(expression, set(holes))
        k = b+1
        env, stats = self.saturate(k)
        def used(e):
            if e[0] == 'hole': return {e[1]}
            return set().union(*(used(c) for _,c in child_occurrences(e)))
        keys = tuple(sorted(used(expression)))
        traces = set()
        for choice in product(*(env[holes[h]] for h in keys)):
            selected = dict(zip(keys,choice))
            trace = []
            def evaluate(e, path):
                if e[0] == 'const': w = e[1:]
                elif e[0] == 'hole': w = selected[e[1]]
                else:
                    ws = [evaluate(c,path+(i,)) for i,c in child_occurrences(e)]
                    w = operation(e[0],ws,e)
                trace.append((path,observe(w)))
                return w
            evaluate(expression,())
            traces.add(tuple(sorted(trace)))
        return frozenset(traces), {'push_mass':b,'cap':k,**stats}

    def query(self, expression, holes):
        """Root-only projection of the per-node correlated observation traces."""
        traces, stats = self.query_traces(expression,holes)
        return frozenset(dict(trace)[()] for trace in traces), stats


def child_occurrences(e):
    tag = e[0]
    if tag in ('const','ref','hole','bound'): return ()
    indices = (3,) if tag in ('prefix','let') else (2,) if tag == 'suffix' else range(1,len(e))
    return tuple((i,e[i]) for i in indices)


def observe(w):
    p,n,r = w
    return n, p>0, r>0, p+n>0, p+n+r==0


def local_terminal(observation, family, allowed=None, subtract=()):
    """Finite fixed-family filter and terminal head subtraction only.

    Terminal subtraction changes family, not counts. Return active count and
    local left-entry presence, residual family, and filter violation.
    Counts and presence survive empty families and rejecting checks.
    No mixed-family replay, source filters, or public compact collector claim.
    """
    n,p,r,left,identity = observation
    residual = frozenset(family) - frozenset(subtract)
    violation = n > 0 and allowed is not None and not residual <= frozenset(allowed)
    return n, bool(p or n > 0), residual, violation


def literal(e, env, bound=None, choices=None, path=()):
    """Independent tokens; choices maps let occurrence paths to token witnesses.

    Caller enumerates available witnesses for finite-DAG evidence; no count
    operation or saturation is invoked by this reference evaluator.
    Root path is (); descendants append their expression tuple index. Each
    binding occurrence selects independently, including shadowed variable names.
    """
    def reduce(seq):
        out=[]
        for t in seq:
            if t=='D' and out and out[-1]=='U': out.pop()
            else: out.append(t)
        return tuple(out)
    def mx(a,b):
        if not a or not b: return a,b
        out=reduce(a+b)
        return (out,()) if 'U' in out else ((),out)
    bound = {} if bound is None else bound
    tag=e[0]
    if tag=='let':
        if choices is None or path not in choices:
            raise ValueError('literal let requires supplied token witness choice')
        return literal(e[3],env,{**bound,e[1]:choices[path]},choices,path+(3,))
    if tag=='bound': return bound[e[1]]
    if tag=='const': return tuple('D'*e[1]+'U'*e[2]),tuple('D'*e[3])
    if tag in ('ref','hole'): return env[e[1]]
    index=3 if tag=='prefix' else 2 if tag=='suffix' else 1
    a,b=literal(e[index],env,bound,choices,path+(index,))
    if tag=='replay':
        c,d=literal(e[2],env,bound,choices,path+(2,)); return mx(reduce(a+c),b+d)
    if tag=='mix': return mx(a,b)
    if tag=='swap': return b,tuple(t for t in a if t=='D')
    if tag=='both_from_right': return b,b
    if tag=='identity': return a,b
    if tag=='prefix': return reduce(tuple('D'*e[1]+'U'*e[2])+a),b
    if tag=='suffix': return a,tuple('D'*e[1])+b
    raise ValueError('unsupported operation')


def decode(w):
    a,b=w
    return a.count('D'),a.count('U'),len(b)


def main():
    checks=0
    def check(condition):
        nonlocal checks
        checks+=1
        assert condition, checks
    I=('const',0,0,0); R=lambda r:('const',0,0,r)
    H=lambda h:('hole',h); T=('ref','T')
    g=Grammar((('T',(R(1),('replay',T,R(4)))),))
    for k in range(1,15):
        env,_=g.saturate(k)
        check(env['T']==frozenset((0,0,x) for x in {min(1+4*j,k) for j in range(k+1)}))
    small,_=g.query(('replay',('const',0,2,0),H('x')),{'x':'T'})
    large,stats=g.query(('replay',('const',0,10,0),H('x')),{'x':'T'})
    check(stats['cap']==11 and (9,False,False,True,False) in large)
    check((5,False,False,True,False) in large)  # permanent cap 1 loses R_5
    check((1,False,False,True,False) in small)
    powers=Grammar((('T',(R(1),('replay',I,('both_from_right',T)))),))
    for k in range(1,20):
        env,_=powers.saturate(k)
        check(env['T']==frozenset((0,0,x) for x in {min(2**j,k) for j in range(k.bit_length()+1)}))
    raw=Grammar((('T',(R(3),('both_from_right',R(2)),('swap',R(4)))),))
    check(raw.saturate(5)[0]['T']==frozenset(((0,0,3),(2,0,2),(4,0,0))))
    old=Grammar((('T',(I,)),)); new=old.add('T',R(2))
    check(old.saturate(3)[0]['T']==frozenset(((0,0,0),)))
    check(len(new.saturate(3)[0]['T'])==2)
    check(old.query(H('x'),{'x':'T'})[0]==frozenset(((0,False,False,False,True),)))
    empty=Grammar((('T',(('replay',T,T),)),))
    check(not empty.saturate(3)[0]['T'])
    check(not empty.query(H('x'),{'x':'T'})[0])
    check(empty.query(I,{'unused':'T'})[0]==frozenset(((0,False,False,False,True),)))
    iterator=Grammar(iter((('T',iter((R(1),R(2)))),)))
    check(len(iterator.saturate(3)[0]['T'])==2)
    # Productive seed appearing after recursive rule: no loss of pending growth.
    pending=Grammar((('T',(('replay',T,R(1)),R(1))),))
    check(pending.saturate(7)[0]['T']==frozenset((0,0,j) for j in range(1,8)))
    correlation=Grammar((('T',(I,R(2))),))
    shared=('replay',('prefix',0,1,H('x')),('swap',H('x')))
    independent=('replay',('prefix',0,1,H('x')),('swap',H('y')))
    a,_=correlation.query(shared,{'x':'T'})
    b,_=correlation.query(independent,{'x':'T','y':'T'})
    check(a < b)
    check(local_terminal((2,False,False,True,False),{'a','b'},{'b'},{'a'})==(2,True,frozenset({'b'}),False))
    check(local_terminal((2,False,False,True,False),{'a'},set(),{'a'})==(2,True,frozenset(),False))
    check(local_terminal((1,False,False,True,False),{'a'},set())==(1,True,frozenset({'a'}),True))
    check(local_terminal((1,False,False,True,False),{'a'},set(),{'a'})==(1,True,frozenset(),False))
    check(local_terminal((0,True,False,True,False),set(),set())==(0,True,frozenset(),False))
    # Grammar sharing differs from independent references.
    L1=('const',1,0,0)
    sharing=Grammar((('T',(L1,R(1))),
                     ('U',(('let','t','T',('replay',('bound','t'),('swap',('bound','t')))),)),
                     ('V',(('replay',T,('swap',T)),))))
    share_env,_=sharing.saturate(3)
    check(share_env['U']==frozenset(((0,0,2),)))
    check(share_env['V']==frozenset(((2,0,0),(0,0,2))))
    chosen=('let','t','T',('replay',('bound','t'),('swap',('bound','t'))))
    check({decode(literal(chosen,{},choices={():literal(c,{})})) for c in (L1,R(1))}=={(0,0,2)})
    # Same-name binders have different syntax owners, with lexical restoration.
    t=('bound','t')
    shadowing=(
        (('let','t','A',('replay',t,('let','t','B',t))),
         {():literal(L1,{}),(3,2):literal(R(2),{})}),
        (('let','t','A',('replay',('let','t','B',t),t)),
         {():literal(L1,{}),(3,1):literal(R(2),{})}),
        (('replay',('let','t','A',t),('let','t','B',t)),
         {(1,):literal(L1,{}),(2,):literal(R(2),{})}),
    )
    for expression,witnesses in shadowing:
        scoped=Grammar((('A',(L1,)),('B',(R(2),)),('C',(expression,))))
        check(scoped.saturate(4)[0]['C']==frozenset(((0,0,3),)))
        check(decode(literal(expression,{},choices=witnesses))==(0,0,3))
    empty_shared=Grammar((('E',()),('U',(('let','t','E',I),))))
    check(not empty_shared.saturate(3)[0]['U'])
    # Internal raw PUSH presence is visible even when an outer swap drops it.
    traces,_=old.query_traces(('swap',('prefix',0,2,H('x'))),{'x':'T'})
    check(traces==frozenset(((((),(0,False,False,False,True)),
                              ((1,),(2,False,False,True,False)),
                              ((1,3),(0,False,False,False,True))),)))
    # A finite raw wrapper may exceed the debt marker; only saturation clips.
    raw_trace,_=old.query_traces(('suffix',9,('prefix',0,2,H('x'))),{'x':'T'})
    check(dict(next(iter(raw_trace)))[()]==(2,False,True,True,False))
    check(values(('suffix',9,('prefix',0,2,H('x'))),{'x':{(0,0,0)}},'hole')=={(0,2,9)})
    # Transcribed primitive three-NT Value circuit arithmetic regression.
    # Argument Effect annotation is NegRow([],Top), hence swap, not both.
    SF=('ref','S_F'); SC=('ref','S_C'); SR=('ref','S_R')
    circuit=Grammar((('S_F',(R(1),('replay',SR,R(1)))),
                     ('S_C',(('replay',SF,L1),)),
                     ('S_R',(('replay',SC,R(2)),))))
    for k in range(1,12):
        check(circuit.saturate(k)[0]['S_F']==frozenset((0,0,min(1+4*j,k)) for j in range(k+1)))
    circuit_observers=(('swap',H('x')),('swap',H('x')),
                       ('mix',('prefix',0,1,H('x'))),
                       ('mix',('prefix',1,0,H('x'))))
    for expr in circuit_observers:
        got,_=circuit.query(expr,{'x':'S_F'})
        expected=frozenset(observe(decode(literal(expr,{'x':literal(R(1+4*j),{})}))) for j in range(4))
        check(got==expected)
    invalid_grammars=[(('T',(('const',0,1,0),)),), (('T',(('prefix',0,1,T),)),),
                      (('T',(('ref','missing'),)),), (('T',(('swap',T,T),)),),
                      (('T',(('const',-1,0,0),)),), (('T',(('bogus',T),)),),
                      (('T',(('suffix',True,T),)),),
                      (('T',(('bound','t'),)),),
                      (('T',(('let','t','missing',I),)),),
                      (('T',(('let','t','T',('prefix',0,1,('bound','t'))),)),),
                      (('T',(('let','t','T'),)),),
                      (('T',(('let','','T',I),)),),
                      (('T',(('let','t','T',('bound','missing')),)),)]
    for rules in invalid_grammars:
        try: Grammar(rules)
        except ValueError: check(True)
        else: check(False)
    for expr in [('ref','T'),('hole','bad'),('replay',H('x')),('prefix',0,-1,H('x')),('bogus',H('x')),('bound','t'),('let','t','T',I)]:
        try: old.query(expr,{'x':'T'})
        except ValueError: check(True)
        else: check(False)
    # Independent exhaustive finite DAG denotation (no bounded recursive trees).
    # A chooses 3 constants; B independently chooses 9 replay sibling pairs,
    # plus raw wrappers. Exhaustive token interpretation supplies exact output.
    constants=(I,R(1),('const',2,0,1))
    refs=('ref','A')
    productions=(('replay',refs,refs),('both_from_right',refs),('swap',refs),('prefix',1,0,refs),('suffix',2,refs))
    dag=Grammar((('A',constants),('B',productions)))
    exact_a={literal(c,{}) for c in constants}
    exact_b=set()
    for production in productions:
        if production[0]=='replay':
            for x,y in product(exact_a,repeat=2):
                # Rename siblings in literal reference to keep independent choices.
                exact_b.add(literal(('replay',('ref','x'),('ref','y')),{'x':x,'y':y}))
        else:
            for x in exact_a: exact_b.add(literal(production,{'A':x}))
    for k in range(1,8):
        env,_=dag.saturate(k)
        check(env['B']==frozenset((min(p,k),0,min(r,k)) for p,n,r in map(decode,exact_b)))
    observations=0
    for push in range(5):
        for outer in ('identity','mix','swap','both_from_right'):
            for side in ('left','right'):
                core=('replay',('const',0,push,0),H('x')) if side=='left' else ('replay',H('x'),('const',0,push,0))
                expr=(outer,core)
                got,_=dag.query(expr,{'x':'B'})
                expected=frozenset(observe(decode(literal(expr,{'x':w}))) for w in exact_b)
                check(got==expected); observations+=len(exact_b)
    # B counts expanded occurrence mass including wrappers and constant leaves.
    expr=('replay',('prefix',0,2,H('x')),('prefix',0,3,('const',0,4,0)))
    check(old.query(expr,{'x':'T'})[1]['push_mass']==9)
    print(json.dumps({'result':'PASS','assertions':checks,'literal_observer_evaluations':observations,
                      'finite_DAG_exact_values':len(exact_b),'numeric_iteration_cap':False,
                      'source_oracle_certified':False},sort_keys=True))

if __name__=='__main__': main()
