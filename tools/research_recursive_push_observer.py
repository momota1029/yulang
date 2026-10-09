#!/usr/bin/env python3
"""Producer-frozen research: exact finite observers of explicit PUSH value sets.

Premises: recursive-push-algebra-attack sections 1--4 and the immutable count
DSL in research_mixed_debt_observer.py, frozen source e3ddf9f19e08be74a8467a61b5415244f6f5ac0f.
This is not a general recursive grammar/PVASS or production/source solver.
No grammar is accepted and no debt-grammar PUSH rejection is changed.

Observer tuples: const(p,n,r), hole(name), replay(x,y), mix(x), swap(x),
both_from_right(x), identity(x), prefix(p,n,x), suffix(r,x). Occurrence paths
append the actual child tuple index, including 3 for prefix and 2 for suffix.
Named holes share an entire selected value; different names select independently.

Supplying descriptors (all constants natural, plus indicated positive bounds):
  ('left_pairs',)                  all (p,n,0), independently natural p,n
  ('push_ray',)                    all (0,k,0)
  ('orbit', (p,n,r), a, b)          C^k(seed), a>=1, b>=0, k>=0
     C(W)=replay(prefix(0,a,W),const(0,0,b))
  ('growth', p0,n0,a,b)            (p0+a*k,n0+b*k,0), k>=0
  ('doubling', h,x0)               (h,h+x0*2^k,0), h,x0>=1
  ('finite', ((p,n,r), ...))       finite union, possibly empty
  ('union', (descriptor, ...))     finite union, possibly empty
Other input descriptors, expression tags and ill-formed counts are rejected.

query(expression, holes, predicate) accepts a callable on a symbolic trace
dict, path -> (Affine p, Affine n, Affine r). It must return a finite DNF:
iterable of conjunctions of eq(x,y) / ge(x,y) Constraints. () is false;
((),) is true. Affine expressions permit integer +, -, constant *. Strict
order is ge(x,y+1); disequality is ((ge(x,y+1),),(ge(y,x+1),)). Thus arbitrary
finite Boolean combinations of affine count tests are available by finite DNF.
The callable can branch on finite fixed family/filter decorations; local_filter
provides the precise fixed-family active violation predicate. It is not an
opaque oracle predicate on unbounded integers. universal_no_violation decides
the absence of choices satisfying an explicitly supplied violation predicate.
Checks observe the original supplying set; they never prune its recursion.

Small decision kernel and proof:
1. Each supplying set is a finite union of guarded affine triples over natural
   parameters, optionally requiring Pow2(t). The cancellation orbit consists
   of its raw seed, a bounded affine bulk parameter, and a signed affine tail,
   split at zero. Its bulk endpoint is computed by quotient, never unfolded.
2. Symbolic evaluation splits directed composition at q-n>=0 versus n-q>=1.
   Actual mix has disjoint cases r=0; r>=1,p+n=0; participating n>r;
   participating n<=r. Every node's triple is retained before its parent acts.
   Induction gives an exact finite union of guarded affine traces. Repeated
   holes reuse parameters. There are no auxiliary variables per observer node.
3. For s=c+sum(a_i*x_i), read synchronous natural binary digits LSB first.
   Initialize carry c, then carry' = floor((carry+sum(a_i*bit_i))/2).
   For equality additionally require an even numerator at every step and final
   carry 0. For s>=0 require final carry>=0. After L columns the carry equals
   floor(s_L/2^L), where s_L uses the L-bit natural inputs. Equation parity
   checks exactly enforce its lower L bits being zero, including negative s.
   Accepting states therefore correspond exactly to satisfying finite inputs.
   Empty digit words encode all zeros; arbitrary common zero padding is valid.
   Pow2 tracks 0/1/>1 seen one-bits and accepts exactly 1. This has no variable
   exponent arithmetic premise. Each carry stays in [-M,M],
   M=max(abs(c),sum(abs(a_i))), by induction under the floor recurrence.
   Finite product-state BFS terminates and reconstructs an exact witness.
4. Every reconstructed hole selection is evaluated again with the ordinary
   count operations from the debt tool; its entire trace, guards and predicate
   are rechecked. This checks implementation consistency, not source semantics.

There is no digit/count/depth/state search cutoff. The finite construction can
be exponentially expensive in parameters, guards, observer size and constants;
no cheap resource bound or general grammar closure is claimed. Python's own
memory/stack limits are not mathematical approximations or successful answers.
All public results and this implementation await independent review.

Focused executable check: timeout 30s bash -c 'ulimit -v 262144; exec python3 -B
tools/research_recursive_push_observer.py'. See main for deterministic coverage.
"""

from collections import deque
from dataclasses import dataclass
from itertools import product
import json
import resource
import time

import research_mixed_debt_observer as debt


def integer(x):
    if type(x) is not int:
        raise ValueError('integer required')
    return x


@dataclass(frozen=True)
class Affine:
    constant: int = 0
    terms: tuple = ()

    def __post_init__(self):
        integer(self.constant)
        terms = {}
        for i, coefficient in self.terms:
            debt.nat(i); integer(coefficient)
            terms[i] = terms.get(i, 0) + coefficient
        object.__setattr__(self, 'terms', tuple(sorted((i,a) for i,a in terms.items() if a)))

    def __add__(self, other):
        other = affine(other)
        return Affine(self.constant+other.constant, self.terms+other.terms)

    __radd__ = __add__

    def __neg__(self):
        return Affine(-self.constant, tuple((i,-a) for i,a in self.terms))

    def __sub__(self, other): return self + -affine(other)
    def __rsub__(self, other): return affine(other) + -self

    def __mul__(self, coefficient):
        integer(coefficient)
        return Affine(self.constant*coefficient, tuple((i,a*coefficient) for i,a in self.terms))

    __rmul__ = __mul__

    def value(self, parameters):
        return self.constant + sum(a*parameters[i] for i,a in self.terms)


def affine(x):
    return x if isinstance(x, Affine) else Affine(integer(x))


ZERO = Affine()


@dataclass(frozen=True)
class Constraint:
    kind: str
    expression: Affine

    def __post_init__(self):
        if self.kind not in ('eq', 'ge') or not isinstance(self.expression, Affine):
            raise ValueError('only affine equality and nonnegative inequality supported')

    def holds(self, parameters):
        s = self.expression.value(parameters)
        return s == 0 if self.kind == 'eq' else s >= 0


def eq(x,y=0): return Constraint('eq', affine(x)-y)
def ge(x,y=0): return Constraint('ge', affine(x)-y)


def conjunction(tests):
    """Validate, remove duplicates/constant truths, detect constant falsehoods."""
    result = []
    seen = set()
    for test in tests:
        if not isinstance(test, Constraint):
            raise ValueError('predicate must return finite DNF of Constraints')
        if not test.expression.terms:
            if not test.holds(()): return None
        elif test not in seen:
            seen.add(test); result.append(test)
    return tuple(result)


def triple(w):
    if not isinstance(w, tuple) or len(w) != 3:
        raise ValueError('seed/value must be an immutable natural triple')
    for count in w: debt.nat(count)
    return w


def validate_generator(g):
    if not isinstance(g, tuple) or not g or not isinstance(g[0], str):
        raise ValueError('supplying set must be a tagged immutable tuple')
    tag = g[0]
    if tag in ('left_pairs','push_ray') and len(g) == 1: return
    if tag == 'orbit' and len(g) == 4:
        triple(g[1]); debt.nat(g[2]); debt.nat(g[3])
        if g[2] < 1: raise ValueError('cancellation PUSH coefficient must be positive')
        return
    if tag == 'growth' and len(g) == 5:
        for count in g[1:]: debt.nat(count)
        return
    if tag == 'doubling' and len(g) == 3:
        for count in g[1:]: debt.nat(count)
        if not g[1] or not g[2]: raise ValueError('doubling constants must be positive')
        return
    if tag in ('finite','union') and len(g) == 2 and isinstance(g[1], tuple):
        for member in g[1]:
            triple(member) if tag == 'finite' else validate_generator(member)
        return
    raise ValueError('unsupported recursive supplying set or invalid descriptor')


def cancel(w, a, b):
    prefixed = debt.operation('prefix', [w], ('prefix',0,a,None))
    return debt.operation('replay', [prefixed,(0,0,b)], ('replay',None,None))


def orbit_phases(seed, a, b):
    """Return (first, bulk length or None, tail index, signed tail start)."""
    first = cancel(seed,a,b)
    p,n,r = first
    if not p: return first,None,1,n-r
    j = p//a if not b else min(p//a, max((n-1)//b,0))
    endpoint = (p-a*j,n-b*j,0)
    if endpoint[0]:
        endpoint = cancel(endpoint,a,b)
        tail_index = j+2
    else:
        tail_index = j+1
    assert endpoint[0] == 0
    return first,j,tail_index,endpoint[1]-endpoint[2]


def orbit_value(seed,a,b,k):
    debt.nat(k)
    if not k: return seed
    first,j,start,q = orbit_phases(seed,a,b)
    if j is not None and k <= j+1:
        p,n,_ = first
        return p-a*(k-1),n-b*(k-1),0
    q += (a-b)*(k-start)
    return 0,max(q,0),max(-q,0)


@dataclass(frozen=True)
class Selection:
    counts: tuple
    guards: tuple
    powers: tuple
    descriptor: tuple
    parameters: tuple

    def materialize(self, inputs):
        parameters = {name: expression.value(inputs) for name,expression in self.parameters}
        return {'descriptor':self.descriptor, 'parameters':parameters}


def selected_value(selection):
    g = selection['descriptor']; p = selection['parameters']; tag = g[0]
    if tag == 'left_pairs': return p['p'],p['n'],0
    if tag == 'push_ray': return 0,p['k'],0
    if tag == 'orbit': return orbit_value(g[1],g[2],g[3],p['k'])
    if tag == 'growth': return g[1]+g[3]*p['k'],g[2]+g[4]*p['k'],0
    if tag == 'doubling':
        t = p['power']
        if t < 1 or t & (t-1): raise AssertionError('invalid power witness')
        return g[1],g[1]+g[2]*t,0
    if tag == 'finite': return g[1][p['member']]
    raise AssertionError('invalid materialized selection')


class Parameters:
    def __init__(self): self.names = []

    def fresh(self, hole, name):
        i = len(self.names); self.names.append((hole,name))
        return Affine(0, ((i,1),))


def supplying(g, hole, allocator):
    tag = g[0]
    def selection(counts, guards=(), powers=(), parameters=()):
        return Selection(tuple(map(affine,counts)),tuple(guards),tuple(powers),g,tuple(parameters))
    if tag == 'left_pairs':
        p = allocator.fresh(hole,'p'); n = allocator.fresh(hole,'n')
        return (selection((p,n,0),parameters=(('p',p),('n',n))),)
    if tag == 'push_ray':
        k = allocator.fresh(hole,'k')
        return (selection((0,k,0),parameters=(('k',k),)),)
    if tag == 'growth':
        k = allocator.fresh(hole,'k')
        return (selection((g[1]+g[3]*k,g[2]+g[4]*k,0),parameters=(('k',k),)),)
    if tag == 'doubling':
        t = allocator.fresh(hole,'power'); i = t.terms[0][0]
        return (selection((g[1],g[1]+g[2]*t,0),powers=(i,),parameters=(('power',t),)),)
    if tag == 'finite':
        return tuple(selection(w,parameters=(('member',Affine(i)),)) for i,w in enumerate(g[1]))
    if tag == 'union':
        return tuple(s for member in g[1] for s in supplying(member,hole,allocator))
    if tag == 'orbit':
        seed,a,b = g[1:]
        t = allocator.fresh(hole,'phase_parameter')
        first,j,start,q = orbit_phases(seed,a,b)
        result = [selection(seed,parameters=(('k',ZERO),))]
        if j is not None:
            p,n,_ = first
            result.append(selection((p-a*t,n-b*t,0),(ge(j,t),),parameters=(('k',1+t),)))
        signed = q+(a-b)*t
        result.append(selection((0,signed,0),(ge(signed),),parameters=(('k',start+t),)))
        result.append(selection((0,0,-signed),(ge(-signed,1),),parameters=(('k',start+t),)))
        return tuple(result)
    raise AssertionError('descriptor was not validated')


def symbolic_compose(a,b):
    p,n = a; q,m = b; d = q-n
    return (((p+d,m),(ge(d),)), ((p,m-d),(ge(-d,1),)))


def symbolic_mix(w):
    p,n,r = w
    return ((w,(eq(r),)),
            (w,(ge(r,1),eq(p+n))),
            ((p,n-r,ZERO),(ge(r,1),ge(p+n,1),ge(n-r,1))),
            ((ZERO,ZERO,p+r-n),(ge(r,1),ge(p+n,1),ge(r-n))))


def symbolic_operation(e, children):
    tag = e[0]; p,n,r = w = children[0]
    if tag == 'replay':
        v = children[1]
        return tuple((out, cg+mg) for pair,cg in symbolic_compose(w[:2],v[:2])
                     for out,mg in symbolic_mix((*pair,r+v[2])))
    if tag == 'mix': return symbolic_mix(w)
    if tag == 'prefix':
        return tuple(((*pair,r),guards) for pair,guards in symbolic_compose(tuple(map(affine,e[1:3])),w[:2]))
    if tag == 'suffix': return (((p,n,r+e[1]),()),)
    if tag == 'swap': return (((r,ZERO,p),()),)
    if tag == 'both_from_right': return (((r,ZERO,r),()),)
    if tag == 'identity': return ((w,()),)
    raise AssertionError('expression was not validated')


def symbolic_traces(e, selections, path=()):
    tag = e[0]
    if tag in ('const','hole'):
        counts = tuple(map(affine,e[1:])) if tag == 'const' else selections[e[1]].counts
        return ((counts,(),{path:counts}),)
    branches = [symbolic_traces(child,selections,path+(i,)) for i,child in debt.child_occurrences(e)]
    result = []
    for children in product(*branches):
        inherited = tuple(test for _,guards,_ in children for test in guards)
        trace = {key:value for _,_,tr in children for key,value in tr.items()}
        for counts,guards in symbolic_operation(e,[w for w,_,_ in children]):
            tests = conjunction(inherited+guards)
            if tests is not None: result.append((counts,tests,{**trace,path:counts}))
    return tuple(result)


def ordinary_trace(e, chosen, path=()):
    trace = {}
    def evaluate(node, here):
        tag = node[0]
        if tag == 'const': value = node[1:]
        elif tag == 'hole': value = chosen[node[1]]
        else:
            children = [evaluate(child,here+(i,)) for i,child in debt.child_occurrences(node)]
            value = debt.operation(tag,children,node)
        trace[here] = value
        return value
    evaluate(e,path)
    return trace


def binary_witness(tests, powers, variables):
    """Finite product automaton BFS; None is an exact empty-language result."""
    tests = conjunction(tests)
    if tests is None: return None,0
    variables = tuple(sorted(set(variables)))
    powers = tuple(sorted(set(powers)))
    positions = {v:i for i,v in enumerate(variables)}
    coefficients = tuple(tuple(dict(test.expression.terms).get(v,0) for v in variables) for test in tests)
    initial = (tuple(test.expression.constant for test in tests), (0,)*len(powers))
    def accepts(state):
        carries,seen = state
        return (all(c == 0 if test.kind == 'eq' else c >= 0 for test,c in zip(tests,carries))
                and all(count == 1 for count in seen))
    predecessor = {initial:None}; queue = deque((initial,))
    while queue:
        state = queue.popleft()
        if accepts(state):
            columns = []; final = state
            while predecessor[state] is not None:
                state,bits = predecessor[state]; columns.append(bits)
            columns.reverse()
            values = {v:sum(bits[i] << j for j,bits in enumerate(columns)) for i,v in enumerate(variables)}
            assert accepts(final)
            return values,len(predecessor)
        carries,seen = state
        for bits in product((0,1),repeat=len(variables)):
            numerators = tuple(c+sum(a*bit for a,bit in zip(coefficient,bits))
                               for c,coefficient in zip(carries,coefficients))
            if any(test.kind == 'eq' and value % 2 for test,value in zip(tests,numerators)): continue
            next_seen = tuple(min(2,count+bits[positions[v]]) for count,v in zip(seen,powers))
            if 2 in next_seen: continue  # irreversible non-Pow2 state
            successor = (tuple(value//2 for value in numerators),next_seen)
            if successor not in predecessor:
                predecessor[successor] = (state,bits); queue.append(successor)
    return None,len(predecessor)


@dataclass(frozen=True)
class QueryResult:
    exists: bool
    witness: object
    statistics: dict


def query(expression, holes, predicate=None):
    """Exact existence for finite DNF on every raw and mixed syntax occurrence."""
    holes = dict(holes)
    if any(not isinstance(name,str) or not name for name in holes): raise ValueError('invalid hole name')
    for generator in holes.values(): validate_generator(generator)
    debt.validate(expression,set(holes))
    if predicate is None: predicate = lambda trace: ((),)
    if not callable(predicate): raise ValueError('predicate must be callable')
    used = set()
    def collect(e):
        if e[0] == 'hole': used.add(e[1])
        for _,child in debt.child_occurrences(e): collect(child)
    collect(expression)
    keys = tuple(sorted(used)); allocator = Parameters()
    sources = [supplying(holes[key],key,allocator) for key in keys]
    stats = {'parameters':len(allocator.names),'symbolic_branches':0,'conjunctions':0,'automaton_states':0}
    for choices in product(*sources):
        selections = dict(zip(keys,choices))
        source_guards = tuple(test for choice in choices for test in choice.guards)
        powers = tuple(i for choice in choices for i in choice.powers)
        for _,guards,trace in symbolic_traces(expression,selections):
            stats['symbolic_branches'] += 1
            # Retain parameters occurring in the trace or metadata, even when
            # unconstrained by this query, to construct a complete selection.
            variables = {i for counts in trace.values() for count in counts for i,_ in count.terms}
            variables.update(i for choice in choices for _,count in choice.parameters for i,_ in count.terms)
            variables.update(powers)
            for clause in predicate(dict(trace)):
                tests = conjunction(source_guards+guards+tuple(clause))
                if tests is None: continue
                if any(i >= len(allocator.names) for test in tests for i,_ in test.expression.terms):
                    raise ValueError('predicate may refer only to supplying parameters in the trace')
                stats['conjunctions'] += 1
                variables.update(i for test in tests for i,_ in test.expression.terms)
                assignment,states = binary_witness(tests,powers,variables)
                stats['automaton_states'] += states
                if assignment is None: continue
                parameters = tuple(assignment.get(i,0) for i in range(len(allocator.names)))
                selected = {key:selection.materialize(parameters) for key,selection in selections.items()}
                chosen = {key:selected_value(selection) for key,selection in selected.items()}
                actual = ordinary_trace(expression,chosen)
                expected = {path:tuple(count.value(parameters) for count in counts) for path,counts in trace.items()}
                if actual != expected or not all(test.holds(parameters) for test in tests):
                    raise AssertionError('symbolic/ordinary witness mismatch')
                actual_symbolic = {path:tuple(map(affine,counts)) for path,counts in actual.items()}
                if not any(all(test.holds(()) for test in clause) for clause in predicate(actual_symbolic)):
                    raise AssertionError('ordinary predicate witness mismatch')
                witness = {'selections':selected,'values':chosen,'trace':actual,
                           'parameters':parameters,'parameter_names':tuple(allocator.names)}
                return QueryResult(True,witness,stats)
    return QueryResult(False,None,stats)


def universal_no_violation(expression,holes,violation):
    """True iff no supplied choice has the caller's finite-DNF violation."""
    return not query(expression,holes,violation).exists


def local_filter(trace,path,family,allowed=None,subtract=()):
    """DNF for an actual fixed-family local active/filter violation.

    Finite head subtraction only changes family; rejecting checks leave counts
    intact. Caller chooses the syntax occurrence and its actual decorations.
    """
    residual = frozenset(family)-frozenset(subtract)
    if allowed is None or residual <= frozenset(allowed): return ()
    return ((ge(trace[path][1],1),),)


def main():
    start = time.monotonic(); checks = 0; decisions = 0; token_checks = 0; orbit_checks = 0
    def check(condition):
        nonlocal checks
        checks += 1
        assert condition, checks
    def decide(e,holes,predicate,expected):
        nonlocal decisions
        result = query(e,holes,predicate); decisions += 1
        check(result.exists == expected)
        return result
    H = lambda name: ('hole',name)
    C = lambda p,n,r: ('const',p,n,r)
    def counts(path,expected):
        return lambda trace: (tuple(eq(x,y) for x,y in zip(trace[path],expected)),)
    all_pairs = {'x':('left_pairs',)}
    decide(H('x'),all_pairs,counts((),(1,1,0)),True)
    decide(H('x'),all_pairs,lambda tr: ((eq(tr[()][0],tr[()][1]),ge(tr[()][0],1),eq(sum(tr[()]),0)),),False)
    huge = 10**30
    result = decide(H('x'),all_pairs,counts((),(huge,huge+1,0)),True)
    check(result.witness['values']['x'] == (huge,huge+1,0))
    decide(H('x'),all_pairs,lambda tr: ((ge(-tr[()][0],1),),),False)
    decide(H('x'),{'x':('push_ray',)},counts((),(0,2**20,0)),True)
    doubling = {'x':('doubling',1,1)}
    result = decide(H('x'),doubling,counts((),(1,1+2**20,0)),True)
    check(result.witness['selections']['x']['parameters']['power'] == 2**20)
    decide(H('x'),doubling,counts((),(1,4,0)),False)
    decide(H('x'),doubling,counts((),(1,2,0)),True)
    decide(H('x'),doubling,counts((),(1,1,0)),False)
    shared = ('replay',H('x'),H('x'))
    independent = ('replay',H('x'),H('y'))
    decide(shared,doubling,counts((),(1,4,0)),False)
    decide(independent,{'x':doubling['x'],'y':doubling['x']},counts((),(1,4,0)),True)
    finite = ('finite',((0,1,0),(1,0,0)))
    shared = ('replay',H('x'),('swap',H('x')))
    independent = ('replay',H('x'),('swap',H('y')))
    decide(shared,{'x':finite},counts((),(0,0,0)),False)
    decide(independent,{'x':finite,'y':finite},counts((),(0,0,0)),True)
    raw = ('mix',('suffix',3,('prefix',0,2,H('x'))))
    source = {'x':('finite',((0,0,4),))}
    def raw_predicate(tr):
        return ((eq(tr[(1,2)][1],2),eq(tr[(1,)][2],7),eq(tr[()][2],5)),)
    decide(raw,source,raw_predicate,True)
    decide(('both_from_right',H('x')),source,counts((),(4,0,4)),True)
    decide(('swap',H('x')),source,counts((),(4,0,0)),True)
    decide(H('x'),{'x':('growth',3,5,2,3)},counts((),(3+2*huge,5+3*huge,0)),True)
    decide(H('x'),{'x':('growth',3,5,2,3)},counts((),(5,9,0)),False)
    decide(H('x'),{'x':('growth',0,0,0,0)},counts((),(0,0,0)),True)
    # Exact accelerated orbits versus ordinary repeated count application.
    for seed in product(range(4),repeat=3):
        for a in range(1,4):
            for b in range(4):
                w = seed
                for k in range(10):
                    orbit_checks += 1; check(orbit_value(seed,a,b,k) == w)
                    w = cancel(w,a,b)
    for seed,a,b,expected in (((9,11,0),2,3,(0,0,2)),((0,0,5),2,3,(0,0,6)),
                              ((5,0,0),2,0,(1,0,0)),((4,0,0),2,0,(0,0,0)),
                              ((0,0,0),2,0,(0,6,0)),((1,0,0),2,3,(0,0,2))):
        decide(H('x'),{'x':('orbit',seed,a,b)},counts((),expected),True)
    decide(H('x'),{'x':('orbit',(huge,huge,0),1,1)},counts((),(1,1,0)),True)
    decide(H('x'),{'x':('orbit',(9,11,0),2,3)},counts((),(8,8,0)),False)
    decide(H('x'),{'x':('orbit',(0,0,5),3,1)},counts((),(0,huge+1,0)),True)
    decide(H('x'),{'x':('finite',())},None,False)
    decide(C(0,0,0),{'unused':('finite',())},None,True)
    decide(H('x'),{'x':('union',())},None,False)
    decide(H('x'),{'x':('union',(('push_ray',),('finite',((1,1,1),))))},counts((),(1,1,1)),True)
    # Finite DNF and explicit local check placement, without generator pruning.
    predicate = lambda tr: ((eq(tr[()][0],7),),(eq(tr[()][1],11),))
    decide(H('x'),all_pairs,predicate,True)
    decide(raw,source,lambda tr: local_filter(tr,(1,2),{'a'},set()),True)
    decide(raw,source,lambda tr: local_filter(tr,(),{'a'},set()),False)
    decide(raw,source,lambda tr: local_filter(tr,(1,2),{'a'},set(),{'a'}),False)
    check(universal_no_violation(H('x'),doubling,lambda tr: ((ge(1,tr[()][1]),),)))
    # Literal token reference shares only the supplied algebra, not count ops.
    expressions = (H('x'),('mix',H('x')),('swap',H('x')),('both_from_right',H('x')),
                   ('prefix',1,2,H('x')),('suffix',2,H('x')),
                   ('replay',H('x'),C(1,2,3)),('replay',C(1,2,3),H('x')),
                   ('replay',('prefix',0,2,H('x')),('swap',H('x'))),raw,
                   ('identity',('suffix',1,('both_from_right',H('x')))))
    for w in product(range(3),repeat=3):
        literal_w = debt.literal(C(*w),{})
        for e in expressions:
            literal_value = debt.decode(debt.literal(e,{'x':literal_w}))
            result = decide(e,{'x':('finite',(w,))},counts((),literal_value),True)
            check(result.witness['trace'][()] == literal_value); token_checks += 1
            # Attack a wrong root tuple; no search depth proxy is involved.
            wrong = (literal_value[0]+1,*literal_value[1:])
            decide(e,{'x':('finite',(w,))},counts((),wrong),False)
    # Negative constants/coefficient parity and all-zero empty-word acceptance.
    for p in range(8):
        for n in range(8):
            x = Affine(0,((0,1),)); y = Affine(0,((1,1),))
            constraints = (eq(x,p),eq(y,n),ge(2*x-3*y,-4))
            witness,_ = binary_witness(constraints,(),(0,1))
            check((witness is not None) == (2*p-3*n >= -4))
    witness,_ = binary_witness((eq(Affine(-2,((0,2),))),),(),(0,))
    check(witness == {0:1})
    witness,_ = binary_witness((eq(Affine(-1,((0,2),))),),(),(0,))
    check(witness is None)
    invalid = (('grammar',()),('doubling',0,1),('orbit',(0,0,0),0,1),('growth',0,0,True,1),('finite',[(0,0,0)]))
    for g in invalid:
        try: query(H('x'),{'x':g})
        except ValueError: check(True)
        else: check(False)
    for e in (('ref','x'),('let','x','T',H('x')),('bogus',H('x')),('prefix',0,-1,H('x'))):
        try: query(e,all_pairs)
        except ValueError: check(True)
        else: check(False)
    usage = resource.getrusage(resource.RUSAGE_SELF)
    print(json.dumps({'status':'PASS','assertions':checks,'decisions':decisions,
                      'literal_observers':token_checks,'orbit_comparisons':orbit_checks,
                      'wall_seconds':time.monotonic()-start,'user_seconds':usage.ru_utime,
                      'system_seconds':usage.ru_stime,'max_rss_kib':usage.ru_maxrss},sort_keys=True))


if __name__ == '__main__': main()
