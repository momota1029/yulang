#!/usr/bin/env python3
"""Bounded differential execution probe, not compiler inference.

Canonical scoped call/compose trees match yu-hir's research scoped tests.
Authority: typed-computation-core-elaboration §§3,6 and ordinary-computation-
semantics-package §§3–4. Only Value entry is modeled. Primitive Int→Int
relations are finite premises, not inferred Function interfaces. Receipts and
lexical paths are observable tokens; no actual (nu,K,D) satisfaction, callback
admission, handler capture, effect-row solver, principal adequacy or production
adequacy is established. Delete this standalone probe to roll it back.

The recursive source interpreter and generated-core instruction machine share
AST/primitive relation data and observation vocabulary, but no execution or
continuation machinery. Fresh generator runs enumerate response paths; within
each run a suspended generator resumes in place without replaying receipt.
"""
from dataclasses import dataclass
from itertools import product

VALUES = STATES = (0, 1)
# Modes exhaust this declared tiny primitive family, not all possible functions.
G_MODES = ('return', 'request')
F_MODES = ('state', 'xor-state')


@dataclass(frozen=True)
class Expr:
    tag: str
    data: object
    children: tuple = ()


def var(i):
    return Expr('name', i)


def lam(i, body):
    return Expr('lambda', i, (body,))


def app(i, f, x):
    return Expr('apply', i, (f, x))


def tree(which):
    body = app(0, var(0), var(1)) if which == 'call' else app(
        0, var(0), app(1, var(1), var(2)))
    for binder in reversed(range(2 if which == 'call' else 3)):
        body = lam(binder, body)
    return body


@dataclass(frozen=True)
class Closure:
    binder: int
    body: object
    env: tuple


@dataclass(frozen=True)
class Primitive:
    name: str
    mode: str


def harness(which, gm, fm, x):
    expr = tree(which)
    args = [Primitive('f', fm)]
    if which == 'compose':
        args.append(Primitive('g', gm))
    args.append(x)
    for i, value in enumerate(args):
        expr = app(100 + i, expr, Expr('literal', value))
    return expr


def event(kind, occurrence, scope, detail=None):
    return (kind, occurrence, scope, detail)


def suffix(i, scope):
    return (('rebind', i, scope), ('body', i, scope), ('return', i, scope))


def source(expr, state):
    """Direct source application: receive argument code, then enter it."""
    trace = []
    pending = []

    def run(e, env):
        nonlocal state
        if e.tag == 'name':
            return dict(env)[e.data]
        if e.tag == 'literal':
            return e.data
        if e.tag == 'lambda':
            return Closure(e.data, e.children[0], env)
        f = yield from run(e.children[0], env)
        i, scope = e.data, tuple(k for k, _ in env)
        trace.append(event('receipt', i, scope))
        saved = list(pending)
        pending[:0] = suffix(i, scope)
        trace.append(event('force', i, scope))
        value = yield from run(e.children[1], env)
        pending.pop(0)
        trace.append(event('rebind', i, scope, value))
        pending.pop(0)
        if isinstance(f, Closure):
            result = yield from run(f.body, f.env + ((f.binder, value),))
        else:
            assert isinstance(value, int) and value in VALUES
            trace.append(event('primitive', i, scope, (f.name, value, state)))
            if f.name == 'g' and f.mode == 'request':
                q = ('g-request', i, scope, ('origin', i, scope), value)
                trace.append(event('request', i, scope, q))
                response, state = yield ('pending', q, state, tuple(trace), tuple(pending))
                trace.append(event('resume', i, scope, (response, state)))
                result = response
            elif f.name == 'g':
                result = value
            else:
                result = state if f.mode == 'state' else value ^ state
        pending.pop(0)
        assert pending == saved
        trace.append(event('return', i, scope))
        return result

    value = yield from run(expr, ())
    return ('complete', value, state, tuple(trace), tuple(pending))


def compile_core(e):
    """Generate finite Return/lookup/Closure/Apply code; argument stays inert."""
    if e.tag == 'apply':
        return ('apply', e.data, compile_core(e.children[0]),
                ('delay', compile_core(e.children[1])))
    if e.tag == 'lambda':
        return ('closure', e.data, compile_core(e.children[0]))
    return (e.tag, e.data)


def core(code, state, mutant=None):
    """Independent stack machine; frames are the state-threaded bind suffix."""
    work = [('eval', code, ())]
    value = None
    trace = []
    while work:
        instruction = work.pop()
        op = instruction[0]
        if op == 'eval':
            _, node, env = instruction
            tag = node[0]
            if tag == 'name':
                value = dict(env)[node[1]]
            elif tag == 'literal':
                value = node[1]
            elif tag == 'closure':
                value = Closure(node[1], node[2], env)
            else:
                _, i, callee, delay = node
                assert delay[0] == 'delay'
                work.extend([('invoke', i, delay[1], env), ('eval', callee, env)])
        elif op == 'invoke':
            _, i, argument, env = instruction
            i = 0 if mutant == 'occurrence-collapse' and i < 100 else i
            scope = tuple(k for k, _ in env)
            f = value
            if mutant != 'eager-force':
                trace.append(event('receipt', i, scope))
            trace.append(event('force', i, scope))
            work.extend([('return', i, scope), ('body', i, scope, f),
                         ('rebind', i, scope), ('eval', argument, env)])
            if mutant == 'eager-force':
                # Deliberately place receipt after argument execution.
                work.insert(len(work) - 3, ('late-receipt', i, scope))
        elif op in ('rebind', 'return', 'late-receipt'):
            _, i, scope = instruction
            kind = 'receipt' if op == 'late-receipt' else op
            trace.append(event(kind, i, scope, value if op == 'rebind' else None))
        elif op == 'body':
            _, i, scope, f = instruction
            if isinstance(f, Closure):
                work.append(('eval', f.body, f.env + ((f.binder, value),)))
                continue
            assert isinstance(value, int) and value in VALUES
            trace.append(event('primitive', i, scope, (f.name, value, state)))
            if f.name == 'g' and f.mode == 'request':
                q = ('g-request', i, scope, ('origin', i, scope), value)
                trace.append(event('request', i, scope, q))
                frames = tuple((frame[0], frame[1], frame[2])
                               for frame in reversed(work))
                value, state = yield ('pending', q, state, tuple(trace), frames)
                trace.append(event('resume', i, scope, (value, state)))
                if mutant == 'receipt-replay':
                    trace.append(event('receipt', i, scope))
                if mutant == 'dropped-suffix':
                    work.clear()
            elif f.name == 'g':
                pass
            else:
                value = state if f.mode == 'state' else value ^ state
    return ('complete', value, state, tuple(trace), ())


def observe(factory, responses=()):
    evaluator = factory()
    observations = []
    try:
        observations.append(next(evaluator))
        for response in responses:
            observations.append(evaluator.send(response))
    except StopIteration as done:
        observations.append(done.value)
    return tuple(observations)


def main():
    cases = list(product(('call', 'compose'), G_MODES, F_MODES, VALUES, STATES))
    comparisons = pending = completions = 0
    witnesses = {}
    for case in cases:
        which, gm, fm, x, state = case
        expr = harness(which, gm, fm, x)
        code = compile_core(expr)
        paths = [()]
        if which == 'compose' and gm == 'request':
            paths += [(r,) for r in product(VALUES, STATES)]
        for responses in paths:
            expected = observe(lambda: source(expr, state), responses)
            actual = observe(lambda: core(code, state), responses)
            assert expected == actual, (case, responses, expected, actual)
            comparisons += 1
            pending += sum(o[0] == 'pending' for o in expected)
            completions += sum(o[0] == 'complete' for o in expected)
            for mutant in ('eager-force', 'receipt-replay',
                           'occurrence-collapse', 'dropped-suffix'):
                bad = observe(lambda: core(code, state, mutant), responses)
                if bad != expected:
                    # Exhaustive lexicographic shrinking within the declared domain.
                    key = (len(responses), case, responses)
                    if mutant not in witnesses or key < witnesses[mutant]:
                        witnesses[mutant] = key
    assert len(witnesses) == 4, witnesses
    # A changed resumed store must reach f; it is not restored at entry/return.
    probe = harness('compose', 'request', 'state', 0)
    for resumed_state in STATES:
        observed = observe(lambda: core(compile_core(probe), 0),
                           ((1, resumed_state),))
        assert observed[-1][1:3] == (resumed_state, resumed_state)
        prefix = observed[0]
        assert prefix[-1][:4] == (
            ('return', 1, (0, 1, 2)), ('rebind', 0, (0, 1, 2)),
            ('body', 0, (0, 1, 2)), ('return', 0, (0, 1, 2)))
    print(f'PASS: {len(cases)} finite cases; {comparisons} response-path comparisons; '
          f'{pending} pending-prefix observations; {completions} complete observations')
    for mutant, witness in sorted(witnesses.items()):
        _, case, responses = witness
        print(f'KILLED {mutant}: smallest domain witness={case}; responses={responses}')
    print('Bounded Value-entry execution only; no solver or production adequacy claim.')


if __name__ == '__main__':
    main()
