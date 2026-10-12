#!/usr/bin/env python3
"""Finite scalar reference trace; no compiler, source parser, or intrusion oracle.

Rules are independently transcribed from pinned Typer.scala:48-83,88-159,166-207.
Declared additions: Unit is a level-0 primitive; Group preserves its AST node
and returns its child's scalar type; an annotated local infers its RHS at
boundary+1, checks below its primitive annotation, and exposes that annotation.
This is a conditional native analogue of the exact Yulang source, not a Yulang
source theorem or a complete Call/effect checker. Run takes no arguments/files.
"""
from dataclasses import dataclass, field
import json


@dataclass(frozen=True)
class Prim:
    name: str
    level: int = 0


@dataclass(eq=False)
class Var:
    name: str
    level: int
    lower: list = field(default_factory=list)
    upper: list = field(default_factory=list)


@dataclass(frozen=True)
class Fn:
    arg: object
    result: object

    @property
    def level(self):
        return max(self.arg.level, self.result.level)


INT, UNIT = Prim('int'), Prim('unit')


def show(t):
    if isinstance(t, Var):
        return f'{t.name}@{t.level}'
    if isinstance(t, Fn):
        return f'({show(t.arg)} -> {show(t.result)})'
    return t.name


class Typer:
    def __init__(self):
        self.variables, self.pairs, self.uses, self.publications = [], [], [], []
        self.names, self.calls, self.groups, self.checks = {}, {}, [], []

    def fresh(self, level, label):
        v = Var(f'{label}#{len(self.variables)}', level)
        self.variables.append(v)
        return v

    def constrain(self, lhs, rhs, cache=None):
        if lhs is rhs:
            return
        cache = set() if cache is None else cache
        if isinstance(lhs, Var) or isinstance(rhs, Var):
            if (lhs, rhs) in cache:
                return
            cache.add((lhs, rhs))
        if isinstance(lhs, Fn) and isinstance(rhs, Fn):
            self.constrain(rhs.arg, lhs.arg, cache)
            self.constrain(lhs.result, rhs.result, cache)
        elif isinstance(lhs, Var) and rhs.level <= lhs.level:
            lhs.upper.insert(0, rhs)
            for b in list(lhs.lower):
                self.constrain(b, rhs, cache)
        elif isinstance(rhs, Var) and lhs.level <= rhs.level:
            rhs.lower.insert(0, lhs)
            for b in list(rhs.upper):
                self.constrain(lhs, b, cache)
        elif isinstance(lhs, Var):
            self.constrain(lhs, self.extrude(rhs, False, lhs.level, {}), cache)
        elif isinstance(rhs, Var):
            self.constrain(self.extrude(lhs, True, rhs.level, {}), rhs, cache)
        else:
            raise ValueError(f'cannot constrain {show(lhs)} <: {show(rhs)}')

    def extrude(self, t, positive, target, memo):
        if t.level <= target:
            return t
        if isinstance(t, Fn):
            return Fn(self.extrude(t.arg, not positive, target, memo),
                      self.extrude(t.result, positive, target, memo))
        if isinstance(t, Prim):
            return t
        key = (t, positive)
        if key in memo:
            return memo[key]
        v = self.fresh(target, 'copy+' if positive else 'copy-')
        memo[key] = v
        self.pairs.append((v, t, positive, target))
        if positive:
            t.upper.insert(0, v)
            v.lower = [self.extrude(b, positive, target, memo) for b in t.lower]
        else:
            t.lower.insert(0, v)
            v.upper = [self.extrude(b, positive, target, memo) for b in t.upper]
        return v

    def freshen(self, boundary, t, level, label):
        memo, retained = {}, set()

        def go(t):
            if t.level <= boundary:
                if isinstance(t, Var):
                    retained.add(t)
                return t
            if isinstance(t, Fn):
                return Fn(go(t.arg), go(t.result))
            if isinstance(t, Prim):
                return t
            if t in memo:
                return memo[t]
            v = self.fresh(level, label)
            memo[t] = v
            v.lower = list(reversed([go(b) for b in reversed(t.lower)]))
            v.upper = list(reversed([go(b) for b in reversed(t.upper)]))
            return v

        result = go(t)
        self.uses.append((label, boundary, level, memo, retained, result))
        return result

    def rhs(self, recursive, name, rhs, ctx, boundary, annotation=None):
        if recursive:
            root = self.fresh(boundary + 1, name)
            self.names[name] = root
            value = self.term(rhs, dict(ctx, **{name: root}), boundary + 1)
            self.constrain(value, root)
            value = root
        else:
            value = self.term(rhs, ctx, boundary + 1)
        if annotation is not None:
            self.checks.append((name, boundary + 1, value, annotation))
            self.constrain(value, annotation)
            value = annotation
        self.publications.append((name, boundary, value))
        return boundary, value

    def term(self, node, ctx, level):
        kind, *data = node
        if kind == 'name':
            binding = ctx[data[0]]
            if isinstance(binding, tuple):
                return self.freshen(*binding, level, data[1])
            return binding
        if kind == 'lam':
            name, body = data
            parameter = self.fresh(level, name)
            self.names[name] = parameter
            return Fn(parameter, self.term(body, dict(ctx, **{name: parameter}), level))
        if kind == 'app':
            tag, callee, argument = data
            f, a = self.term(callee, ctx, level), self.term(argument, ctx, level)
            r = self.fresh(level, tag)
            self.calls[tag] = f, a, r
            self.constrain(f, Fn(a, r))
            return r
        if kind == 'let':
            recursive, name, rhs, body, annotation = data
            scheme = self.rhs(recursive, name, rhs, ctx, level, annotation)
            return self.term(body, dict(ctx, **{name: scheme}), level)
        if kind == 'group':
            self.groups.append(level)
            return self.term(data[0], ctx, level)
        return {'int': INT, 'unit': UNIT}[kind]


def source(extra_local_roots=False):
    n = lambda spelling, use='mono': ('name', spelling, use)
    fy = ('app', 'f-y', n('f'), n('y'))
    drop_use = ('app', 'drop-call', n('drop', 'drop-use'), ('group', fy))
    g_body = ('let', extra_local_roots, 'drop', ('lam', 'z', n('y')), drop_use, None)
    first_rhs = ('app', 'g-int', n('g', 'g-use-0'), ('int',))
    second = ('app', 'g-unit', n('g', 'g-use-1'), ('unit',))
    suffix = ('let', False, 'first', first_rhs, second, INT)
    f_body = ('let', extra_local_roots, 'g', ('lam', 'y', g_body), suffix, None)
    return ('let', True, 'f', ('lam', 'x', f_body), n('f', 'f-final'), None)


def run():
    t = Typer()
    t.rhs(False, 'answer', source(), {}, 0)
    o, b, z = t.names['f'], t.names['y'], t.names['z']
    r = t.calls['f-y'][2]
    assert (o.level, b.level, z.level, r.level) == (2, 3, 4, 3)
    cp, dp = [p for p in t.pairs if p[1] is b or p[1] is r]
    c, d = cp[0], dp[0]
    assert cp[1:] == (b, True, 2) and dp[1:] == (r, False, 2)
    uses = {u[0]: u for u in t.uses}
    drop = uses['drop-use']
    assert drop[1:3] == (3, 3) and b in drop[4] and z in drop[3]
    for label, level in [('g-use-0', 3), ('g-use-1', 2)]:
        u = uses[label]
        assert u[1:3] == (2, level) and b in u[3] and c in u[4]
        assert r not in u[3] and d not in u[3]
    assert uses['g-use-0'][3][b] is not uses['g-use-1'][3][b]
    assert t.groups == [3]
    assert t.checks[0][0:2] == ('first', 3)
    assert o in uses['f-final'][3] and c in uses['f-final'][3]
    # A separate finite extension of the finished ordinary store. These are
    # supplied use-frame equality clauses, NOT an adopted intrusion schedule.
    extended = Typer()
    extended.rhs(False, 'answer', source(), {}, 0)
    eb, er = extended.names['y'], extended.calls['f-y'][2]
    ec, ed = [p[0] for p in extended.pairs if p[1] is eb or p[1] is er]
    extended.constrain(ed, er)
    extended.constrain(er, ed)
    argument_equalities = []
    euses = {u[0]: u for u in extended.uses}
    for label in ['g-use-0', 'g-use-1']:
        bi = euses[label][3][eb]
        argument_equalities.append([show(ec), show(bi)])
    try:
        for label in ['g-use-0', 'g-use-1']:
            bi = euses[label][3][eb]
            extended.constrain(bi, ec)
            extended.constrain(ec, bi)
    except ValueError as failure:
        assert str(failure) == 'cannot constrain unit <: int'
        equality_result = str(failure)
    else:
        raise AssertionError('shared-C argument equality extension should fail')
    # A second declared scalar analogue retains additional open q_g/q_drop
    # roots even without self occurrences, using Typer's existing recursive
    # let constructor. It checks that these roots cannot silently be treated
    # as the first analogue's direct Function roots. It is not the Rust facade
    # algorithm (Name/Group/Block and four effect ports are still absent).
    rooted = Typer()
    rooted.rhs(False, 'answer', source(extra_local_roots=True), {}, 0)
    rb, rz = rooted.names['y'], rooted.names['z']
    rr = rooted.calls['f-y'][2]
    ruses = {u[0]: u for u in rooted.uses}
    rcp, rdp = [p for p in rooted.pairs if p[1] is rb or p[1] is rr]
    assert rcp[1:] == (rb, True, 2) and rdp[1:] == (rr, False, 2)
    assert rooted.names['drop'] in ruses['drop-use'][3]
    assert rz in ruses['drop-use'][3] and rb in ruses['drop-use'][4]
    for label in ['g-use-0', 'g-use-1']:
        assert rooted.names['g'] in ruses[label][3]
        assert rb in ruses[label][3] and rcp[0] in ruses[label][4]
    print(json.dumps({
        'status': 'PASS: finite conditional native analogue; ordinary reference rules',
        'variables': len(t.variables), 'groups_at_levels': t.groups,
        'pairs': [[show(c), show(p), '+' if q else '-', l] for c, p, q, l in t.pairs],
        'publications': [[n, l, show(v)] for n, l, v in t.publications],
        'uses': [{'name': n, 'boundary': l, 'use_level': k,
                  'fresh': [[show(a), show(b)] for a, b in m.items()],
                  'retained': sorted(show(v) for v in keep)}
                 for n, l, k, m, keep, _ in t.uses],
        'annotation': [[n, l, show(v), show(a)] for n, l, v, a in t.checks],
        'conditional_finished_store_extension': {
            'result_equality_alone': 'consistent in this finite native relation',
            'argument_equalities': argument_equalities,
            'result': equality_result,
            'scope': 'supplied clauses on native use images; no source or schedule claim'},
        'additional_open_g_drop_roots_analogue': {
            'variables': len(rooted.variables),
            'publications': [[n, l, show(v)] for n, l, v in rooted.publications],
            'drop_fresh': [[show(a), show(b)] for a, b in ruses['drop-use'][3].items()],
            'g_fresh': {n: [[show(a), show(b)] for a, b in ruses[n][3].items()]
                        for n in ['g-use-0', 'g-use-1']},
            'scope': 'same formal copy parents; different extra root map; no Rust equivalence'},
        'ignored_f_result': {'row': show(r), 'lower': [show(v) for v in r.lower],
                             'upper': [show(v) for v in r.upper]},
        'shared_argument_copy': {'row': show(c), 'lower': [show(v) for v in c.lower]},
    }, indent=2))


if __name__ == '__main__':
    run()
