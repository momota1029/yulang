# Contextual explicit-effect attachment: finite model

Date: 2026-10-10
Status: unreviewed bounded research characterization; frozen on producer handoff
Baseline: `8a387485a7a19fed3890a47a0321707eac42497e`
Lease: this note only; the executable is embedded below and writes no files
Method: finite set saturation versus event-specific relational reachability,
with targeted shortcut mutations

## Objective, authority, and exact premises

Test the smallest contextual interpretation of the selected negative `[E]`
subtraction and positive concrete allowance while retaining ordinary flow,
future concrete checks, composed Function polarity, and atomic failure.
The governing source is
[annotation effect hygiene integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–5. The primary additionally supplied the already selected closed/open
positive-row contract, recorded in
[concrete covariant annotation implementation](../design/2026-10-10-concrete-effect-annotation-implementation.md):
a closed positive row permits its concrete members, while an unmatched concrete
atom in an open row reaches its symbolic tail and remains subject to tail checks.
The latter document's opening policy, annotation checking/publication owner,
and conflict/equality/rollback sections are direct dependencies.

The Oracle premises are only those source-inspection results recorded in the
governing policy §2: Function argument polarity reverses; results retain it;
annotation variables remain connected; filters check future lowers; annotation
scope/position owns authority. No additional Oracle code was read or executed.
The existing [attached-subtraction probe](2026-10-05-effect-attachment-subtraction-playground.md)
is retained as a limit: it supplied attachment/consumption flags and did not
construct annotation incidence. This experiment does not rerun its 256 histories.

This is a **candidate transition model**, followed by a **bounded executable
characterization** and a short **conditional invariant derivation**. It is not
an established source-to-solver theorem. In particular, the model assumes:

1. Two distinct nullary nominal atoms `E` and `F`, already resolved by the source
   owner. There are no parameterized effects or spelling comparisons.
2. Each concrete contribution has a stable event ID. Sharing row storage does
   not equate source contributions or annotation boundary IDs.
3. Source construction has already supplied the actual boundary, its owner,
   composed polarity, concrete permitted/subtracted atoms, symbolic-tail row,
   and directional flow edges. A gate on an edge means that traversal genuinely
   crosses the retained annotation occurrence.
4. The active-owner set is fixed for each evaluation. An inactive-owner run
   describes an unlicensed traversal; it does not prescribe a runtime operation
   that resurrects an already removed effect after scope exit.
5. Ordinary edges carry contributions without generating or deleting them.
   Row equality shares lower sets; it does not copy a boundary gate onto other
   traversals. An allowance is not an emitted contribution or subtraction grant.
6. A transaction publishes its entire updated state only on success. The
   executable uses a full snapshot to test that requirement; it does not prove
   production journal completeness.

Premise 3 is the unproved source-construction obligation. Nothing in this checker
derives it from an annotation syntax node, pending Call metadata, row equality,
or an observed successful solver query. The model deliberately makes it visible
as the gate-bearing directional edge, rather than guessing incidence from rows.

## Algebra and conditional derivation

An event is `q = (event_id, nominal_atom)`. A gate is
`g = (boundary_id, owner, kind, members, optional_tail)`, where `kind` is
negative or positive. At a genuine traversal through `g`, with active owners `A`:

```text
negative transfer_g(q, A) = empty     if owner(g) in A and atom(q) in members(g)
                            {q}       otherwise
positive transfer_g(q, A) = {q}       if atom(q) in members(g)
                            {q}       if tail(g) exists; also insert q into tail(g)
                            conflict  otherwise
ordinary transfer(q)     = {q}
support(L)              = {atom(q) | q in L}
```

The positive tail insertion records the unmatched concrete lower and keeps it
reachable by a separately supplied tail consumer. A variable is not itself a
concrete event. An empty symbolic tail therefore passes a concrete check; later
`F` at a tail constrained to `{E}` conflicts. That tail constraint is a test
input, not a claimed universal restriction on every annotation variable.

Each canonical row's lower set is the least solution of its supplied seeds and
incoming transfers. Canonical equality unions row sets and preserves all gates
at their original edges. Function polarity at a path is the root sign multiplied
by `-1` for each argument/value or argument/effect step, and by `+1` for each
result/value or result/effect step.

Conditional on premises 1–6, finite saturation terminates: there are six named
rows and at most two seeded events in the enumerated envelope, so a successful
run can add at most twelve row/event pairs. Each sweep either adds a pair or
terminates; closed-row conflicts terminate immediately. Ordinary transfer has
the identity frame condition. Negative transfer removes only the event's
traversal through that gate, and positive transfer never removes it. If another
ordinary or allowed path for the same atom reaches the complete output, the
output support retains that atom. Canonical equality changes available paths,
not which edge has a subtraction license. These are consequences of the supplied
algebra; they do not prove the source supplies that algebra.

## Smallest discriminating witnesses

| Obligation or shortcut | Witness and expected observation |
| --- | --- |
| Two attachments at distinct positions, same `E` | `q0:E` crosses negative `b0`; `q1:E` crosses positive `b1`; only `q1` reaches output. Both seeds have equal singleton support `{E}`. Family-only or structural-row-equality cancellation incorrectly removes `q1`. |
| One row shared by both positions | One seed `q0:E`, one row aliased as both sources: negative traversal removes it, positive traversal retains it, output remains `{E}`. Copying the gate onto every edge of the canonical row incorrectly produces empty output. |
| Nested Function argument polarity | Root-positive path `(argument, argument_effect)` is positive after two reversals, and therefore allows `E`; treating the nearest argument label as negative would authorize removal. Length two is minimal for this shortcut. |
| Future lower insertion | Form an empty positive closed `{E}` view: initial state succeeds; later `q0:F` at its source conflicts. Formation-only checks accept a forbidden future lower. One event is sufficient. |
| Open symbolic tail and retained later check | Empty open `{E} + tail` succeeds; later `q0:F` reaches both the positive output and tail. Adding tail upper `{E}` makes the same lower conflict. Erasing the tail connection bypasses this conflict. |
| Copied parent equality | Begin with one `E` seed at the negative source: output is empty. Add parent/copy equality with the positive source: that source now observes the event and output becomes `{E}`, while the original negative edge still removes it. No grant transfers through equality. |
| Failure rollback | In one transaction append an ordinary edge, add source equality, and insert `F` into a closed `{E}` boundary. Reject and restore the complete pre-state, including edges, aliases, seeds, derived rows, and revision. A failed transaction must publish none of its attempted additions. |

The distinct-position witness requires two events to expose the survival of an
independent contribution. The shared-row witness needs only one event and two
outgoing paths; with one outgoing path there is no competing surviving traversal
to distinguish attachment-local authority from a global row filter. Event IDs
remain evidence coordinates; public support is still a set without multiplicity.

## Executable experiment

The finite graph is `r0 --negative b0--> n --> out` and
`r1 --positive b1--> p --> out`, plus optional equality `r0 = r1` and optional
positive symbolic tail `tail`. Owner `function0` is active or inactive.
Enumeration covers both independent event choices `absent/E/F`, both owner
states, distinct/shared source rows, and closed/open positive rows:
`3^2 * 2^3 = 72` complete input valuations. Polarity covers all 85 paths of
length zero through three over the four Function-port roles. No randomness or
PRNG seeds, search truncation, compiler invocation, filesystem outputs, or child
processes occur inside the checker.

The candidate computes an increasing fixed point. The reference builds an
event-specific adjacency matrix and computes reflexive transitive closure;
closed allowance and tail conflicts are checked against the resulting reachable
sources. The two algorithms share the supplied gate-transfer algebra, row
equality interpretation, contribution identities, and finite graph. Algorithmic
agreement is independent of sweep order and detects propagation omissions; it
is **not** independent Oracle validation of those shared source premises. Named
mutation assertions below discriminate concrete shortcuts, not alternative
language meanings.

Run this exact command from the repository root:

```sh
python3 - <<'PY'
from pathlib import Path
import resource
resource.setrlimit(resource.RLIMIT_CPU, (5, 5))
resource.setrlimit(resource.RLIMIT_AS, (64 * 1024 * 1024, 64 * 1024 * 1024))
p = Path('notes/progress/2026-10-10-explicit-effect-attachment-finite-model.md')
code = p.read_text().split('```python\n', 1)[1].split('\n```', 1)[0]
exec(compile(code, str(p), 'exec'))
PY
```

```python
from copy import deepcopy
from dataclasses import dataclass, field
from itertools import product
from time import monotonic

ROWS = ('r0', 'r1', 'n', 'p', 'out', 'tail')
ACTIVE = frozenset({'function0'})

@dataclass(frozen=True)
class Gate:
    boundary: str
    owner: str
    kind: str
    members: frozenset
    tail: str | None = None

@dataclass
class World:
    edges: list
    aliases: list = field(default_factory=list)
    seeds: dict = field(default_factory=lambda: {r: set() for r in ROWS})
    tail_checks: dict = field(default_factory=dict)
    derived: dict = field(default_factory=dict)
    revision: int = 0

def make_world(shared=False, open_tail=False):
    neg = Gate('b0', 'function0', 'negative', frozenset({'E'}))
    pos = Gate('b1', 'function0', 'positive', frozenset({'E'}),
               'tail' if open_tail else None)
    return World([('r0', 'n', neg), ('r1', 'p', pos),
                  ('n', 'out', None), ('p', 'out', None)],
                 [('r0', 'r1')] if shared else [])

def solve(w, active):
    lower = deepcopy(w.seeds)
    while True:
        before = deepcopy(lower)
        for x, y in w.aliases:
            both = lower[x] | lower[y]
            lower[x] = set(both)
            lower[y] = set(both)
        for src, dst, gate in w.edges:
            for q in tuple(lower[src]):
                atom = q[1]
                if gate and gate.kind == 'negative':
                    if gate.owner in active and atom in gate.members:
                        continue
                if gate and gate.kind == 'positive' and atom not in gate.members:
                    if gate.tail is None:
                        return None
                    lower[gate.tail].add(q)
                lower[dst].add(q)
        for row, permitted in w.tail_checks.items():
            if any(q[1] not in permitted for q in lower[row]):
                return None
        if lower == before:
            return lower

def reference(w, active):
    result = {r: set() for r in ROWS}
    events = set().union(*w.seeds.values())
    for q in sorted(events):
        reach = {(r, r) for r in ROWS}
        reach |= {(a, b) for x, y in w.aliases for a, b in ((x, y), (y, x))}
        for src, dst, gate in w.edges:
            if gate and gate.kind == 'negative':
                if gate.owner in active and q[1] in gate.members:
                    continue
            reach.add((src, dst))
            if gate and gate.kind == 'positive' and q[1] not in gate.members:
                if gate.tail is not None:
                    reach.add((src, gate.tail))
        # Warshall closure is independent of solver sweep order.
        for pivot in ROWS:
            reach |= {(a, b) for a in ROWS for b in ROWS
                      if (a, pivot) in reach and (pivot, b) in reach}
        reached = {dst for src in ROWS if q in w.seeds[src]
                   for dst in ROWS if (src, dst) in reach}
        for src, _, gate in w.edges:
            if (src in reached and gate and gate.kind == 'positive'
                and gate.tail is None and q[1] not in gate.members):
                return None
        if any(row in reached and q[1] not in permitted
               for row, permitted in w.tail_checks.items()):
            return None
        for row in reached:
            result[row].add(q)
    return result

def publish(w, active):
    result = solve(w, active)
    if result is None:
        return False
    w.derived = result
    return True

def transact(w, active, mutation):
    old = deepcopy(w.__dict__)
    mutation(w)
    w.revision += 1
    if publish(w, active):
        return True
    w.__dict__.clear()
    w.__dict__.update(old)
    return False

started = monotonic()
envelope = 0
for first, second, shared, open_tail, live in product(
        (None, 'E', 'F'), (None, 'E', 'F'), (False, True),
        (False, True), (False, True)):
    w = make_world(shared, open_tail)
    for row, event, atom in (('r0', 'q0', first), ('r1', 'q1', second)):
        if atom is not None:
            w.seeds[row].add((event, atom))
    active = ACTIVE if live else frozenset()
    assert solve(w, active) == reference(w, active)
    envelope += 1

roles = ('argument', 'argument_effect', 'result', 'result_effect')
def polarity(path):
    sign = 1
    for role in path:
        sign *= -1 if role in roles[:2] else 1
    return sign

polarity_cases = 0
for depth in range(4):
    for path in product(roles, repeat=depth):
        parity = sum(role in roles[:2] for role in path) % 2
        assert polarity(path) == (1 if parity == 0 else -1)
        polarity_cases += 1
assert polarity(('argument', 'argument_effect')) == 1
assert (-1 if 'argument_effect' in roles[:2] else 1) == -1

q0, q1 = ('q0', 'E'), ('q1', 'E')
distinct = make_world()
distinct.seeds['r0'].add(q0)
distinct.seeds['r1'].add(q1)
res = solve(distinct, ACTIVE)
assert res['n'] == set() and res['p'] == {q1} and res['out'] == {q1}
assert distinct.seeds['r0'] == {q0} and distinct.seeds['r1'] == {q1}
assert {q[1] for q in distinct.seeds['r0']} == {q[1] for q in distinct.seeds['r1']}
# Family-global and structurally-equal-support mutations delete every E.
assert {q for q in res['out'] if q[1] != 'E'} != res['out']

shared = make_world(shared=True)
shared.seeds['r0'].add(q0)
res = solve(shared, ACTIVE)
assert res['n'] == set() and res['p'] == {q0} and res['out'] == {q0}
# A canonical-row-wide subtraction mutation also deletes this surviving E.
assert {q for q in res['out'] if q[1] != 'E'} != res['out']

parent = make_world()
parent.seeds['r0'].add(q0)
assert solve(parent, ACTIVE)['out'] == set()
parent.aliases.append(('r0', 'r1'))
assert solve(parent, ACTIVE)['out'] == {q0}
assert solve(parent, ACTIVE)['n'] == set()

closed = make_world()
assert publish(closed, ACTIVE)
closed.seeds['r1'].add(('q0', 'F'))
assert solve(closed, ACTIVE) is None and reference(closed, ACTIVE) is None
# Formation-only mutation: replace the retained future consumer by plain flow.
formation_only = deepcopy(closed)
formation_only.edges[1] = ('r1', 'p', None)
assert solve(formation_only, ACTIVE)['out'] == {('q0', 'F')}

symbolic = make_world(open_tail=True)
assert solve(symbolic, ACTIVE)['tail'] == set()
symbolic.seeds['r1'].add(('q0', 'F'))
assert solve(symbolic, ACTIVE)['tail'] == {('q0', 'F')}
symbolic.tail_checks['tail'] = frozenset({'E'})
assert solve(symbolic, ACTIVE) is None and reference(symbolic, ACTIVE) is None
# Disconnected-symbolic-tail mutation forgets the route to its retained check.
erased_tail = deepcopy(symbolic)
erased_tail.edges[1] = ('r1', 'p', None)
assert solve(erased_tail, ACTIVE) is not None

rollback = make_world()
assert publish(rollback, ACTIVE)
before = deepcopy(rollback.__dict__)
def failing_mutation(w):
    w.edges.append(('out', 'n', None))
    w.aliases.append(('r0', 'r1'))
    w.seeds['r0'].add(('q0', 'F'))
assert not transact(rollback, ACTIVE, failing_mutation)
assert rollback.__dict__ == before
dirty = deepcopy(rollback)
failing_mutation(dirty)
dirty.revision += 1
assert not publish(dirty, ACTIVE) and dirty.__dict__ != before

# Neither empty allowance support nor ordinary propagation manufactures E.
assert all(not values for values in solve(make_world(), ACTIVE).values())
ordinary = World([('r0', 'out', None)])
ordinary.seeds['r0'].add(('q0', 'F'))
assert solve(ordinary, ACTIVE)['out'] == {('q0', 'F')}
assert solve(distinct, frozenset())['n'] == {q0}
print(f'PASS {envelope} complete valuations; {polarity_cases} polarity paths; '
      '7 focused vectors; 7 named shortcut witnesses')
assert monotonic() - started < 5, 'wall-time envelope exceeded'
```

## Results, budgets, omissions, and handoff

The exact embedded command passed with:

```text
PASS 72 complete valuations; 85 polarity paths; 7 focused vectors; 7 named shortcut witnesses
```

One measured invocation, wrapped with `/usr/bin/time`, used 0.04 seconds elapsed,
0.03 seconds user CPU, 0.00 seconds system CPU, and 13,920 KiB peak resident
memory. This is a resource observation of the checker, not a performance claim.
The run is limited to one Python process, five CPU seconds, 64 MiB address space,
and five seconds of checker wall time. These are experiment caps, not proposed
compiler work limits. No Cargo/build/test/format process or benchmark sample is
authorized or needed for this note.

Seven named shortcuts are discriminated: family-global removal, cancellation
based on equal structural support, canonical-row-wide gate copying, nearest-label
polarity, formation-only allowance checks, symbolic-tail disconnection, and failed
state publication. The two global-removal assertions test intentionally erroneous
output projections; they are not complete implementations of alternative solvers.
Likewise the polarity mutation isolates composition, not Function construction.

Unverified: actual source formation of gate incidence and local ownership,
transport/freshening/extrusion of those witnesses, declaration identity creation,
provider no-backflow in the compiler, handler selection/resumption and complete
handler output, dynamic owner-lifetime updates, recursive Function construction,
parameterized effects, cycles beyond the rollback failure witness, production
journal/resource correctness, source soundness, principality, and public cutover.
No broader exhaustive search or Oracle execution is claimed. In particular,
the reference shares the most important transition premise; agreement cannot
discharge that premise.

Recommended next action: test the real source constructor/transport cut against
the one-event shared-row witness, retaining the two original boundary traversals
through parent equality. This attacks the missing incidence premise instead of
running another equivalent supplied-flag model.

Frozen dependency SHA-256 values at baseline and at producer start:

```text
annotation-effect-hygiene-integration.md
4071679ebd184560fc6fe30a68618f18cd2e669324ce70aa0751dbb55b595a37
concrete-effect-annotation-implementation.md
592dc8d6ea54aefd0cbc76244966874ac2d61b66cd249795c2ea3ce1de337765
effect-attachment-subtraction-playground.md
7a831a5068d1fcc61a5ed350acce7b32822757c99e1ae778775ef80f0c52e0b6
```

Commit packet: exact lease is
`notes/progress/2026-10-10-explicit-effect-attachment-finite-model.md`;
baseline `8a387485a7a19fed3890a47a0321707eac42497e`; direct dependency changes
were rechecked at handoff and none changed; HEAD remained the pinned baseline.
Checks already run are the embedded bounded Python
experiment, note whitespace/reference inspection, and direct dependency hashes;
status is unreviewed research characterization, with
no source theorem or production authority. Proposed message:
`research: characterize contextual explicit effect attachment in a finite model`.
Shared-record deltas left for the primary/curator: link this bounded result and
its remaining gate-incidence premise in `tasks/current.md` / `tasks/research-lab.md`
if useful; no theory node should be closed by algorithm agreement. No shared
records, question bundle, compiler, manifest, lockfile, or Git state were changed.
