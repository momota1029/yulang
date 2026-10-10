# Nonterminal acknowledgement prefix: bounded transition falsification

Date: 2026-10-11
Status: producer-only, unreviewed bounded characterization; no Rust-source theorem.
Baseline: `6a962826ab46d7f58529f7162aa016997ed5418d`.
Exclusive lease: this note only. Producer: `/root/ack_prefix_repair_falsifier`.

## Objective and fixed premises

Test the proposed nonterminal resume rule under suspension contract §§3 and 6:
prepare current-route undo for every pending acknowledgement before any further
dispatch effect, pop or append; prepare each new acknowledgement before appending
it. The approved contract retains exact child ownership and restores exact
pre-route state on failure. This does not change its language meaning.

The prior distinct-handle counterexample is recorded in
`2026-10-11-local-use-restoration-continuation-falsifiers.md`. The present lane
tests its proposed repair with repeated handles and repeated commits; it does
not repeat the prior source-reachability or live-vector mutation attacks.

Candidate assumptions are explicit: acknowledgements name ordered children;
all modeled children are already queued; preparation journals the current
handle's queued/consumed/retired state; reverse journal order restores handles;
commit clears undo and resets prepared to completed; existing transactional
owners restore the frame, worklist and dispatch effects. A newly popped child's
undo reservation, pop and append form one atomic transition. Commits may occur
after any successful model step, including each prefix reservation and each
terminal consumption, but not inside that atomic transition. Terminal resume
prepares one next acknowledgement when completed equals prepared. Retired replay
handles remain retained throughout the model; reclamation is omitted.

## Frozen executable model

The following block is the complete executable. The oracle stores the entire
logical model state at the latest commit; it does not consult the prepared
cursor or infer coverage from journal entries. Candidate rollback uses separate
frame/worklist/effect snapshots and per-handle undo. Both share the above
transition rules and acknowledgement identities. Thus this is independent of
the candidate's cursor-based journal decisions, but not independent validation
of the supplied transitions or of Rust/source reachability.

```python
from copy import deepcopy
from itertools import product
from collections import Counter

stats = Counter()

def canonical_words(n):
    for word in product(range(3), repeat=n):
        seen = []
        for h in word:
            if h not in seen:
                seen.append(h)
        if seen == list(range(len(seen))):
            yield word

def initial(word, n, c):
    count = Counter()
    acks = []
    for h in word:
        acks.append((h, count[h]))
        count[h] += 1
    consumed = Counter(h for h, _ in acks[:c])
    ops = {h: (count[h], consumed[h], consumed[h] == count[h], count[h])
           for h in count}  # queued, consumed, retired, total
    return dict(ops=ops, acks=acks[:n], c=c, p=c, queue=acks[n:],
                phase='dispatch', event=0, effects=[], frame=True)

class Machine:
    def __init__(self, state, mutation=None):
        self.s = state
        self.base = deepcopy(state)
        self.frame_undo = None
        self.queue_undo = None
        self.effect_undo = None
        self.undo = []
        self.mutation = mutation

    def checkpoint(self):
        self.s['p'] = self.s['c']
        self.base = deepcopy(self.s)
        self.frame_undo = self.queue_undo = self.effect_undo = None
        self.undo = []

    def rollback(self):
        restored = deepcopy(self.s)
        entries = self.undo if self.mutation == 'forward_undo' else reversed(self.undo)
        for h, old in entries:
            restored['ops'][h] = old
        if self.frame_undo is not None:
            restored.update(deepcopy(self.frame_undo))
        if self.queue_undo is not None:
            restored['queue'] = self.queue_undo[:]
        if self.effect_undo is not None:
            restored['effects'] = self.effect_undo[:]
        assert restored == self.base, ('rollback', self.mutation, self.base, restored)
        stats['rollback_checks'] += 1

    def reserve(self, label, fail):
        # Failure before this reservation mutates anything.
        if label == fail:
            raise MemoryError(label)

    def journal_frame(self, fail):
        if self.frame_undo is None:
            self.reserve('frame', fail)
            self.frame_undo = deepcopy({k: v for k, v in self.s.items()
                                      if k not in ('ops', 'queue', 'effects')})

    def prepare(self, ack, fail, label):
        h, i = ack
        q, consumed, retired, total = self.s['ops'][h]
        if i >= q or i < consumed:
            raise ValueError('invalid preparation')
        self.reserve(label, fail)
        self.undo.append((h, self.s['ops'][h]))

    def invariant(self):
        s = self.s
        assert s['c'] <= s['p'] <= len(s['acks'])
        journaled = {h for h, _ in self.undo}
        assert all(h in journaled for h, _ in s['acks'][s['c']:s['p']]), (
            'prepared prefix lacks current-route undo', s, self.undo)

    def step(self, fail=None):
        s = self.s
        if not s['frame']:
            return False
        self.journal_frame(fail)
        if s['phase'] == 'dispatch':
            if s['p'] < len(s['acks']) and self.mutation != 'skip_prefix':
                self.prepare(s['acks'][s['p']], fail, 'prefix')
                s['p'] += 1
            elif s['event'] == 0:
                # Includes the retained initial dispatch, with zero new pops.
                assert self.mutation == 'skip_prefix' or s['p'] == len(s['acks'])
                self.reserve('effect', fail)
                if self.effect_undo is None:
                    self.effect_undo = s['effects'][:]
                s['effects'].append(len(s['acks']))
                s['event'] = 1
            elif s['queue']:
                assert self.mutation == 'skip_prefix' or s['p'] == len(s['acks'])
                self.reserve('new_buffer', fail)
                self.prepare(s['queue'][0], fail, 'new_ack')
                if self.queue_undo is None:
                    self.queue_undo = s['queue'][:]
                s['acks'].append(s['queue'].pop(0))
                s['p'] += 1
                s['event'] = 0
            else:
                s['phase'] = 'terminal'
        elif s['c'] < len(s['acks']):
            if s['c'] == s['p']:
                self.prepare(s['acks'][s['c']], fail, 'terminal')
                s['p'] += 1
            h, i = s['acks'][s['c']]
            q, consumed, retired, total = s['ops'][h]
            if consumed != i:
                raise ValueError('invalid completion')
            s['ops'][h] = (q, consumed + 1, consumed + 1 == total, total)
            s['c'] += 1
        else:
            s['frame'] = False
        if self.mutation != 'skip_prefix':
            self.invariant()
        return True

def explore(m, commits_left):
    stats['nodes'] += 1
    m.rollback()  # Failure after every completed primitive.
    if not m.s['frame']:
        stats['completed_schedules'] += 1
        assert all(v[1] == v[3] and v[2] for v in m.s['ops'].values())
        return
    for fail in ('frame', 'prefix', 'new_buffer', 'new_ack', 'effect', 'terminal'):
        probe = deepcopy(m)
        try:
            probe.step(fail)
        except MemoryError:
            probe.rollback()
            stats['reservation_failures_' + fail] += 1
    stepped = deepcopy(m)
    assert stepped.step()
    explore(stepped, commits_left)
    if commits_left and stepped.s['frame']:
        committed = deepcopy(stepped)
        committed.checkpoint()
        stats['commits'] += 1
        explore(committed, commits_left - 1)

for total in range(5):
    for word in canonical_words(total):
        for n in range(total + 1):
            for c in range(n + 1):
                stats['initial_states'] += 1
                explore(Machine(initial(word, n, c)), 2)
print('REPAIR', dict(sorted(stats.items())))

# Exact repeated acknowledgement identity is corrupt input, not a second child.
bad = initial((0, 0), 2, 0)
bad['acks'] = [(0, 0), (0, 0)]
bad_machine = Machine(bad)
try:
    while bad_machine.step():
        pass
except ValueError as e:
    bad_machine.rollback()
    print('EXACT_DUPLICATE_REJECTED', str(e))
else:
    raise AssertionError('exact duplicate accepted')

# Prior shortcut: append undo for a new distinct handle without prefix repair.
m = Machine(initial((0, 1), 1, 0), 'skip_prefix')
try:
    while m.step():
        m.rollback()
except AssertionError:
    print('MUTATION_SKIP_PREFIX_DETECTED', 'one old ack, one new ack, two handles')
else:
    raise AssertionError('mutation escaped')

# Reverse order matters once terminal commits reset preparation to completed.
m = Machine(initial((0, 0, 0), 3, 0), 'forward_undo')
while m.s['phase'] != 'terminal':
    m.step()
m.step()  # consume first child, then commit.
m.checkpoint()
m.step()
m.step()
try:
    m.rollback()
except AssertionError:
    print('MUTATION_FORWARD_UNDO_DETECTED', 'one handle, two post-commit completions')
else:
    raise AssertionError('forward mutation escaped')

# Deliberately expose a commit inside the atomic new-child transition.
m = Machine(initial((0,), 0, 0))
m.journal_frame(None)
m.prepare(m.s['queue'][0], None, 'new_ack')
m.checkpoint()  # Reservation no longer belongs to the current route.
m.journal_frame(None)
m.queue_undo = m.s['queue'][:]
m.s['acks'].append(m.s['queue'].pop(0))
m.s['p'] += 1
try:
    m.invariant()
except AssertionError:
    print('SPLIT_POP_APPEND_BOUNDARY_DETECTED', 'zero old acks, one child')
else:
    raise AssertionError('split seam escaped')
```

## Results, coverage and limits

**No counterexample in the completed named finite envelope.** The main run
visited 276 initial states, 100,748 nodes, 14,589 complete schedules and 14,313
commit branches. It performed 161,269 full logical-state rollback comparisons:
100,748 after successful prefixes and 60,521 at reached reservation failures.
The reservation-failure counts were frame=14,589, prefix=18,513,
new-buffer=4,353, new-ack=4,353, effect=7,983 and terminal=10,730.
All successful schedules consumed every child exactly once and retired each
operation. This is bounded characterization under the fixed premises, not an
unconditional theorem or source proof.

No seeds: the main envelope enumerates every
canonical handle word of total length 0–4 over at most three handles, every split
between old and new acknowledgements, every completed old prefix, and all
commit/no-commit branches with at most two successful commits after model steps.
Canonical renaming removes symmetric identities only. Repeated handles use
distinct consecutive child indices. Exact duplicate identities are separately
tested as invalid input. Failure is injected at every reached reservation
position and rollback is checked after every successful primitive. Immediate
entry commits and consecutive commits without intervening steps are idempotent
under these transitions and are represented by the same initial/checkpoint state.

The repaired smallest prior witness has `acks=[(Q0,0)]`, queue `[(Q1,0)]`,
completed=prepared=0 after commit. The model first journals Q0 and advances
prepared to one. It later journals Q1 before pop/append, giving prepared=2.
After Q0 completes, rollback has current-route undo for both distinct handles;
Q0's consumed/retired state returns to its full pre-route value. The old
skip-prefix mutation loses this restoration and is detected.

Repeated handles are materially covered: separate child indices on one handle
produce multiple undo records. The forward-undo mutation is detected after one
terminal commit and two later completions on that same handle; restoring the
newer snapshot last leaves consumed=2 instead of the route baseline consumed=1.
The reverse ordering passes every main comparison. An exact duplicated
`(handle,index)` is rejected at its second completion and rollback succeeds;
this is an invalid-input control, not an admitted successful duplicate child.

The deliberately split reservation/pop/append control detects a separate
atomicity condition with **zero old acknowledgements and one child**: reserve
that child's undo, commit, then pop/append without reserving again. Prepared=1
claims coverage although the current-route journal is empty. Re-preparing the
old pending prefix cannot protect an acknowledgement which was not appended at
commit. The test reports the prefix invariant failure; it does not establish
source reachability of this cut. Any implementation exposing this extra pause
must reserve the current item's completion again on resume or keep the seam
atomic. Failure inside reservation before pop is covered by the main envelope.

The envelope omits four distinct handles, more than four total acknowledgements,
more than two commits, nested frames, new replay allocation or transfer,
unacknowledged queued work, diagnostic graph construction, capacity/accounting,
handle reclamation, representative changes, lifecycle invalidation and authentic
source suspension. The model's full-state oracle covers its complete logical
state, not the full Rust/compiler state. No compiler behavior or production gate
closure follows from green enumeration.

## Source snapshot and process boundary

Narrow owning reads: `candidate_context.rs:1560–1700,1810–1895` and
`lib.rs:11878–11970,12275–12350`. They ground reverse replay undo, commit frontier
reset, preparation validation, pre-pop completion reservation/tail append and
terminal consumption. These are locators, not a source-rule proof. Working
inputs were hashed before implementation movement:

```text
24909fb9a09e6f9d383e5b1f8f4f8db9d5f7e587a1ed5bbb6a47ead77e140831  crates/yu-solver/src/candidate_context.rs
77a3c4bdb48d438f7e5678c35302ad2aa1f6665ca9cbb8f3fdc0a48e730a30f4  crates/yu-solver/src/lib.rs
734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d  notes/design/2026-10-11-private-candidate-suspension-contract.md
8f7e99ae225e312384bc2ec101a13392d8e935eb349edd5483316d16eb4c32f7  notes/progress/2026-10-11-local-use-restoration-continuation-falsifiers.md
```

One read-only `git rev-parse HEAD` was inadvertently issued despite the packet's
no-Git wording; it returned the baseline above. This is disclosed as a process
violation, not counted as compliant verification. No Git mutation occurred;
no further Git command, delegation, Cargo, compiler edit or formatter ran.

The four working input hashes were unchanged when rechecked after execution.
They were not independently compared with committed baseline blobs by this
lane; the primary must perform that Git-owned revalidation. No dependency hash
change was observed in the inspected working inputs.

The exact command extracts the executable from this sole leased artifact;
there is no scratch file, generated report or additional output lease:

```text
/usr/bin/time -f 'elapsed=%e maxrss_kib=%M' timeout 30s bash -c 'ulimit -v 131072; exec python3 -c '\''from pathlib import Path; p=Path("notes/progress/2026-10-11-nonterminal-ack-prefix-falsifiers.md"); s=p.read_text().split("```python\n",1)[1].split("\n```",1)[0]; exec(compile(s,str(p),"exec"))'\'''
```

One bounded, sequential Python run exited 0: elapsed 25.54 seconds, maximum
RSS 12,800 KiB. Caps were 30 seconds/run, 128 MiB virtual memory and 90 seconds
aggregate; measured probe wall usage was 25.54/90 seconds. No CPU parallelism,
random seeds, timeouts, incomplete shards or hidden retries occurred. CPU time,
read-command resource usage and reasoning resource usage were not measured.
The run printed the main counts and four controls: exact duplicate rejected,
skip-prefix detected, forward-undo detected and split pop/append detected.
The frozen note also receives a narrow whitespace/executable-block extraction
check; no further search or model run is required.

## What an adapter can establish

A separately authorized test adapter can genuinely discriminate this rule
without relying on prepared as its oracle: retain real replay operations and
pending acknowledgements, save each operation's queued/consumed/retired state,
commit, invoke the actual prefix-preparation helper, inject failure at every
pending position, and compare real rollback with the saved operation states.
Use distinct handles plus consecutive children on one handle; compare frame
cursor state separately. The oracle must read complete retained operation
state directly rather than call the same preparation helper or infer protection
solely from `prepared_acks`. Testing only that the cursor reaches the list's
length cannot expose missing undo or wrong reverse ordering.

The primary's source audit reports no production retained nonterminal resume
owner and `begin_route_transaction` requiring an empty typed worklist. Such an
adapter therefore establishes direct helper/journal behavior in constructed
states. It cannot establish authentic entry into resumed dispatch, restoration
of a retained worklist/current item, full continuation rollback, or full §7
source/lifecycle conformance. This model similarly assumes transactional owners
for its frame, queue and effects rather than proving those owners from Rust.

## Handoff and commit packet

Recommended next action: under the primary's implementation/test authority,
exercise the actual prefix helper against independent replay-state snapshots,
while preserving reservation/pop/append atomicity and recording the missing
retained nonterminal resume owner as a separate source obligation.

This artifact is frozen for primary adjudication. It claims no independent
review, theorem closure or production authorization; no other leased artifact
was edited. Full lifecycle withdrawal, readiness/filter recognition, source
reachability, retained-worklist rollback, accounting and §7 remain unverified.

Commit packet: exact leased path
`notes/progress/2026-10-11-nonterminal-ack-prefix-falsifiers.md`; baseline
`6a962826ab46d7f58529f7162aa016997ed5418d`; dependency hashes changed: none observed
in the four rechecked working inputs, committed-blob equality deferred to the
primary. Review status: producer-only unreviewed bounded characterization.
Checks already run: narrow source reads, two working-input SHA256 captures,
one capped exhaustive model/control run, leased-note whitespace and extraction
check. Proposed one-line research-checkpoint message:
`Record bounded nonterminal acknowledgement prefix falsification`.
Shared-record deltas intentionally left for primary/curator: record the finite
transition result and its atomicity/shared-owner premises; retain source resume,
worklist ownership and full suspension gates as open; do not promote the model
to a source theorem or reopen the selected language meaning.
