# Replay input projections: bounded executable falsification

Status: unreviewed research characterization; frozen after the recorded run.
Producer: independent executable-model research lane, not a proof reviewer.
Baseline: `9d4392ef4a4ef309c6c9c9194840deca3cbf6de6`.
Authority: `notes/design/2026-10-10-contextual-attachment-admission-design.md`
§§4–5; §3 supplies the already selected ordered/shared construction boundary.
Lease: this note only. No compiler, tests, shared records, or Git mutations.

## Objective, dependencies, and premises

Test two tempting recognizer projections in a tiny supplied finite model:
forgetting lower/upper Replay order, and unfolding a shared child into two
independent copies with identical payload and attachment identities. This is
distinct from auditing Function-port source generation. The moving Packet 1
diff was not inspected.

Pinned Git blobs:

| Input | Blob |
| --- | --- |
| `crates/yu-solver/src/candidate_context.rs` | `ac646a46dd687e4d56bcd09887545f91de32391d` |
| governing attachment/admission design | `c99873544ca90aa817c77941514f7868a8023d65` |

At this baseline, `ContextExpr::Replay { lower, upper }` retains ordered
`ContextId` children. `State::context` interns exact expressions, including
payload/certificate handles and child identities, rather than numeric results.
`RelationKey` contains the typed endpoint pair and exact context handle.
`Dependency::Replay` additionally retains child/lower/upper relations and both
`BoundKey` inputs. The replay owner constructs its lower/upper context in that
order irrespective of insertion direction. These construction and dependency
identities are **not** inferred from the scalar model below.

`fold_context`/`evaluate_context` provide the exact detached algebra seam:
each reachable child is evaluated once and Replay reads its two child values
in lower/upper order. Replay concatenates left words, intersects filters,
combines right POP words, and applies directed mix at that node. The detached
evaluator retains construction records separately from numeric values. Its
single-valued numeric operations neither mutate children nor select independent
valuations for separate copies. It has no live general attachment consumer;
this experiment does not establish source reachability or a production defect.

The supplied model assumes fixed finite family per attachment ID, cancellation
`PUSH_i POP_i -> empty`, independence of different IDs, leading unmatched POPs,
and the pinned directed-mix operation. A normalized per-ID word is `(p,n)`.
Appending `(q,m)` gives `(p+max(q-n,0), m+max(n-q,0))`. Mixing right debt `r>0`
leaves `(p,n-r)` if `n>r`; otherwise it moves `p+r-n` to the right. No new
annotation meaning or semantic restriction is proposed.

## Finite envelope and independence

For each ID universe `{0}` and `{0,1}`, enumerate:

- every left word of length 0–2 over that universe's PUSH/POP alphabet;
- a right word that is empty or one POP of any ID;
- every fixed family assignment from subsets of `{A,B}` to IDs;
- filters `All`, empty, `{A}`, `{B}`, and `{A,B}`;
- every ordered pair of these child contexts under one Replay;
- shared `Replay(X,X)` versus two identical independent copies, followed by
  every one-step Replay continuation with left word length 0–1 and the same
  right/filter choices, in both continuation orientations.

No random sampling: exhaustive lexicographic enumeration, no seed. Child words
can be constructed using PrefixLeft nodes; right POPs using SuffixRightPops.
Each tested input has one Replay level. Continuation testing adds a second
Replay level, separately identified from the input DAG envelope.

The literal reference retains operation letters and cancels adjacent PUSH/POP
per ID, then implements mix by appending right POP letters and transferring
unmatched left POPs when pushes are absent. The compressed candidate uses
integer `(p,n)` composition and the formula above. They are different algorithms
with common supplied transition assumptions; neither is an independent Oracle
or proof that compiler source generates those transitions. This run does not
execute Rust or the frozen Oracle.

Observed scalar data are the exact per-ID counts/right debt, filter, active
family identities, the predicate that some active family is not contained in
the filter, and head intersection with `{A,B}`. These local observer formulas
are supplied assumptions, not full public type support. Family values are fixed
throughout: residual-family mutation, gamma construction, parameterized or
cofinite families, Swap/Both, certificate authorization, relation provenance,
late-edge invalidation, rollback, and arbitrary cyclic components are omitted.

For sharing, the DAG fold really compares one child vertex referenced twice
against two separately evaluated child vertices; the unused identity placeholder
is identical in both. Separate payload tokens may have identical numeric values. Ordinary exact
interning would merge copies with identical expression handles, so treating
such copies as separate vertices is an abstract unfolding experiment, not an
assertion that the baseline can construct duplicate interned expressions.
Distinct payload handles with equal detached values remain constructionally
distinct in the baseline, but their source availability is unproved here.

## Reproducible probe

Run the only Python fence in this file with Python 3. The script uses no files,
subprocesses, package imports beyond the standard library, or output artifacts.
One lightweight single-process probe; deadline 45 seconds; no builds.

```python
import itertools as it
import resource
import time

started = time.monotonic()
def words(k, limit):
    alphabet = tuple((i, sign) for i in range(k) for sign in (-1, 1))
    return [w for n in range(limit + 1) for w in it.product(alphabet, repeat=n)]

def literal(word, k):
    out = []
    for i in range(k):
        letters = []
        for j, sign in word:
            if j == i:
                if sign == -1 and letters and letters[-1] == 1:
                    letters.pop()
                else:
                    letters.append(sign)
        out.append(tuple(letters))
    return tuple(out)

def counts(word, k):
    return tuple((s.count(-1), s.count(1)) for s in literal(word, k))

def literal_replay(a, b, k, mix=True):
    word_a, right_a, _ = a
    word_b, right_b, _ = b
    left = [list(s) for s in literal(word_a + word_b, k)]
    right = tuple(right_a[i] + right_b[i] for i in range(k))
    if mix:
        residual = list(right)
        for i, debt in enumerate(right):
            if debt:
                for _ in range(debt):
                    if left[i] and left[i][-1] == 1:
                        left[i].pop()
                    else:
                        left[i].append(-1)
                residual[i] = 0
                if 1 not in left[i]:
                    residual[i] = len(left[i])
                    left[i] = []
        right = tuple(residual)
    return tuple((s.count(-1), s.count(1)) for s in left), right

def replay(a, b, mix=True):
    la, ra, fa = a
    lb, rb, fb = b
    left = []
    right = []
    for (p, n), (q, m), x, y in zip(la, lb, ra, rb):
        p, n = p + max(q - n, 0), m + max(n - q, 0)
        debt = x + y
        if mix and debt:
            if n > debt:
                n, debt = n - debt, 0
            else:
                p, n, debt = 0, 0, p + debt - n
        left.append((p, n))
        right.append(debt)
    filt = fb if fa is None else fa if fb is None else fa & fb
    return tuple(left), tuple(right), filt

def observe(value, families):
    left, _, filt = value
    active = tuple((i, families[i]) for i, (_, n) in enumerate(left) if n)
    violation = filt is not None and any(s & ~filt for _, s in active)
    heads = 3
    for _, family in active:
        heads &= family
    return active, bool(violation), heads

def fold_pair(x, shared):
    # Vertices: identity 0; payload X 1; optional payload copy 2; root last.
    nodes = [('identity',)] + [('payload', x)]
    if not shared:
        nodes.append(('payload', x))
    nodes.append(('replay', 1, 1 if shared else 2))
    cache = {}
    def visit(v):
        if v not in cache:
            node = nodes[v]
            cache[v] = node[1] if node[0] == 'payload' else replay(visit(node[1]), visit(node[2]))
        return cache[v]
    return visit(len(nodes) - 1), len(cache)

totals = dict(ordered=0, reversed_numeric=0, reversed_observer=0,
              missing_mix=0, sharing_roots=0, sharing_continuations=0)
best = None
for k in (1, 2):
    ws = words(k, 2)
    rights = [(0,) * k] + [tuple(int(i == j) for i in range(k)) for j in range(k)]
    filters = (None, 0, 1, 2, 3)
    raw = [(w, r, f) for w in ws for r in rights for f in filters]
    values = [(counts(w, k), r, f) for w, r, f in raw]
    continuations = [(counts(w, k), r, f) for w in words(k, 1) for r in rights for f in filters]
    # Numeric transition does not depend on family, so validate it once.
    numeric = {}
    for ai, a in enumerate(raw):
        for bi, b in enumerate(raw):
            result = replay(values[ai], values[bi])
            reference = literal_replay(a, b, k)
            assert result[:2] == reference
            assert replay(values[ai], values[bi], False)[:2] == literal_replay(a, b, k, False)
            numeric[ai, bi] = result
    for families in it.product(range(4), repeat=k):
        for ai, a in enumerate(raw):
            for bi, b in enumerate(raw):
                value = numeric[ai, bi]
                reverse = numeric[bi, ai]
                totals['ordered'] += 1
                totals['reversed_numeric'] += value != reverse
                obs, rev_obs = observe(value, families), observe(reverse, families)
                totals['reversed_observer'] += obs != rev_obs
                totals['missing_mix'] += value != replay(values[ai], values[bi], False)
                if obs[1] != rev_obs[1]:
                    size = len(a[0]) + sum(a[1]) + len(b[0]) + sum(b[1])
                    key = (size, k, repr((families, a, b)))
                    if best is None or key < best[0]:
                        best = (key, families, a, b, value, reverse, obs, rev_obs)
            x = values[ai]
            shared, shared_visits = fold_pair(x, True)
            duplicate, duplicate_visits = fold_pair(x, False)
            assert shared_visits == 2 and duplicate_visits == 3
            assert shared == duplicate
            totals['sharing_roots'] += 1
            for continuation in continuations:
                for first, second in ((shared, continuation), (continuation, shared)):
                    copy_first, copy_second = (duplicate, continuation) if first is shared else (continuation, duplicate)
                    assert replay(first, second) == replay(copy_first, copy_second)
                    totals['sharing_continuations'] += 1
        assert time.monotonic() - started < 45, 'incomplete: 45-second budget exceeded'
assert best[0][0] == 2, best
print('totals', totals)
print('minimal_order_witness', best)
print('wall_seconds', round(time.monotonic() - started, 3))
print('cpu_seconds', round(time.process_time(), 3))
print('peak_rss_KiB', resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
```

## Results and smallest witness

The exact executed command was:

```sh
python3 - <<'PY'
from pathlib import Path
p = Path('notes/progress/2026-10-10-replay-input-projection-model.md')
source = p.read_text().split('```python\n', 1)[1].split('```', 1)[0]
exec(compile(source, str(p), 'exec'))
PY
```

Exit status 0; all enumeration and mutation checks completed.

| Check | Coverage/result |
| --- | --- |
| Literal versus compressed numeric replay | 104,125 ordered child pairs, each with mix and without mix; no mismatch |
| Ordered replay including fixed family assignments | 1,607,200 cases |
| Lower/upper reversal changes exact numeric result | 382,600 cases |
| Lower/upper reversal changes a supplied local observer | 304,800 cases |
| Dropping directed mix changes numeric result | 1,194,500 cases |
| Shared versus identical duplicate root | 5,320 cases; no scalar mismatch |
| Shared versus duplicate through oriented finite continuations | 772,800 cases; no scalar mismatch |

The numeric universe is 70 child contexts for one ID and 315 for two IDs;
family assignments number 4 and 16 respectively. The continuation universes
have 30 and 75 contexts respectively. Filter intersection uses the same
supplied formula in both algorithms; its source correctness is not tested.
The literal differential checks cover counts/mix, whereas family enumeration
checks named scalar observer distinctions under the supplied observer rules.

The smallest order projection falsifier uses **one attachment ID and two
operation letters**. Let attachment `i` have family `{A}`; both child filters
are empty; right words are empty:

| Input DAG | Left result `(p_i,n_i)` | Active family | Local filter violation |
| --- | --- | --- | --- |
| `Replay(lower=POP_i, upper=PUSH_i)` | `(1,1)` | `{A}` | true |
| `Replay(lower=PUSH_i, upper=POP_i)` | `(0,0)` | none | false |

Both map to the same unordered multiset `{POP_i,PUSH_i}` of child inputs.
Literal PUSH-then-POP cancels; POP-then-PUSH leaves unmatched POP and live PUSH.
The bounded search found no order/filter-violation witness with fewer than two
letters, counting left letters and right POPs. This minimality is within the
stated finite envelope and operation-count metric. It does not minimize every
possible ContextExpr construction or establish an accepted source program.

The missing-mix mutation also has a two-letter witness: replay a left PUSH_i
against one right POP_i with empty filters. Mix cancels the PUSH and right POP;
omitting mix leaves the active `{A}` family. This is a supplementary mutation
of the same supplied operation contract, not a second source-semantics proof.

**Sharing result:** no scalar-observable counterexample was found for copies
that preserve attachment IDs and all payload values, across 5,320 roots and
772,800 continuations. The shared root evaluates the payload once; the split
root evaluates the identical payload twice; their Replay arguments are equal
values. The fold visits two versus three relevant vertices. That difference is
construction evidence, not an inferred public effect or type difference. It
does not justify erasing sharing from the approved recognizer certificate.

This exact negative result leaves a precise premise open: the current detached
single-valued algebra has no numeric operation that observes child handle
equality. To obtain a scalar sharing discriminator, an additional genuine
consumer would have to observe construction identity, mutate per-node state,
or correlate alternatives; none is supplied by this model. Duplicating a child
while freshening its attachment ID changes authority as well as sharing and
does not answer the identity-preserving duplication question. Likewise,
letting separate children choose independent symbolic valuations would add a
premise that this experiment neither adopts nor proves. The next experiment
should inspect the owning recognizer/certificate, rather than repeat a pure
scalar fold hoping to produce that missing premise.

Resource use: one Python search process, wall 8.088 s, CPU 8.026 s, peak RSS
55,836 KiB (Linux `resource.getrusage`). The 45-second deadline is checked after
each family-assignment block; no timeout, uncovered shard, or partial result.
Machine resource snapshot before execution: 20 logical CPUs, about 27 GiB
available memory; this is not an aggregate utilization measurement. No Cargo,
Rust tests, Oracle execution, benchmark, subprocess wave, or delegation.

Recommended next action: use a structural Packet 1 regression that distinguishes
`Replay(X,X)` from `Replay(X,Y)` with equal detached values but distinct retained
construction handles, checking the ordered child handles and dependency inputs
explicitly. Feed that requirement into Packet 2's certificate input contract.
An expected numeric inequality between those two roots is unsupported here.

Final dependency recheck: HEAD remained the pinned baseline; both HEAD blobs
above are unchanged, and the governing design's working-tree hash matches its
pinned blob. During concurrent Packet 1 work, the observed live source hash was
`55353446b4664b56cc94f85548daad7e7eaa84be`; its content/diff was not read.
All source claims in this note refer to the pinned Git object. Any current-source
bridge must revalidate that changed dependency after Packet 1 freezes.

No claim of source theorem, independent review, production defect, complete
public support, or certificate-recognizer sufficiency follows from the run.

## Commit packet

Exact leased path: `notes/progress/2026-10-10-replay-input-projection-model.md`.
Baseline: `9d4392ef4a4ef309c6c9c9194840deca3cbf6de6`.
Dependency hashes: the two pinned HEAD blobs above are unchanged. Concurrent
working-tree source hash changed to `55353446b4664b56cc94f85548daad7e7eaa84be`;
no reliance on or inspection of that moving source content.
Review status: unreviewed, research-only characterization; frozen before handoff.
Checks: the exact Python extraction/execution command above exited 0; exhaustive
counts/results above; read-only HEAD/blob/working-tree-hash and lease-path checks.
`git diff --no-index --check /dev/null <leased note>` emitted no whitespace
diagnostics (status 1 because the new file differs from `/dev/null`).
Proposed message: `research: characterize replay order and scalar sharing projections`.
Shared-record deltas intentionally left for the primary/curator: Packet 1 replay
regression rationale and Packet 2 recognizer contract; shared task/index/theory
files are not edited by this lease.
