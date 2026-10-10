# Distinct-tail later restoration source trace

Status: frozen, unreviewed bounded source characterization. No production conclusion.
Producer: `/root/source_restore_trace`; frozen at the primary's stop instruction.
Baseline: `4d8e56eecfc8ab1600476eb519e0901a30609069` (HEAD remained equal).

## Objective, method and exact premise

Observe the first later ordinary local use after the established selective
owner/copy SCC witness, and determine whether it presents a missing ordered
restore fiber that survives actual replay and diagnostic consumers. This is a
real parser/HIR/candidate execution with logging added only to a pinned private
source copy, not a supplied-transition model or a constructive theorem.

The target premise remains unestablished: a later use must capture/restore the
same owner bound involving R43 and S49, with a particular ordered lower/upper
relation fiber omega whose child remains absent after all relevant consumers.
The observed later use has real restores, but **does not capture R43 or its
S49-positive-R43 bound**. No missing omega, rescue impossibility, soundness
failure or global restoration theorem follows.

Authority: contextual-attachment-admission design §§4–6; parent-copy SCC
intrusion, “Selected operation and compiler responsibility.” Preserve actual
parent/copy equality, row orientation, attachment identity and exact retained
contexts. No new semantic meaning, source restriction or implementation change.
The yulang-proofs skill and research-lab, design-authority, git-concurrency,
testing, performance and agent-orchestration rules were read. This leaf supplies
complementary executable evidence; it does not claim to be a prover or delegate.

## Exact source and HIR/action evidence

The source is exactly the ordinary-source witness in the assigned note:

```yulang
act E
my left (f:int -> ['r] int) g = { my bridge (consume:(int -> [E, 't] int) -> ['x] int) = ({ my cb z = { my old = f 1; consume cb }; my feed = g bridge; consume cb } as [
    E
    'x
] int); bridge }
```

Parser structural recoveries: `[]`. Actual local HIR is retained in
`/tmp/yulang-distinct-tail-restore-20261011/known.log` under `TRACE HIR`.
The diagnostic collector is `ConstraintBatch::collect_candidate_mode(hir,true,true)`;
this is private candidate evidence, not public/default concrete-formal admission.
No source continuation was added (0 of at most 2 allocated).

Observed zero-based action order:

| Action | Event and checkpoint |
| --- | --- |
| 35 | Local slot 1, occurrence ordinal 22: earlier cb use, before merge |
| 38 | Root Ascription at occurrence ordinal 7, Local scope ordinal 0, root effect row `[E,'x]` |
| 42 | Lambda(1); C55 merges into S49 after X-copy 53 merges into X29 |
| 43–46 | Fact, Install slot 0, Fact, Fact; generation 8 |
| 47 | Local slot 0, occurrence ordinal 23, value component 7, level 1: final `bridge` use |
| 48–55 | Candidate(7), facts, outer lambdas and final Link |

At action 42 the retained merge order is
`E53→E29`, `E55→E49`, `E56→E49`, `E61→E46`, `E62→E8`,
`E63→E7`, `E64→E47`, `E65→E5` (generations 0 through 8).
The targeted C55→S49 merge is the second merge (generation 1→2).
The selected source witness's pre-merge SCC qualification is an input from the
assigned note; this observer records actual merges but does not rerun the
whole physical SCC/path qualification oracle.

At action 47 a captured graph with live root V5 and boundary 1 contains 52
bounds. It contains neither node R43 nor a bound whose endpoint is R43.
It includes `BoundKey(E22, Negative, E49)`; S49 is an older anchor rather than
an owner whose bound collection is copied into this captured graph.
The 52 actual restore calls reconstruct other owner bounds. For example:

```text
E72 Positive E54
E72 Negative E49
E29 Negative Allowance(5)
E77 Positive E29
E83 Positive E29
```

There is no action-47 restore with raw owner R43, bound R43, or raw owner S49.
The graph has no captured `BoundKey(E49, Positive, E43)` or
`BoundKey(E43, Negative, Allowance(1))`. This is the discriminating checkpoint:
ordinary later use occurs, but its capture does not instantiate the target
same-owner restore premise.

Within action 47 the actual merge order is
`E57→E35`, `E58→E27`, `E60→E39`, `E67→E27`, `E59→E25`,
`E66→E25` (generations 8 through 14). Thus copied tail T'66 ultimately equates
with T25 during this later use. This does not contradict the earlier selective
pre-merge witness. Every action checkpoint has an idle typed worklist; final
`execute_candidate_source_root` result is `Ok(())`, with `errors=[]`.

## Ordered fibers, replay and rescue boundary

The observer logs actual restore BoundKeys, opposite-input relation lists,
ordered `(lower,upper)` relation IDs and resulting child relation/context,
merge queue snapshots and post-merge dequeues. Over the whole source it records
66 restores, 516 replay-input observations, 66 restore replay child events,
219 post-merge dequeues, 14 merges and 56 action checkpoints. These counts are
finite trace coverage, not an enumeration of all source programs.

Every printed relation key has `ContextId(0)`; the context-node vector is empty
(identity is implicit). Ordered dependency IDs remain visible, but this source
trace provides no distinct nonidentity contextual omega on the targeted restore.
It does not justify identifying all derivations merely because their contexts
are identity.

Retained target fibers remain visible at action 47's checkpoint:

```text
BoundKey(E43, Negative, Allowance(1)) -> RelationId(175), context 0, completed Some(0)
BoundKey(E49, Positive, E43)         -> RelationId(186), context 0, completed Some(8)
BoundKey(E55, Positive, E43)         -> RelationId(198), context 0, completed None
BoundKey(E43, Negative, E49)        -> RelationId(186), context 0, completed Some(8)
BoundKey(E43, Negative, Allowance(3))-> RelationId(270), context 0, completed Some(8)
```

An uncompleted historical raw fiber by itself is not a missing required child:
its canonical transport/comparison can already have a completed relation.
No assertion of loss is based on `RelationId(198)`'s raw completion value.

Actual consumer source was inspected at the baseline:

- `candidate_extrusion.rs:599`: restoration inserts the physical bound, traverses
  opposites, and uses `candidate_context_restore_replay` to constrain children.
- `candidate_context.rs:1998`: incoming-use replay resets old cursors and visits
  the ordered lower/upper fiber product; both identity inputs produce context 0
  while retaining `Dependency::Replay` with the exact ordered IDs.
- `candidate_context.rs:2064`: canonicalization transports third-owner bound
  incidence before merge replay and retains a derived relation dependency.
- `candidate_intrusion.rs:549`: actual equality transfers both bound sides,
  origins and contexts, canonicalizes bound incidence, then replays lowers.
- `candidate_scheme.rs:1118`: local routing captures a live scheme, freshens it,
  restores captured bounds and admits an actual Value link transactionally.
- `lib.rs:11885`: Value memo handling can skip completed relations, route a raw
  alias to its canonical pair or replay retained structural children.
- `lib.rs:12091`: completed constrain routes call effect-conflict replay and
  diagnostic completion; `candidate_effect.rs:524` traverses retained relation
  children from raw and canonical initial keys to report cached conflicts.

These are static owning-consumer correspondences plus normal execution through
their callers. The observer does **not** separately instrument every rescue
branch, enumerate semantic denotations, check Call/handler behavior or certify
all restored Cartesian products. Success with no reported error is not evidence
that an unspecified missing omega is impossible or rescued. The precise blocker
comes earlier: this source's post-merge captured graph omits the targeted owner
bound, and no independent expected omega is supplied.

## Reproduction, resources, dependencies and omissions

Commands run:

```text
python3 /tmp/yulang-distinct-tail-restore-20261011/prepare.py
/usr/bin/time -v bash /tmp/yulang-distinct-tail-restore-20261011/build.sh
python3 /tmp/yulang-distinct-tail-restore-20261011/run.py
```

The preparer copies `crates/yu-solver/src` from `git show BASELINE:path`; it
adds observation statements and a standalone main without cfg(test), compiler
rule changes or retained-test changes. Build is a single `rustc` binary compile
with shadow-apply-candidate/shadow-f5, cached extern rlibs, codegen-units=1,
clang/mold linking, CPU affinity 0, 120s timeout and AS limit 1.5 GiB.
Build exit 0: 4.47s wall, 3.26s user + 0.39s system, peak RSS 483368 KiB.
Known-source observer exit 0: 0.115599s wall, 0.056956s user + 0.052887s system,
peak RSS 9128 KiB. Log size 575055 bytes, below the 32 MiB limit.
No concurrent Cargo/rustc process was visible before launch. One compile and
one source run; no Cargo/test suite, benchmark, parallel build or Git mutation.
Four warnings belong to the scratch standalone build; no production warning
claim or compiler edit is made. The first preparation invocation used absent
`python` and exited 127; it was rerun successfully with `python3`.

Baseline solver input hashes are retained in scratch `baseline-hashes.json`.
Direct authority/source-note hashes at freeze:

```text
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc contextual-attachment-admission design
8ae4348a93dce6df1852a34b2294ebc5e4e256d8b018c1f6eaad42c502470a8e parent-copy SCC intrusion design
d2bd5926bc150dd9b22dda999406abbd08098a3409bc77e82f8c6aacf8445e5d assigned ordinary-source witness note
```

Cached dependency artifact hashes (not built by this leaf):

```text
d1b06781b3972c4862b4e94e84dc5bbf94a665ca2fe37edfd30f8eb3883c5fdb libyu_hir-f6c83eec0523eca7.rlib
8d0f416b569cc13ed21bb0e2548203fec1af5767b7fc8b1731870448a3e9a969 libyu_core-a0ec78e751fcc385.rlib
f418fc20f54db15cd874fe13e2c56cc828d444a51a70794b43f2126ff08c557b libyu_types-e9e5becba653059a.rlib
e98291abea56d66af0f7ba5e7f81cb34201fe79cd0bfc0b3bb4135007fad0265 libyu_syntax-d13e5e6aeab2e54f.rlib
```

Cached artifacts' exact source commit/build derivation was not independently
established; their byte hashes and successful ABI linkage pin the experiment.
Parser/HIR and solver execution are authentic observations, but share the
compiler's implementation assumptions. There is no independent semantic oracle.
No random seed/range, transition-model oracle or mutation test was used.
Omitted: the two permitted continuations, exhaustive source search, nonidentity
fiber construction, full per-branch diagnostic instrumentation, rollback/retry,
public admission/cutover and all-source restoration/correctness. Search stopped
at the targeted capture premise and then the primary's explicit freeze order.

One recommended next action: construct a later source use that actually captures
or restores `BoundKey(E49,Positive,E43)` (or an explicitly mapped same owner),
then specify an independently justified ordered input fiber before checking its
child across the recorded consumer chain. This trace alone cannot supply that
premise.

## Commit packet

Exact leased outputs:
`/tmp/yulang-distinct-tail-restore-20261011.md` and private scratch directory
`/tmp/yulang-distinct-tail-restore-20261011/` (copied observer sources,
prepare.py, build.sh, run.py, baseline-hashes.json, observer, build.log,
known.yu, known.log, known-resources.json). No repository path changed.
Baseline SHA: `4d8e56eecfc8ab1600476eb519e0901a30609069`.
Changed dependency hashes: none; direct hashes recorded above.
Review: frozen unreviewed research characterization; no independent review.
Checks already run: standalone compile and one exact ordinary-source execution;
static owning-consumer reads and dependency hashes. No production test suite.
Proposed research-checkpoint commit message:
`research: characterize later distinct-tail source restoration capture`.
This tmp-only packet itself has no repository paths eligible for staging.
Shared-record deltas intentionally left for primary/curator: record that action
47 restores 52 other bounds and eventually merges the tail pair, while the
same-owner restore/ordered-omega premise remains open because R43 is absent
from that use's capture. Preserve the established earlier selective witness.
No task/index/theory/authority/question-board record was edited. Writes stop here.
