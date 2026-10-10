# Restoration replay: snapshot derivation and remaining dynamic bridge

Date: 2026-10-10
Status: unreviewed conditional derivation and bounded source characterization; R remains open
Assigned baseline: `e25608d5881123438c57bcba354571611fd98283` on `research/simple-sub-intrusion`
Producer: `/root/restore_replay_proof_fallback`, prover-equivalent generic leaf; no descendants
Exclusive lease: this note only
Requested settings: `gpt-6.1-sol` / `high`; observed model/effort: unknown
Frozen at handoff; no compiler, test, authority, or gate-status promotion

## Frozen question, quantifiers, and exclusions

The original question R quantifies over successful physical-bound restorations
in the admitted candidate route, including restorations whose synchronous
callbacks drain qualifying parent/copy SCCs: does the fixed saved opposite
count and subsequent live-vector iteration cover every contextual and
incoming-use diagnostic obligation of the admitted canonical bound?

The quantifiers remain over actual constructors and consumers, both Value and
Effect, every retained bound fiber, both bound polarities, and the actual
incoming `ConstraintOccurrenceId` and `CauseId`. No single arbitrary fiber is
selected to stand for the rest. A completed comparison from an earlier use
does not by itself discharge the new use's diagnostic obligation. Source
reachability must be established separately before an operational state is
called a source-program counterexample.

Let `c_s` be `canonical_extrusion` in state s and
`K_s(o,p,b) = BoundKey(c_s(o),p,c_s(b))`. Let `F_s(k)` be the complete linked
list returned by `bound_relations(k)`. Physical vectors are the canonical
owner's direct rows followed by exact nonvariable bounds, as consumed by
`candidate_opposite_bound`. Historical fibers remain stored after equality;
their presence does not imply that they contain every subsequently attached
canonical derivation.

This note proves a narrower snapshot theorem S and describes the merge
fallback actually present. It does **not** replace R with S. In particular,
R's source/operational activation bridge, the effect of later canonical-fiber
growth, and the completeness of incoming-use reporting after nested mutation
remain open. HIR carrier approval, arbitrary effect hygiene, complete Call,
source-wide termination, soundness, principality, and F5 cutover are excluded.
The assigned claim class is conditional derivation/bounded characterization.

Common hypotheses: the candidate graph and feature are present; endpoint and
relation indices are valid; the representative forests are well formed; the
restoration entry assertion supplies an idle worklist; no external mutation
interleaves these synchronous Rust calls; all operations being quantified as
successful return `Ok`. For a failure claim, a matching outer route transaction
must actually execute rollback before a subsequent consumer. These are not
claims about all compiler initialization paths or arbitrary direct API calls.

Authority is the approved contextual attachment/admission design §4: bounds
retain contexts/origins, opposite replay keeps ordered parent derivations and
shared inputs, qualifying parent/copy equality transfers contextual obligations,
and rollback restores the complete route. No new behavior is selected here.

## Exact theorem S: one incoming replay snapshot

For every invocation of `candidate_context_restore_replay(l,u,t,publish)` in
this envelope, let s be the state just before `candidate_context_replay_impl`
reads its two literal bound heads. If relation construction, resource sampling,
and the callback all succeed, then the callback receives one list position
for **each ordered pair** `(a,b)` in `F_s(l) × F_s(u)`. The position retains
`Dependency::Replay { child, lower:a, upper:b, lower_input:l, upper_input:u }`;
its context is identity when both inputs are identity and otherwise the exact
ordered `ContextExpr::Replay { lower:context(a), upper:context(b) }`.
Different positions may contain the same interned child relation; the theorem
counts parent-pair positions, not distinct child IDs. It does not assert that
the supplied literal fibers are complete canonical fibers.

Derivation from `candidate_context.rs:1930–1994`:

1. The task pair is canonicalized at entry. The two `BoundKey` arguments are
   looked up literally at 1943; no corresponding key canonicalization occurs.
2. `incoming_use=true` sets `old=(None,None)` independently of recorded replay
   progress. The first rectangle walks all saved lower entries against all
   saved upper entries. The second rectangle is empty because its lower start
   and stop are both `None`.
3. `bound_entry` reads immutable predecessor links (1535–1537). During list
   construction, this method creates contexts, relations and dependencies,
   but does not attach another bound fiber. Synchronous publish has not begun.
   Thus the saved linked lists are stable throughout this enumeration.
4. Ordinary dependency dedup is guarded by `!incoming_use`; it cannot suppress
   a restoration list position. `dependency` may itself reuse an existing
   dependency, but the subsequent `replay.push(child)` still occurs.
5. Replay progress is recorded, resources are sampled, and only then is
   `publish` invoked. The owning restoration callback calls
   `constrain_live_item` separately for every list position with the given
   incoming occurrence/cause (`candidate_extrusion.rs:635–640`).

This is a source derivation, not a finite-model checker that assumes replay.
It proves what the actual consumer constructs. Empty literal fibers yield an
empty product and no nested comparison; successful return alone supplies no
additional activation.

## Corollary S-stable: a complete fixed restoration frontier

Fix one successful restoration. Let s0 be the state after insertion and before
the first loop iteration. Suppose throughout that loop:

- the canonical owner and restored endpoint do not change;
- the owner's opposite direct and exact vectors do not change;
- the relevant inserted and opposite bound fibers do not change.

Then restoration publishes the entire Cartesian replay for each physical
opposite occurrence present in s0, with the incoming occurrence/cause. This
holds for both polarities and kinds, including duplicate endpoints and
self-bounds. It is a fixed-frontier corollary, **not** a source-derived
stability invariant and not the answer to R across SCC draining.

Proof: insertion canonicalizes both endpoints and attaches before vector push
(`candidate_extrusion.rs:422–423`, `candidate_effect.rs:332–336`,
`candidate_context.rs:1869–1910`). Restoration canonicalizes its locals again,
saves the complete opposite count, and iterates exactly indices `0..count`
(`candidate_extrusion.rs:611–634`). Under these hypotheses every index is the
corresponding canonical s0 occurrence and both literal keys are their complete
fibers. Apply S to each iteration. Order is lower then upper regardless of
whether the restored bound is positive or negative.

## Nested execution invalidates the stability premises

The source does not grant the preceding corollary's stability premises.
`constrain_live_item` seeds the incoming source occurrence, drains the typed
worklist, and at every empty boundary calls `settle_candidate_intrusion`
(`lib.rs:11822–11845`). The call can change representatives and vectors before
the outer loop resumes. It restores enclosing processing scopes on success or
error (`lib.rs:12107–12111`); restoration has not itself opened a transaction.

The outer loop saves `bound` and `count` once. It canonicalizes the owner for
each read and key construction, and canonicalizes each newly read opposite
endpoint. It does **not** recanonicalize the saved bound when constructing the
inserted key (`candidate_extrusion.rs:612–633`). The consumer canonicalizes the
task pair but still reads those supplied keys literally. Consequently
`BoundKey(c_s(owner),p,saved_bound)` can be a historical mixed key rather than
`K_s(owner,p,saved_bound)`. Neither nonemptiness nor absence is inferred from
that syntactic distinction.

The saved count is also not a saved vector. An append to direct rows shifts
every exact slot's combined index; owner equality can switch to a different
canonical row's prefix entirely. Successful insertion only appends; successful
merge appends both sides before aliasing and retains the copy's storage
(`candidate_intrusion.rs:549–589`). Within this insertion/merge envelope the
canonical opposite **total length** cannot decrease: at an alias transition
the destination contains its old entries plus all source entries. Hence a
saved in-range index remains in range. This total-length result is not a
coverage result: endpoint identity at the same combined index can change.

## What merge replay rescues, and what it does not prove

For every successful `merge_candidate_rows(copy,parent,root,parent_index)`, the
following sequence is source-derived (`candidate_intrusion.rs:513–609`):

1. Resolve copy and parent, transfer every source bound on both sides through
   insertion and `candidate_transfer_bound_origins` while source storage is
   intact. Transfer walks every source fiber, not an arbitrary representative
   (`candidate_effect.rs:436–466`).
2. Change the representative forest, then canonicalize the entire previously
   retained bound-entry prefix. Canonicalization transports changed keys,
   preserves historical keys and adds equality `Derived` lineage before replay
   (`candidate_context.rs:1996–2014`).
3. Advance equality generation, mark dirty, and reopen the Value root when
   present. Enumerate **all** parent lowers, and for each call ordinary replay
   against **all** current parent uppers. These replay callbacks enqueue and
   do not synchronously drain, so the merge's own enumeration has stable
   representatives/vectors.

Thus a merge has a complete *merged-owner physical pair enumeration* at that
boundary. Its contextual callback is ordinary replay: only frontier deltas
whose exact dependencies are not already retained are enqueued. Unchanged
frontiers can publish an empty list. Those facts do not by themselves prove
that every earlier retained dependency was already executed successfully, or
that every obligation has been reported for this incoming use.

Two source facts prevent a premature diagnostic-loss allegation:

- With a Value `root`, `candidate_replay_bound` records `root → child` in the
  diagnostic graph **before** contextual frontier/dedup handling
  (`candidate_extrusion.rs:666–675`). Merge reopens that root, and the enclosing
  drain completes diagnostic deltas and replays its witness using the incoming
  occurrence/cause (`lib.rs:12088–12090`). A skipped contextual callback is
  therefore compatible with retained diagnostic coverage.
- The empty-worklist boundary calls `candidate_task_scope(initial)` before
  settlement (`lib.rs:11839`). Merge insertions use `candidate_bound_origin`,
  which picks that processing origin; `candidate_context_bound` creates a
  `Derived` edge from the retained matching relation or the origin's source
  relation (`candidate_effect.rs:332–336`; `candidate_context.rs:1876–1909`).
  Effect reporting traverses `children(pair)` from both the raw initial pair
  and its canonical pair; that traversal expands children of **all** relations
  on a reachable pair (`candidate_effect.rs:524–588`,
  `candidate_context.rs:1516–1522`). New transferred-bound dependencies can
  consequently make merge conflicts reachable from the current use.

The second fact is an actual possible rescue path, not a proof that every
merged-owner or third-owner obligation is reachable. Exact parent choice,
context discharge, canonicalization timing, and which sides were inserted
remain relevant. Relation-level transport alone is not an executable
constraint edge: `Dependency::Transport` deliberately adds no ordinary edge
(`candidate_context.rs:1456–1458`). Equality canonicalization additionally adds
its own `Derived` edge; these two cases must not be conflated.

Third-owner incidence is especially precise: canonicalization visits third
owner fibers, but the merge's physical replay enumerates the merged parent,
not every third owner (`candidate_context.rs:1999`; compare
`candidate_intrusion.rs:599–607`). The old key retains its earlier fibers;
canonical transport and subsequent insertion can add fibers at the canonical
key without writing them back to that historical key. No historical-to-current
fiber-completeness theorem follows from successful storage coverage C.

A localized conditional seam is useful here. Suppose a still-distinct third
owner O already retains both `O + b` and `O + B` with retained post-check
contexts x and y, and restoration of `O + b` saves b. Suppose its first nested
drain merges the actual recorded copy b into B while O stays distinct. Equality
canonicalization unions the transported x lineage into `O + B`; it does not
move the existing y lineage backward into `O + b`. At a later upper U the outer
loop can therefore use literal `BoundKey(O,+,b)` while the admitted canonical
fiber is `BoundKey(O,+,B)`. If y is absent from the historical fiber, S enumerates
x-derived inputs and supplies no y-derived list position at this invocation.
No absent-key premise is needed: both keys can be nonempty.

This is a conditional characterization of the actual lookup/transport order,
not a constructed API or source counterexample. It assumes the two incoming
incidences and the nested merge; it does not prove they arise from normal
freshening, that x/y remain distinct after discharge, that the y obligation was
not already activated, or that its incoming diagnostic cannot be reached by
the actual reporter. Those are exactly the rescue/source facts a falsifier or
proof must supply. The dual negative-bound family uses `O - b` and `O - B`.
This isolates a third-owner fiber-union seam even when the opposite vector is
unchanged, so investigation need not start with a larger shifted-slot trace.

## Reduced missing premise for R

The owning insertion/replay/merge paths establish S, fixed-frontier coverage,
canonical storage, and merged-owner pair enumeration. The precise unresolved
bridge is this:

> For an actual admitted restoration, every required incoming-use obligation
> excluded from a later literal-key snapshot by representative change, bound
> fiber growth, or changed combined-vector indices is either activated by a
> successful ordinary replay in the same drain with complete retained lineage,
> or already validly discharged; every retained conflict/consequence requiring
> incoming-use reporting is reachable by the current initial Value diagnostic
> root or Effect pair traversal before that use returns.

This is a missing source invariant, not an assumed lemma or a newly selected
semantic restriction. It has two independently visible seams: contextual
activation through historical versus current canonical fibers, and diagnostic
reachability through ordinary merge replay. Solving only one does not establish
R. A minimal falsifier must exhibit an actual required fiber/obligation excluded
from **both** the outer snapshot schedule and these nested rescue paths, while
respecting constructor origin attachment and merge replay. Merely showing a
shifted slot, stale endpoint, empty ordinary callback, or different relation ID
does not meet that burden.

No source witness or API counterexample to that bridge is established here.
The previously rejected claim that the two-pair trace lacks
`BoundKey(O,+,b)` is not reused: the preceding nested `b <: O` comparison
inserts precisely that historical key before either merge. It supplies a fiber
and can supply retained propagation/diagnostic lineage. The exact injected
setup also lacks an authentic ordinary-Value capture construction according
to the separate reachability audit. There is no compiler-defect conclusion.

This static pass stops at this reduced premise. A direct snapshot derivation
and an independent-in-method nested consumer trace both reach the same dynamic
activation/reporting seam; another equivalent canonical-key restatement would
not prove it. Under proof-obligation economy, admitted contextual obligations
and correct per-use reporting are correctness/natural-inference concerns;
universal arbitrary API-state closure is a stronger characterization. The
natural owner of evidence is the restoration/ordinary replay execution route
that already knows the selected fibers and current cause. This note proposes
no production metadata, semantic clause, source restriction, or behavior change.

## Failure, publication, and rollback boundaries

Replay builds all list positions and commits replay-head progress **before**
calling publish. A callback can process several positions and fail on a later
one. The replay helper frees its scratch vector on the resulting error, but
does not undo its persistent dependencies, heads, or completed earlier nested
drains locally (`candidate_context.rs:1986–1994`). Therefore "published replay
heads" cannot be used as evidence of successful full callback execution in a
route that has not reached its success/rollback boundary.

`with_route_transaction` commits only when its operation returns `Ok`; on
error it calls matching route rollback (`lib.rs:9155–9176`). Context rollback
restores replay-head logs, bound heads, relation/dependency/edge prefixes and
processing/discharge state (`candidate_context.rs:1059–1137`). Route rollback
restores physical vector lengths, row metadata, typed memos, incoming reported
errors and other journaled state (`lib.rs:9347–9444`, intrusion undo). Thus the
conditional derivation can use only successfully finished callbacks or the
fully restored pre-route boundary. It does not certify arbitrary failed direct
API calls or member graph/certificate publication outside these journals.

The existing static test inspection includes
`third_owner_incoming_bound_survives_parent_copy_intrusion_and_rollback_retry`
(`candidate_context_tests.rs:1366–1434`) and the replay-frontier failure test
immediately following it. They are authored assertions, not executed evidence
in this assignment. Neither inspection proves R across all nested mutations.

## Checks, resources, settings, and commit packet

Checks: bounded `cat`, `sed`, `rg` source/rule/skill reads and `sha256sum` only.
No Git command, Cargo process, build, test execution, benchmark, executable
model, source-program run, descendant, compiler edit, shared-record edit, or
question-board action. Zero measurement samples. Tool dispatch included batches
of up to four independent short source-read commands; observed OS process
concurrency and aggregate CPU/RAM were not measured. No sustained compute
process ran. Work stayed within the assigned 45-minute wall-time ceiling.
Requested Sol/high is the assignment request; runtime model/effort metadata is
not exposed, so observed settings remain unknown. This is a generic proof leaf,
not evidence that a custom `prover` role ran.

Direct source/design SHA-256 dependencies observed at handoff:

| Path | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_extrusion.rs` | `3fd1c7234c38013343e1c2e72bfed06c4eecdf7173e27d7581e11d6df84f0b3a` |
| `crates/yu-solver/src/candidate_context.rs` | `2897c168c02640443a2f1280286a648853afe08324294c53f1c95d373ac3a337` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/candidate_effect.rs` | `2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e` |
| `crates/yu-solver/src/candidate_scheme.rs` | `582bfb741315534dacf7290bb5618452bb55d9949a8aac691d8d01b93720de11` |
| `crates/yu-solver/src/lib.rs` | `9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `.codex/agents/prover.toml` | `485a26c7409e16c692ad10095031ab0e7084726ec5da5666082b3bbc4a5daf98` |

Dependencies were not changed by this leaf. Comparison with the assigned Git
baseline is left to the primary under the no-Git packet. Governing instructions
read: `.codex/agents/prover.toml`, `.codex/config.toml`, active orchestration,
research-lab, design-authority, compiler-engineering and git-concurrency rules,
and the `yulang-proofs` skill. The active repository generic-worker fallback and
explicit leaf packet govern instead of the skill's older nested CLI launch.

Next action: independently adjudicate S and the exact missing activation/
reporting bridge, then test that bridge on one authentic nested source
construction; do not promote restoration coverage from storage nonemptiness.

Commit packet: exact lease
`notes/progress/2026-10-10-canonical-bound-fiber-restoration-proof.md`; baseline
`e25608d5881123438c57bcba354571611fd98283`; changed dependency hashes none by
this leaf; unreviewed conditional research checkpoint; static reads/hashes only;
proposed message `research: derive restore replay snapshots and isolate dynamic coverage bridge`.
Shared deltas left to primary/curator: retain R as open; record S and the two
actual merge diagnostic rescue paths without asserting source reachability,
compiler defect, or gate closure.
