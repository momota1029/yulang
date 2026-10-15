# Native relation duplicates: mutable reads and the retained-child gap

Date: 2026-10-16
Status: historical pre-repair mutation audit; its local native operational
retention obligation is discharged by the independently reviewed repair and
composition linked below. No observable semantic counterexample is claimed.
Baseline: `87ac89419`; native owners `bf0562382`.
Exclusive write lease: this new note only. No compiler/shared-record edits.

Primary adjudication: independent `checked_result_semantics` accepts a MAJOR
at the producer/consumer boundary under contextual attachment §4. Ordinary
diagnostic consequences do not certify the actual whole-Value extrusion
rewrite required by `candidate_context_value_rewrite`. The primary authorizes
restoring that existing responsibility boundary; this is not certification of
an observable counterexample or of the universal duplicate theorem. The
producer snapshot is `1259423fa8fb4a2ad12a8abfb7c4528c3c12512f0481ffa1a238f82cbac39185`.
Other mutation-audit cases below remain bounded research evidence pending
closure review. See the [repair gate](../progress/2026-10-16-native-value-rewrite-provenance.md).

Post-repair receipt: the [actual retained-rewrite invariant](2026-10-16-native-retained-value-rewrite-invariant.md)
§§8–9 replaces the unsupported diagnostic-frontier premise with genuine
producer provenance and composes the original native operational case split.
Independent semantic review accepts this exact scope; the primary accepts
the result after focused/phase verification. The old producer body below
records the original obstruction. Source MODEL, semantic adequacy of the
underlying rewrites and full H2/U remain OPEN.

## 1. Frozen original claim

For every current successful production candidate-mode execution, whenever
`pair_is_current` suppresses Value/Effect dispatch, all required current
context checks, retained rewrites, ordered replay and necessary evidence
propagation must already be retained or owned by its active drain. Later
relevant mutations must incrementally propagate their consequences or
invalidate suppression. Include canonicalization, Function children,
restoration and later bounds. No static-snapshot restriction is substituted.

Authority: [top-level principles §§1–5](../design/2026-10-11-yulang-inference-top-level-principles.md)
and [contextual attachment §4](../design/2026-10-10-contextual-attachment-admission-design.md).
Consume the reviewed [initialization replay](2026-10-15-extrusion-initialization-replay-invariant.md)
and [owned-drain completion](2026-10-16-extrusion-replay-capture-completion.md)
at their actual scopes; the independent
[publication attack](../progress/2026-10-16-extrusion-replay-publication-falsifier.md)
does not prove semantic duplicate redundancy. Source MODEL, complete H2/U,
semantic context algebra, generalization and production cutover remain separate.

Method: follow every mutable read relevant to a dispatch branch to its writer
and consequence consumer. Completion is not assumed sound because a memo
exists. The first unclosed case below is a producer of a completion stamp;
therefore an invariant for subsequent `pair_is_current` skips cannot assume
that case correct.

## 2. Exact skip identity and stage ordering

There are two production `pair_is_current` calls, `lib.rs:12468,12480`, in
Effect and Value dispatch. In candidate mode (`:11585–11596`) the predicate is

```text
raw typed_pairs contains the supplied task key
AND actual processing RelationId R has completed[R] == intrusion.generation.
```

Relation R is interned by the full immutable key
`(pair,context,sources,scoped)` (`candidate_context.rs:2569–2600`). Context DAG
nodes, source sets and scoped transformers/flows are interned immutable values.
A different context, source-set or scoped flow therefore does not inherit a
completion stamp from endpoint equality. A new raw diagnostic alias cannot
skip solely because its canonical relation was stamped: raw key presence is
also required.

The production gateway (`lib.rs:12079–12080`) selects the actual retained typed
drain. Its Transport and Context stages (`:12389–12401`) canonicalize retained
relation identity and execute context checks **before** Dispatch. Hence a memo
cannot bypass the current relation's context admission/discharge entrypoint.
Effect dispatch additionally invokes `candidate_enqueue_evidence` before
checking the memo. Value work received relation/evidence at enqueue or its
owning port/replay admission, before it reaches this predicate.

`mark_candidate_pair` (`candidate_intrusion.rs:352–384`) stamps only canonical
tasks, during `record_typed_pair_admission`. A raw alias records diagnostic
state without completing canonical semantic processing. The stamp can precede
descendant execution. The reviewed drain invariant supplies ownership of the
Function cursor, queued rewrites/children, replay acknowledgements and pending
intrusion until successful return; it does not justify omitting an obligation
which was never retained or queued.

## 3. Mutable read -> writer -> consumer inventory

| Mutable information read by skipped dispatch or its ordinary operation | Writer and retained consumer |
| --- | --- |
| Value/effect row representatives | Only qualifying `merge_candidate_rows` changes representatives in production. It copies both sides/origins, canonicalizes all bound fibers, increments intrusion generation, and replays at the merged owner (`candidate_intrusion.rs:518–611`). Old stamps are no longer current. Forest compression alone preserves representatives. |
| Existing row levels used for side/orientation or structural extrusion | Candidate extrusion creates fresh rows; it does not lower existing source rows. Existing candidate levels/non-generic joins change with merge, under the same generation invalidation. Source levels initialize before actions. Base `extrude` lowering is behind candidate-disabled dispatch branches, not a hidden same-generation candidate writer. |
| Row lower/upper arrays and bound fibers | Ordinary candidate Value/Effect application inserts the bound and then calls `candidate_replay_bound` (`candidate_extrusion.rs:844–905`). Every physical opposite is enumerated; replay uses both exact BoundKeys and attached fibers. New bounds need not invalidate all old relation stamps because the writer schedules their own intersections. The retained-child exception in §4 is not covered by this argument. |
| Extra fiber on an already present bound | `candidate_bound_origin_with_evidence` constructs/attaches the actual context fiber before testing its simpler origin duplicate key (`candidate_effect.rs:426–455`). Ordinary insertion/replay sees updated heads. Replay's two delta quadrants cover new-lower×all-upper and old-lower×new-upper (`candidate_context.rs:3406–3459`). Already admitted exact Replay dependencies remain retained; source restoration's incoming-use mode separately replays diagnostic obligations. |
| Context discharge/residual | `candidate_context_execute_relation:3201–3290` runs before every skip. A first discharge installs/checks the exact Allowance registration and replays its existing lowers before retaining discharged/residual state. Later registered filters remain physical upper bounds, so new lowers run their ordinary replay. Context/weight operands do not mutate in place. |
| Support/member/Allowance data and contribution identity | Views, allowed sets, optional tails and contribution records append; existing records are not retargeted on successful production paths. `candidate_check_effect_operand:973–1046` expands Support into all fixed members plus the live tail relation, or checks a fixed nominal member against its original allowed set/tail. A tail's later bounds use the retained row relation. |
| Function child endpoint handles | Structural terms are immutable; dispatch canonicalizes child row endpoints through the current representatives. Same-generation children remain the same four actual pairs; a representative mutation increments generation. Port scope/context/source data is retained per relation, not inferred anew from endpoint shapes. |
| New FunctionPort/Derived/Replay evidence edges or attachment bundles | `dependency`, `edge` and `bundle_edge` backfill existing parent bundles into a newly added child edge. `bundle_link` propagates a new bundle along existing successor/eligible zero-use transport edges (`candidate_context.rs:2365–2402,2660–2755`). Thus either arrival order is covered independently of memo dispatch. |
| Source-support registration lifecycle | New FunctionPort dependencies increment **lifecycle_generation** and invalidate affected watched source-support registrations. This is distinct from **intrusion.generation** used by pair suppression. It is not an invalidation of semantic completion, nor needed for bundle backfill. The present synthetic registration constructor is cfg(test); no production source certificate is inferred from it. |
| Source qualification and retained extrusion groups | Source Value graph/SCCs are sealed from collected source before session actions; a source set's qualification does not mutate under a relation ID. A new source-set relation cannot reuse another relation's completion. Genuine retained extrusion reuse recaptures its output group under the new source set, queuing newly qualifying parent/copy pairs (`candidate_intrusion.rs:317–349`). |
| Diagnostic/raw occurrence origins and completion | Raw pair presence is separate from relation stamps; origin/evidence admission and diagnostic dependencies are retained. Successful drain Diagnostics and acknowledgements consume their owned work. A diagnostic child is not, merely by being stored, an extrusion-rewrite certificate (§4). |

For mutation by merge, generation is published after bound/fiber transport and
before ordinary merged-owner replay. Those transport constructors do not drive
source actions or nested dispatch during that interval. Canonical bound
transport includes third-owner occurrences (`candidate_context.rs:3612–3632`),
not just the merged row's outgoing storage. Later raw work is transported to
the new full relation key before the memo test.

Restoration copies have their explicit transport/attachment, insertion and
replay owners, not a fresh unconstrained pair-cache lookup. The imported replay
and drain theorems cover the exact work they emit; neither imported theorem
says an arbitrary diagnostic child is a sufficient rewrite for a new relation.
On availability failure the source action does not return successful dependent
publication; this note introduces no rollback/retry requirement.

## 4. First uncovered read: all diagnostic children treated as rewrites

The Value branch at `lib.rs:12494–12509`, after `pair_is_current` was false,
reads `typed_pairs[memo_key].children`. Unless both endpoints are Function
constructors, **any nonempty child vector** causes it to:

1. record/stamp the current relation;
2. iterate every child, call `recapture_candidate_extrusion`;
3. form `candidate_context_value_rewrite(key,child)` and enqueue that child;
4. return without `candidate_apply_value` on the original row relation.

The intended producer is an actual structural extrusion: its transformed
child and parent/copy graph must be reused, not rebuilt. But the vector also
has another production writer. Ordinary `candidate_replay_bound`, called from
`candidate_apply_value`, invokes `record_diagnostic_edge(parent,child,None)`
for every Value opposite replay (`candidate_extrusion.rs:817–824`). Its parent
can be an ordinary **row/row** relation. No extrusion output/group is required.
Function-port and canonicalization edges also share this diagnostic container;
the Function/Function exclusion does not distinguish row/row replay children.

`recapture_candidate_extrusion` does not validate this distinction: if no
matching output group exists, it just returns without adding a group. The
rewrite constructor retains a Derived relation/context for the selected
child, but it does not attach the new parent relation to the skipped original
BoundKey. A completion proof therefore needs either a genuine retained
rewrite invariant at this read, or a separate completeness argument for the
diagnostic frontier being substituted. The code does not test such a tag.

### Authentic source/action trace reaching this mixed use

Use the ordinary, unscoped source constructor route for the following small
graph (no execution/type-success probe is claimed):

```yu
my apply (f: 'a -> int) (x: int) = {
    my first = f x;
    f x
}
```

This uses supported source forms and the actual annotation/Name/Apply actions;
the static trace does not edit session state or call test-only constructors.
Let p be x's formal row and a the distinct scoped argument annotation variable
of f. Both are at the formal level. The source constructors give:

| Source/action step | Actual native consequence |
| --- | --- |
| Visit annotated f and x before their body (`candidate_source.rs:714–750`) | Formal actions execute the paired f target and Int+<=p, p<=Int-. |
| Both Name-x occurrences (`:620–624`) | Both arguments use exactly CandidateEndpoint::Parameter(x), not separate Name expression rows. |
| First f x in local first initializer | Its Apply and any required whole-demand extrusion retain p in the argument field: p's level is already the receiving formal level. Function Argument dispatch reaches p+<=a-. |
| First row application | Equal-level orientation owns B=(p,Negative,a); Int is already a positive lower of p. `candidate_apply_value` inserts B and replay records diagnostic child Int+<=a- on parent (p,a). |
| Second f x after the initializer/Install actions | Same Argument endpoint pair (p,a); a different source Call occurrence owns a distinct source association and hence a different full relation R2. The source Value graph records every actual Apply event separately (`candidate_value_graph.rs:166–177`). |
| Dispatch R2 | Its memo stamp is absent, so pair_is_current is false. But the shared raw (p,a) diagnostic children already include Int<=a. The retained-child branch stamps R2 and replays that child instead of inserting/attaching R2 at B. |

The Call sources are nonrecursive parameter uses: their receiver is the
parameter Value f, which has no return path to their source owner in this
graph. No qualifying merge is needed for this trace. The ordinary complete
action drains ensure the first row's diagnostic child exists before the second
Call action. Source action generation places first initializer/Install before
the final expression; this is not an arbitrary reordering of queue entries.

R2 now has a Derived path to its current Int<=a child, but the persistent B
fiber from the first row application retains R1's source association. The
second branch does not attach R2 to B. The exact missing storage is therefore
identified, as is its completion-stamp producer. It cannot be dismissed by
the correct statement that pair_is_current keys include sources: this branch
is what supplies the new R2 stamp in the first place.

### This is not yet a semantic counterexample

Here x's annotation also supplies p<=Int. The current Int<=a consequence may
be a complete semantic substitute for p<=a in this specific graph. Thus the
trace does **not** prove that a required program outcome or type constraint
has been lost, and does not authorize an implementation repair by itself.

The exact still-uncovered mutable read is the **lower-bound frontier of p**
after a relation was completed by this shortcut. New direct lowers are written
by ordinary insertion/restoration/merge owners. Ordinary replay enumerates
only bound fibers actually attached at B; it cannot reconstruct the absent
R2 fiber from endpoint equality. If the retained children are a complete
future-stable source frontier, their existing row children/closed upper
contracts may already cover every later contribution. That stronger property
must be proved from actual source producers and their later mutations, not
assumed from a diagnostic edge or from the queue-completion theorem.

In particular, merely proposing a later arbitrary Bool lower on p in this
example is not a source-qualified falsifier: p:Int already rejects it. Nor
does a synthetic edit adding such a lower satisfy this packet. A separating
source trace must produce a later legal contribution not already represented
by that retained frontier, with its necessary context/source consequence.
No such complete separating trace was established in this bounded pass.

## 5. Consequence for the original universal statement

The mutation audit establishes the local key/context ordering, writer-owned
opposite replay, generation invalidation, Function-drain ownership and
incremental edge/bundle propagation arguments above. It does not establish
the original universal duplicate-preservation theorem because a current
completion stamp can come from the unclassified retained-child branch.
Assuming that stamp redundant would assume the memo-soundness conclusion.

The remaining premise is now at one concrete owning read, with a real
production writer and source-generated schedule: whether ordinary diagnostic
replay children can replace a new full row relation for **all later relevant
mutations**, or whether reuse must be justified by a genuine retained
extrusion-rewrite witness. This is not another publication-order question.
The active drain only completes the selected child work; it cannot manufacture
the original bound fiber omitted by that selection.

One next action: attack/prove this retained-child frontier at
`lib.rs:12494–12509`, using the source trace above as the minimum real entry
case and a later source-owned lower/transport mutation. Distinguish a tagged
extrusion rewrite from ordinary bound-replay diagnostic edges. A source probe,
if the primary authorizes one, should observe those two producer classes and
the exact bound fibers; it must not test arbitrary mutated state as source
reachability. No compiler change or new readiness/solver policy is proposed.

## 6. Snapshot, checks and commit packet

| Input | SHA-256 |
| --- | --- |
| solver lib.rs | `199963ac9cd13eebca44c4881b859eeb1f801259cc944bf1d5a57df78dc0c070` |
| candidate_context.rs | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` |
| candidate_intrusion.rs | `2158e7377686189ed90d8b8d8803dbb446368abb52b7e0cb24b2282ebe41007c` |
| candidate_extrusion.rs | `2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b` |
| candidate_effect.rs | `44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9` |
| candidate_source.rs | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| candidate_value_graph.rs | `d08f6c5fb9ae4c5f005b6cb40aa3462f4f58b350cd6842b76a15d2dfdb520bec` |
| top-level principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| contextual attachment design | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| initialization replay proof | `cb1ffafb226d1b8443c6d6f3206b5205fc2ec760137e58e16b964f659d67797c` |
| replay/capture completion proof | `f286eb3d0280b614caf2a870aa36204ff766241033c9dc49b75f01cde9d87fd7` |
| independent publication falsifier | `622873c766f9f3a5ae8bf7bc6bd7469216715d79f85b760a9335285fd818cac9` |

Native files are under `crates/yu-solver/src/`. Checks: bounded static reads,
symbol/call-site searches, dependency hashes, note whitespace/fences/local
links. No tests, builds, source probes, Git operations, production/shared edits
or children. One bounded normal prover pass; requested configured Sol/high,
effective runtime metadata unavailable. Zero executable samples/heavy processes;
CPU/RAM not instrumented. This proposes no implementation/runtime overhead.

The original theorem, source MODEL, H2/U, context semantics, generalization,
principality and production gates remain OPEN. Independent review pending.
Sole changed path is this note; baseline `87ac89419`; dependencies unchanged.
Suggested checkpoint: `research: audit native relation duplicates and isolate retained-child frontier`.
Shared-record delta left to primary: consume the concrete mutable-read case
and retain universal duplicate preservation at that owner, without recording
a compiler defect or proof closure before independent adjudication.
