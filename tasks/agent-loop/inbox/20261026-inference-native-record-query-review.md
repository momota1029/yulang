# Native record-query correspondence: independent M3 review

Date: 2026-10-26. Assignment/revision:
`20261026-inference-native-record-query-review`, revision 1.
Reviewer: `/root/native_record_query_review`, fresh generic leaf fallback,
nonauthor of the reviewed packet. No contributing descendants.

## Decision and scope

**ACCEPT for the frozen research source/native correspondence packet. No
BLOCKING or major finding; no mandatory repair.** Two minor textual precision
points are recorded below for primary adjudication. They do not affect the
finite shape construction, metadata equations after the evident type
unwrapping, or the explicit residual semantic premises.

This acceptance covers the paper and producer handoff identified below. It is
an independent source/mathematical/specification audit, not a fresh kernel or
native execution result. It does not accept the moving `NativeRecordPlan`
module or its companion paper; neither was used as evidence in this review.
The separate joint Lean-bridge review remains with the primary.

The unchanged parent is `SourceProblem.InferenceSoundness` at
`notes/theory/lean/YulangClosure/Contracts.lean:128`: for every supported
original source and scope, a generated solved problem must construct one
original source judgment and the corresponding `sameScoped` witness. This
packet does not discharge that quantifier. It neither adopts the selected
research manuscript as production semantics nor changes the supported source
domain, the inference algorithm, or the independent Call/effect obligations.

Primary-reported checkout baseline: branch `yulang3`, HEAD
`dd7d881ff58ff20cbfbea8db72126dbbecbc3a1a`. Producer's historical supplied
baseline remains `f5b947056f23fb50236463d86738bdea579c1514`. Git was forbidden
and was not used to verify either ref. The actual reviewed bytes were verified
by SHA-256; every source identity listed by the producer matched.

## Frozen artifacts and dependencies

| Path | Verified SHA-256 |
| --- | --- |
| `notes/theory/2026-10-26-native-record-query-correspondence.md` | `120b380acae1cf96c45f810f76ab56b375c84b23278c9904b94ffdc60c0e3bc8` |
| `tasks/agent-loop/inbox/20261026-inference-native-record-query.md` | `5abf9e4a683a2e75d064f78d8e5bab7df3a03a88ad0bdfe85e21067a9adbed89` |
| `notes/theory/lean/YulangClosure/RecordBoundaryPreservation.lean` | `1bde9224c1b0d568d5cc73d84a5ccc5f1157452c87ea2ff428096c1dbd50d056` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| `crates/yu-solver/src/candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| `crates/yu-solver/src/candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/candidate_value_graph.rs` | `aaaa88a374083f898188cd390b8cf0244855d8c09c8939b9e68ee2831bc692cf` |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| `crates/yu-hir/src/module/source_annotation.rs` | `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f` |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `docs/yulang-whole-language-semantics-ja-expanded-20261023.tex` | `28dc9b7fcb818e99a9513054d5847274ccce0d816a8c4a9644b802f0aa3fbd65` |

The paper, producer receipt and accepted Lean dependency were rehashed after
the source audit and still matched the frozen grant.

## Independent findings by obligation

1. **Total pure scan and failure precedence.** The actual record branch at
   `lib.rs:14593-14641` builds the first-name table with increasing source
   enumeration and `or_insert`, then scans targets in their original order.
   A missing optional target produces no native child and has an explicit
   absence slot in the mathematical skeleton. Every admissible common field,
   including optional/optional, retains one payload comparison and both
   original indices. Missing required terminates the scan, records the direct
   diagnostic and returns Rust `Ok(())` before any accumulated payload child
   is admitted or recorded as a diagnostic child. Optional-to-required returns
   `RecordAdaptationUnavailable` before memo admission. Thus the first bad
   target controls the disposition. Resource/receipt availability remains
   external to the total pure scan; no successful semantic route is inferred
   from Rust `Ok` or from this classification alone.

2. **Order.** `candidate_step_record_dispatch` at `lib.rs:15007-15029`
   admits index `n-1-k`, retains a pending item, then front-enqueues it and
   increments `next`. Together with `enqueue_item:15223-15243` and
   `pop_worklist:15166-15171`, this establishes exactly
   `[q(n-k),...,q(n-1)] ++ W` after `k` completed sibling enqueues. The final
   sibling queue has target order. The packet correctly excludes descendant
   scheduling and effectful runtime evaluation order from that equation.

3. **Metadata and interning.** `candidate_record_port_admit:3603-3633`
   uses the actual processing parent, canonicalizes the task pair, inherits
   `post_check_context(parent)`, its source set and its full scoped flow,
   interns the complete relation key, and records both original indices in
   `Dependency::RecordPort`. The local allowance-context branch cannot run
   for a Value child (`candidate_context.rs:3357-3372`). The stored task
   remains distinct from subsequent relation-key canonicalization; its
   endpoints may already have been canonicalized by `value_endpoint`
   (`lib.rs:11753-11777`), so it is not a replacement for the original terms
   and field indices. Each uninterrupted admission step restores the same
   current parent; preparation, RecordPort/Derived insertion and queue
   reservation neither process children nor change representatives or
   discharge state. `relation_with_scoped:3062-3093` therefore returns the
   same child RelationId for equal canonical pairs in that block. Distinct
   index incidences remain distinct dependency keys. This proves no semantic
   cast consistency across different generations, contexts or resumed
   histories.

4. **Authentic source trace.** The existing source text
   `my f {required, fallback = required} = fallback` is a genuine fixture
   (`candidate_effect.rs:2918-2939`); it was read, not rerun. The source/HIR
   record-pattern and action constructors preserve source identity and order.
   The owner at `candidate_effect.rs:1581-1607` generates default links at
   slots 258/259 and the two record bounds at slots 43/44. Opposite physical
   bounds and their exact retained BoundKeys generate Replay, followed by
   the two payload children `(0,0,r<=r)` and `(1,1,i<=i)`. The optional child
   is not skipped. Seed lookup and the sole `checking.insert` owner establish
   authentic `sources=None`; Apply slot 0 is not a formal slot. These Value
   seeds, bounds, Replay and children have IDENTITY context in this trace.
   Original occurrence/cause and producer provenance are separately retained.

5. **Operational event versus semantic boundary.** The source action,
   occurrence/cause, origin, replay inputs, actual dispatch step and current
   relation form a legitimate proof-side event product. The actual source
   drain receipt is published only after successful enqueue, and passive
   completion can be omitted on reservation failure. A ghost execution
   derivation can retain the event without claiming a retained completion
   record exists. Neither a reused RelationId nor the explicitly synthetic
   `Wait` establishes the manuscript's semantic boundary `j`.

6. **Application of the accepted record consumer.** With an injective finite
   label encoding, a shared endpoint interpretation and one resolver satisfying
   the selected cast equation for every hole, induction gives the stated
   `RecordBoundary.compile ... = some plan` equation. The accepted
   `compiled_run_preserves` additionally needs independent `ViewTyped`,
   `PresenceValid`, `ChildSound` and an actual `Run`; the all-false presence
   function supplies no optional-to-required witness. In the displayed
   equal-row instance, identity execution supplies the normal child contract
   and a pure run, for independently typed input. This is a mathematical
   instance, not evidence of a compiler-executed adapter. The required one
   resolver agreement is explicit: relation interning alone cannot construct
   it, and separately preserving casts cannot substitute for it. The original
   optional payload, nontransitivity and non-resurrection discriminators are
   preserved.

7. **Original-source gap remains explicit.** `SourceAnnotationValue` has no
   Record constructor. The inspected formal, annotation/ascription and
   record-literal equations do not attach an executable `RecMap_j` with a
   distinct output visible-view port. Section 7 correctly retains that exact
   source-elaboration obligation, or a source-authenticated classification
   as unchanged-view flow where appropriate. Reference/SCC incidence is not
   silently treated as such flow. The complete native Call certificate
   producer, child request/resumption contract, contextual meaning and
   generation/currentness transport remain independent obligations. No
   premise has been relabeled as whole-source proof closure.

## Minor textual precision points

- **MINOR, paper lines 211-212:** `raw query` is declared to be the stored
  `TypedPairKey`, but the next pseudocode line wraps it as `Value(raw query)`
  before `task_pair`. The exact typed equation is
  `relationPair = candidate_context_pair(raw query)`. Equivalently, first
  destructure `raw query = TypedPairKey::Value(rawPair)` and then apply
  `task_pair(LiveConstraintTask::Value(rawPair))`. Evidence is
  `lib.rs:15020-15024` and `candidate_context.rs:3612`. The intended
  canonicalization is unambiguous and all subsequent claims use it correctly.
  Closure, if the primary chooses a text repair: remove the redundant wrapper
  or name the unwrapped pair explicitly. No test or new proof is needed.

- **MINOR, paper lines 355-356:** local annotation allocates its fresh row
  before the check (`candidate_effect.rs:1761-1763`), then exposes the positive
  annotation into that row and returns it after checking (`:1770-1772`).
  Thus “creates a fresh root after its check” is imprecise allocation-order
  wording. “Uses a fresh root, exposed and returned after its check” matches
  the code. This does not change the separate input/output-port observation
  or supply the missing record adaptation. Closure, if selected: a text-only
  correction inspected by the primary.

## Authority, resources and cessation

Read the root operating maps, `rules/design-authority.md`, the Authoritative
top-level inference principles, goal-driven and M3 review rules, the complete
current native-inference progress note, the continuation selector, the
repository proof skill and its source/execution references. Inspected the
selected manuscript record/boundary clauses and the actual accepted Lean
consumer declarations; historical green tests and proof counts were not used
as proof of source correspondence. The project pin/config were read only.

Granted budget: 600 seconds; ZERO Lean/Lake invocations, Cargo invocations,
native tests or probes. Consumed: zero of every prohibited check; source reads,
searches and SHA-256 identity reads only. Review began at 04:37:11 UTC; the
substantive review was complete by 04:40:08 UTC, within 177 seconds, with this
receipt frozen immediately afterward. No Git, source/Lean edits, imports,
dependency changes, shared status writes, subprocess agents or children.
Requested specialist model/effort and effective runtime model metadata were
not provided by the launch packet; no role/model execution claim is made.

Exact write lease used: this receipt only. The granted isolated scratch path
`/workspace/scratch/f98087c7ac1a/inference-native-record-query-review` was not
used. All producer files and accepted dependencies remain untouched. Primary
owns adjudication, any minor text correction, integration and the separate
joint Lean-bridge review. **Writes stopped after this receipt; no descendant
leases or background work.**

## Revision 2: narrow paper-only delta acknowledgement

Date/time: 2026-10-26, review begun 04:42:10 UTC. Primary-authorized follow-up
budget: 180 seconds, zero checkers. Previous frozen review receipt SHA-256:
`538173c0300671f33d99e2205c0bbb35def0c46ec135bd3f2630b711d84010c1`.

**ACCEPT the corrected paper; both minor precision points are closed.**
New paper SHA-256:
`7e903edc8348d900954d655f82d9cadb623b47e8224e525602b3cef42777ccd1`.

The canonical-pair equation now applies `candidate_context_pair` directly to
the stored `TypedPairKey`. The local-annotation description now states that
the fresh root is allocated before checking and exposed/returned afterward.
Both changes exactly match the source evidence already inspected in revision 1.

A read-only byte comparison reversed precisely these two replacements in
memory. Each replacement occurred once, and the reconstructed original had
SHA-256 `120b380acae1cf96c45f810f76ab56b375c84b23278c9904b94ffdc60c0e3bc8`.
This establishes that the delta contains only the acknowledged corrections
and their local line wrapping. All fourteen other table entries (the producer
handoff and thirteen source/dependency inputs) were rehashed and unchanged.

No unrelated accepted scope was reopened. The original exclusions, open
semantic premises and separate `NativeRecordPlan` review remain unchanged.
Consumed: source text/hash reads only; zero Lean/Lake, Cargo, native tests,
probes or other proof checkers, within the 180-second grant. Only this
acknowledgement was appended to the existing receipt. No producer files,
Git, imports or shared status were changed. **Writes stopped again after
this revision; no descendants or background work.**
