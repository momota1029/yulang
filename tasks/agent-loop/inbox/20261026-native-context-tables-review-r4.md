# Native Context tables r4 — independent compiler referee

Date: 2026-10-26. Reviewer: `/root/context_tables_review_r4`.
**Decision: ACCEPT for the represented native table-lifetime / Context-driver
combined-history construction.** The one batched minor warning finding is closed.
No mathematical, original-source correspondence or scope-blocking finding remains.
This is not acceptance of complete `SourceProblem.InferenceSoundness`.

## Scope, independence and authority

Fresh nonauthor review of the frozen table-lifetime construction, its direct
accepted dependencies, native owners and original theorem contracts. The only
repository write lease is the resulting review receipt. No proof, producer,
configuration, scheduling, shared import or Git mutation is performed by this
reviewer. There are no descendants. The bounded assignment permits 900 wall
seconds and at most two concrete-risk Lean bundles; no redundant clean build
is requested. Governing root/pre-sprint instructions, design authority,
current inference principles, sprint/review policy and the Lean skill and
source/execution references were consulted.

The original goal remains complete native correspondence and
`SourceProblem.InferenceSoundness`, retaining the original source domain and
same scoped witness. Acceptance of this construction cannot supply authentic
runtime extraction, full Effect/Value semantics or a successful source judgment.

## Source and theorem assessment

| Responsibility | Independent assessment |
| --- | --- |
| Native constructor coverage | Compared all actual writes of the Context/weight/View/contribution vectors in `candidate_context.rs`, `candidate_effect.rs` and the relevant extrusion/intrusion inputs. The represented table mutations are Context interning, zero-word source weights, signature/copy View allocation, and contribution append. All six Context constructors survive. Context IDs use vector index plus one with zero reserved for Identity; other vector IDs start at zero. Existing-key lookup precedes allocation and remains valid near the index limit. |
| Full retained payload | Source weights preserve exact ordered allowed members, View boundary, owner/position and attachment polarity/scope/member ordinals/unit-push condition. View records retain both source and executable closed-weight handles, operation origin and requested tail. Contributions retain effect, source origin and actual instance index. Opaque source identities remain raw data inputs, not fabricated source-semantic certificates. |
| View publication order | Native `candidate_signature_view` reserves the View index/capacity, may append the source weight, publishes the View, then samples. `Draft` and its stages represent that order. Weight-before-View and Context/weight-rollback-before-View windows are explicitly present; neither is hidden by an assumed global table well-formedness property. Operation Views and open annotated Views preserve their distinct weight rules. |
| Copy validation | `copyInput` checks the actual original View and the same six comparisons as native `validate_payload_view`; missing source weight and incompatible closed-weight state fail. The operation/annotation distinction, owner, position, ordered allowed data, source attachment and new requested tail survive. External remap storage and substitution meaning remain separate, as the note says. |
| Interner cache | `native_interner_cache` derives insertion or reuse from the complete expression. No-duplicate expressions follow from actual construction history. `native_cache_rollback` removes exactly the drained suffix; its derived no-duplicate premise prevents deleting a retained key through a duplicate in the removed suffix. `prefixIdentity` is the same actual cache lookup, not an independently stable oracle. |
| Forward lookup and missing answers | `run_prefixes` derives four vector prefixes; `run_table_extension` derives positive read preservation and existing prefix-ID preservation. An earlier missing answer may become present. `allocated_lookup_extension` correctly requires allocation. Successful operand transport uses the native closed-weight availability guard; it does not assume all missing lookups or all Views are globally stable. |
| Evaluator transport | Read the actual parser/weight/child-source/operand/filter/prepare/finish proof cases. Every successful evaluator result is carried by the source-derived extension. `VersionedChecks` retains every original filter and its order while permitting constructor allocations between checks. The maps, availability and other callback inputs remain the explicit original inputs to this represented slice. |
| Reindexing the driver | `Reindex.state` preserves every underlying control/key/task/route/owner/memo/seal/receipt/map/Derived-edge field. `Reindex.step` handles every constructor of the accepted driver, including queued-key Transport, fresh/cached Context, early publication/sampling, active-owner memo admission, duplicate return, Value Context/return and settlement/merge. A live owner does not become sealed merely through migration. |
| Common history and cancellation | A dependent `Joint` contains the store and driver indexed by its actual table projection. Table steps derive extension and migrate that driver; Context steps use that same store. `JointHistory` starts from the constructed empty state. Cancel derives the vector/cache restoration and restores the same saved driver checkpoint; native journal erasure/authentication is explicitly still an application boundary. No arbitrary equality of unrelated table functions is an input of the committed roots. |
| Births and versions | Allocation births, version stamps, observation lists and history receipts are proof annotations. Raw numeric indices rewind on cancellation; the ghost clock does not. A retry gets a later birth, and positive or missing observations retain their actual cut. These records are not asserted to exist in Rust, nor read from optional completion telemetry. |
| Parent application | `committed_tables_context_readback` applies the prior quiescent theorem to a Run derived from this combined history. `committed_tables_original_body` retains the exact NoCurrent cut and obtains a stored original BodyRecipe, previous checks, Derived edges, whole sources/transformer and absent Effect demand. `committed_tables_whole_child` proves complete child payloads of that body, not semantic child success or existence of a terminating continuation. |

The source-qualified lifetime issue is addressed constructively: the example
allocates a closed View, weight, prefix Context and contribution, cancels them,
and reuses the same raw Context ID with a different birth and expression. Both
parser results are computed in legal constructed histories. This is not a
counterexample to source soundness and is not used to narrow accepted source.

## Batched minor finding — CLOSED

One batched minor finding: the initial final producer build replayed 21 warnings
originating in the new module. They consist of unnecessary `simpa`, unused simp
arguments, one unused binder and a globally registered lambda-headed simp lemma.
The final census itself was clean. Under the repository's rule for warnings
introduced by the active change, this required a local repair before integration;
producer check 19 now builds the same construction with zero warnings.
The 21-line repair changes only unnecessary `simpa`, unused simp arguments,
one unused binder spelling and the unsuitable global simp attribute on
`Reindex.map_put`. Every existing use names that lemma explicitly. No proposition,
semantic guard, definition or dependency changed; no linter was suppressed. The exact warning list/excerpt and initial frozen evidence are
retained under `context-tables-review-r4/`.

## Initial frozen evidence verified

The initial frozen source is
`fdb227b46a0029d5338c152a67700488bf9dbb161ae30e73ec09995a168a7740`.
All 18 pinned native/dependency/config inputs and all 190 manifested producer
artifacts were independently hashed. The complete 771,138-byte originating
census, hash `bba69be02f7086d48b3cac07c1e159f0c8ae313acf6a45da832ec570ad6b2a73`,
contains 1,125 unique balanced declaration blocks, 521 theorem constants,
145 distinct named theorem roots, 65 private declarations and 43 private
theorem constants. Every complete type and axiom set reconciles with the
origin inventory and EOF trailer. No replacement character, type elision,
originating project axiom, sorryAx or unchecked native-evaluation dependency
is accepted. The actual origin-index enumerator includes generated/private
constants and checks transitive axioms; the named roots are only a subset.

The theorem axiom distribution is 260 none, 118 propext, 113 propext+Quot.sound,
and 30 additionally Classical.choice. All 18 producer check receipts and
retained repair failures are preserved. The first reviewer integrity script
failed only at its strict no-warning assertion after all artifact/type/axiom
checks passed; that failure led to the reported warning repair. The amended
read-only reconciliation distinguishes clean census output from build warnings.

No new Lean process has been used by the reviewer: the remaining risk concerns
source correspondence, output completeness and the final narrow repair delta,
all checked against the existing exact compiled evidence. No default-target
integration or complete binary refinement is inferred from the focused checks.

## Final freeze and independently reconciled delta

The producer stopped writes again at **2026-10-26 12:54:27 UTC**. The final
manifest contains 397 owned artifacts, including the complete pre-review snapshot
and every failed check. I independently hashed each manifested artifact and all
18 unchanged live/isolated inputs, then reconciled all unique complete printed
types and transitive axiom sets with the final origin inventory and EOF trailer.
The final census still has **1,125 declarations / 521 theorem constants /
145 named roots / 65 private declarations / 43 private theorem constants**.
Its 771,138 bytes have no diagnostics, truncation, replacement characters,
forbidden axioms or unbalanced/duplicate declaration blocks.

All 145 named root inventory entries are byte-identical before and after repair.
Of all 1,125 entries, 1,123 are byte-identical. The only remaining differences are
generated `step_fresh._simp_1_6` becoming `_simp_1_5`, and `_simp_1_7` becoming
`_simp_1_6`; their complete types and axiom sets are identical under that exact
renaming. This comparison was independently performed from the two full
inventories, not inferred from the producer's delta claim. The source diff has
exactly the 21 requested changed lines. The note and handoff delta updates the
verified evidence and preserves the original scope and remaining owners.

| Accepted artifact | Exact SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/NativeContextTables.lean` | `eaf2b037af40af01ad116e1ae413a6c7d5a0023d49c8b9f1b92d29c319d2df81` |
| `notes/theory/2026-10-26-native-context-tables.md` | `2333038f316391be3cdceb3d732d12ffe23cb10e7055462fb1b2e2b786383d86` |
| `tasks/agent-loop/inbox/20261026-native-context-tables-r4.md` | `bf4114ff9fe8d6304cc882ec6c00215e39273a80166bfb95dbde0ac1c96aaed9` |
| Final `context-tables-r4/freeze.json` | `c29ecbcc08b366013dfcc6a406606c15929d0528e32f933cb64139992b3ecd15` |
| Final `artifact-manifest.json` | `bf2474525e65e5531ccb57739669a57a8f5543477484a6448ddaa57c6fa090b0` |
| Unchanged `inputs.json` | `182e58373d3c2379ef9036b8bb90df2ab5390707831a617705b59de84ad0cd51` |
| Final `check19-origin-census.log` | `ec9858b8f1f923d47fddf1e627227e060ff96bdcfdcbfde9331474420b8db32d` |
| Final `origin-inventory.json` | `f48c9d108b76d3a4a5c388500e03ae6a503c227e2774955dac45bd7ed05162e3` |
| Initial freeze, retained | `125eacdcce98a327ba9e8e82f94d1ce4ab21a3e4c736322180b195c437dc8bac` |
| Reviewer `final-evidence-integrity.json` | `12a1c31323b4f432e82be443eca0a396a64764c5c56cf854a5dc25431328290b` |
| Reviewer `independent-final-delta.json` | `c6c97cab15db41d9266ad6a36ec99d4c4aaea72b2c24c050fb3b41a0317e0bbc` |

Producer check 19 invokes the pinned Lake version and Lean version, builds the
exact module, and runs the complete audit using `-j1 -M1024`. All four commands
exit 0; build and audit have no warnings. It took 14.749 seconds under its
120-second bound, with one thread and child maximum RSS 1,022,980 KiB.
The only review repair consumed one additional focused producer check: 19 of
24 total, cumulative measured 261.166 seconds, maximum 55.687 seconds.
Failures 01, 03–13, 15 and 16 and the original warning-bearing final build remain
retained. The source/census delta introduces no concrete risk requiring a
redundant Lean invocation by this reviewer: **0 of 2 reviewer bundles used**.

Reviewer evidence lives under
`/workspace/scratch/f98087c7ac1a/context-tables-review-r4/`; the complete frozen
producer bundle lives under its sibling `context-tables-r4/`. Initial immutable
copies, the failed strict integrity assertion, its warning diagnostic excerpt,
final copies, independent integrity and full inventory delta are retained.

## Original boundaries retained

The fixed table lifetime premise is discharged for the represented combined
history. Authentic native callback/control events, complete raw relation/task
and scope inputs, source cuts, row representatives and carriers, complete
Value/Effect dispatch, settled acceptance and original full semantic bodies
remain with their actual owners. Allocation/resource failures, external
substitution/remap ownership and whole runtime journal extraction are not
manufactured from a generic Ok result. The model can record a conflict and
return locally; a BodyRecipe is not conflict-free source subtyping.

Optional `source_drain_completions` can fail to record an observation while
inference succeeds. None of the accepted roots requires its presence. Original
Call, Function, effect hygiene, source-world interpretation, sameScoped,
principality, termination and production promotion are not closed here.

## Cessation and handoff

This independent review is complete within the original 900-second packet.
Only this receipt and the reviewer's owned scratch were written. No Git,
source/note/producer/import/configuration/shared-status mutation, descendant,
background worker or Lean process was started by the reviewer. All reviewer
writes and processes stop on producing this receipt. The final exact scope is
ACCEPT for the represented construction, with all original semantic and runtime
extraction obligations above still OPEN. Integration and Git actions remain
with the primary.

Receipt finalized: **2026-10-26 12:55:49 UTC**.
