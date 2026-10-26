# Native Context expansion: executable factoring and the installed body

Date: 2026-10-26. Status: kernel-checked construction; independent review pending.
The original `MERGE-EXPANSION-COVER-1`, native accepted-return correspondence,
and `SourceProblem.InferenceSoundness` remain OPEN.
Author: `/root/context_expansion_r4`, bounded generic proof leaf.
Baseline supplied by the primary: `37ec9da2aaca2d7b806887d06d9bbd8b0fc5439c`,
branch `yulang3`. No native implementation or semantic authority is changed.

## 1. Original target and the premise removed here

The original parent, `SourceProblem.InferenceSoundness` in `Contracts.lean`, is

```text
for every supported source s, original scope x, generated constraints d,
and solution a: there is one source witness e with
sourceJudgment s x e and sameScoped s x e a.
```

All original source forms, optional records, method selection, complete Call,
effects, generalization, lexical/event scopes, and the shared witness remain
in scope. The fixed Value-birth-level qualification is unchanged. This packet
does not infer an arbitrary native model or source witness from row equality.

The immediate construction is the full Context part of
`2026-10-26-native-replay-lifecycle.md`, section 6. Earlier
`NativeMergeExpansion` constructed particular installed filter carriers and a
residual; `NativeReplayCurrent` constructed an operand graph. Neither computed
the complete outgoing Context body. In particular, its extensional `ClosedAt`
cannot recover which body was installed.

The new `NativeContextExpansion.lean` computes that outgoing body from the
actual parser and local callback operations. It includes **every filter**, in
native order, and exactly one of consumed-endpoint absence or the residual
dispatch. A graph event installs this computed body, registers all its child
keys, attaches all its fibers, and retains the original-parent edges. The
all-depth consumer reads precisely this installed body. No complete-Context
coverage proposition, arbitrary favorable child list, semantic solution,
`LocalLaws`, or admission-completion law is an input.

This removes the former *outgoing full Context clause* as an assumed graph
law. It does not complete the separate construction of the event projection
from one actual committed native execution. The exact outstanding Context
seam is described in section 7, including the already-discharged branch and
publication-before-Dispatch cuts. It would be incorrect to report the whole
native frontier as closed.

## 2. Parser inventory and allowed input

`Expr`, `Weight`, `View`, and `Tables` retain raw immutable native identities.
The Effect projection uses all seven existing endpoint constructors. Source
sets and transformers retain their complete interned IDs. `effectTables`
selects the actual closed weight's allowed list when present; ordinary views
use their own allowed list. No default transformer replaces a scoped flow.

The following is the complete `candidate_zero_word_filters` case inventory
at `candidate_context.rs:3670–3765`.

| Case | Exact successful action / rejection |
| --- | --- |
| Identity ID 0 | Pop without table lookup. Top-level identity execution bypasses parsing. |
| Already visited `(id,mode)` | Pop without reprocessing that mode. A visit in another mode is distinct. |
| `PrefixLeft` in outer mode | Require smaller input ID; update residual to input; continue the outer spine. |
| `PrefixLeft` in Replay mode | Require identity input and smaller input ID; record Replay-filter presence. |
| `PrefixLeft` in directed mode, or nonidentity input in Replay mode | Reject. |
| Accepted prefix payload | Require the weight and boundary view, empty local words, matching owner and position, and exact `closed_weight`; append the first occurrence of that weight. Repeated weights remain deduplicated. |
| `Replay` | Require both children smaller than this ID; visit lower before upper. Directed mode stays directed; the other modes enter Replay mode. Only an outer Replay sets the residual-Replay flag. |
| `Swap` / `WithoutLeftFilter` | Require smaller input, record a directed residual, and continue in directed mode. |
| `SuffixRightPops` / `BothFromRight` | Reject in every live mode, including a supplied certificate. |
| End of scan | Reject mixed Replay filters and a directed residual. A pure Replay residual becomes identity; a directed residual retains its exact Context ID. |

`scanStep` implements this stack, visited set, ordered filter deduplication and
all structural guards. `scanLoop` counts stack iterations. It is not a new
supported-input limit: `scan_run_computes` constructs sufficient fuel for every
finite successful scan transcript, while `scan_computes_run` gives the reverse
readback. `parsed_no_mixed` and `finish_pure_replay` establish the parser's two
distinct residual conditions. Allocation/resource success is projected by the
driver's `Availability.parser`, not inferred from a syntax tree.

`expand` requires the actual canonical processing key and successful entry
preparation. `decompose` checks the nonzero-transformer self-relation rejection
before installing any check. `executeInput` also rejects an Effect demand.
For Value requests, `valueContext` accepts only transformer zero and identity
or an empty-filter parse. It returns the **same complete Value request**;
the endpoint type is arbitrary, and all stored Context, source-set, and whole
optional demand fields survive. `filtered_value_rejected` covers the rejected
Value/filter case. Indexed Value dispatch is the next owner's operation; it
has not been replaced by a trivial Effect or terminal case.

## 3. Every callback, residual, and child key

`decompose` runs `collect checkFilter` on the entire parser output.
`decompose_exact` proves an ordered `Aligned` relation between filter weights
and results, the exact post-check Context, consumed condition, continuation
presence, and publication-success guard. `every_filter_executed` derives both
the exact count and an executed check for each selected weight. This is not
the earlier assertion that one selected filter fiber exists.

`Check.registered` records which native filter branch was taken:

* An already registered row/Allowance bound runs origin attachment and Replay.
  It does not require another physical insertion. `applyFilter` and
  `registered_filter_constructed` implement this branch.
* Otherwise `applyEffect` uses the actual reflexive, row placement or operand
  branch. A new physical bound requires successful origin attachment,
  physical insertion/readback and Replay callbacks.

Each inline check keeps the original complete processing parent. A checked
row/Allowance fiber has identity Context, the parent's source set and the
parent's full transformer. The validated weight/view relation models the
native `checking_filters` guard that licenses that identity Context.

The residual is absent **exactly when** the original upper is an Allowance
whose boundary occurs among the executed checks. Otherwise the original
directed comparison is dispatched with the exact post-check Context. Both
row/row level branches, row/rigid, and rigid/row placement are computed by
`placedBound`; `placed_bound_pair` proves the stored polarity still denotes
the original directed pair. There is no assumed residual fiber or favored
storage owner.

Empty-filter execution is different from publication. Even if an empty pure
Replay parsed to residual zero, native execution does not publish a discharge;
`empty_filters_keep_stored` proves that the retained Context stays the stored
parent ID. Nonempty execution publishes only after **all** checks and the
publication reserve/sample guard succeed.

Operand execution retains all existing `Effect.checkOperand` cases: Bottom,
every indexed Support member followed by its optional row tail, Contribution
and AnnotationMember membership, closed-weight allowed input, Allowance tail,
conflict and unavailable. A successful native mismatch callback records a
conflict and returns `Ok`; it is represented by `Leaf.conflict`, not by local
semantic success and not by an availability error. Availability failure
prevents a body from being installed. Diagnostic acceptance remains a later
obligation.

`admit` computes each entire child key using its child-local
`candidate_context_source`, canonical endpoints, inherited sources and whole
transformer. It verifies the actual nonzero PrefixLeft(weight,Identity)
interner result when needed, the child self-relation guard, and enqueue
success. `apply_children_admitted` retains the ordered alignment with the
actual emitted operand list. `whole_child_payload` and
`full_body_child_payload` derive the exact payload and guard for **every child
in the whole Context body**, including children of inline filters and of the
residual. No child-currentness or child-completion premise is supplied.

`nonzero_self_child_rejected` is a useful falsifier of an overly strong source
application: a Support tail can compute a canonical self-pair, but with a
nonzero transformer that child cannot successfully be admitted. Conversely,
an inline reflexive `candidate_apply_effect` call creates no child relation;
its actual local return remains represented. These are distinct native checks.
No source-qualified counterexample to the original inference theorem was found.

## 4. Installed construction, publication and generation changes

The new graph stores each actual `Body` separately from its owner's
retained/queued/active phase and erased return marker. `Step.expand` requires
the registered active owner and the local executable `expand` result. It
registers all child keys and attaches every fiber and original-parent path.
The `Built` witness records computation and later transport constructors;
there is no constructor accepting `ClosedAt`, a completion memo or semantic
coverage. `Held` checks all stored child/fiber memberships and paths.

`Step.reuse` preserves the same full-key expansion owner, including an active
back-reference. It does not invent a body or acknowledge a new physical Replay
occurrence. Queue/activation and return markers are separate operations.

The graph's discharge log is computed from successful installed bodies.
`postContexts` executes the existing publication algorithm on that log;
`Step.merge` uses this computed map, rather than an unconstrained claimed
stored/post-check equality. `identity_post_context` ensures that an identity
carrier stays identity. Applying the existing `allowance_carrier_exact` with
this log gives the exact merged identity-context Allowance key.

Merge executes the earlier physical copy selection and frozen-prefix scan.
`Body.transport` maps **every** check leaf and the residual leaf. It retains
the parser result, ordered weights, boundary IDs, original registered-branch
flags, consumed decision and complete child list. `body_fibers_transport`
computes the entire carrier list. For each carrier, the previously established
formula is still

```text
unchanged physical bound: old stored fiber Context;
changed physical bound:   postContexts(previous graph)(old complete fiber key).
```

`held_merge` constructs membership and original-parent paths for all these
carriers, including a residual at a different owner, and preserves all child
paths. It composes old paths with actual copy/canonicalization edges.
`merge_invariant` preserves the constructed-body invariant under the native
representative absorption equation. Pending phases and return markers survive
unchanged; no outstanding acknowledgement is completed by this algebra.

`InstalledAt` reads `g.bodies key` directly at positive depth. Its child list
is the stored body's complete list; an unrelated favorable list cannot replace
it. A missing body remains an explicit retained/queued/active frontier. A
retained fiber is still a row obligation, and a conflict is still a diagnostic
obligation. Neither this predicate nor an erased return marker means that
native acknowledgement, diagnostics or semantic satisfaction has finished.

## 5. Application to the original Replay root

`ReplayState`, `ReplayStep` and `ReplayReachable` use the same frozen
`Replay.State`, two-quadrant computation, incoming full product and exact
dependency suppression as the preceding construction. They replace its
operand-only graph with this complete computed-body graph. One `keyOf` still
belongs to one fixed ordered pair of physical BoundKeys and exact attached
relations; other pair projections must share the same native execution.

`replay_reachable_invariant` derives origin, installed-body, freshness and
historical-root registration from empty events. Its public applications are

```text
historical_full_context:
  ReplayReachable t keyOf s ->
  operations[operation] = some batch -> batch[index] = some pair ->
  for every depth, InstalledAt t s.graph depth (keyOf pair).

dependency_skip_full_context / old_old_full_context:
  the actual suppressed pair reaches that same installed-body graph.

full_product_context:
  executing actual ordinary/incoming Replay covers every present product
  by that same construction, including the suppressed products.
```

`construct_full_context` supplies the local graph event from the computed
parser/callback result. Its premise is a finite local program result with
explicit input/resource guards; it is not a recursive coverage assumption.
This is the direct integration seam for the previously missing full Context
clause. The existing extensional `ClosedAt` is not used to recover a body.

## 6. Native constructor/consumer map

All line locators refer to the frozen source bytes in the input manifest.

| Native owner | Construction / required readback |
| --- | --- |
| `candidate_context.rs:242–266,3670–3765` | All six Context constructors, parser modes, stack order, deduplication, structural validation and residual flags. |
| `candidate_context.rs:3062–3073,3361–3372` | Kind/scoped guards and exact child-local PrefixLeft interning. |
| `candidate_context.rs:3799–3888` | Canonical processing key, scoped observation, identity, empty filters, consumed check, registered/new callbacks and discharge publication. |
| `candidate_context.rs:3898–3936` | Validated checked-boundary identity Context versus ordinary post-check residual; original-parent Derived edge and exact bound attachment. |
| `candidate_extrusion.rs:635–879,1147–1180` | Origin/physical emission/readback callbacks and all Effect placement/reflexive cases. |
| `candidate_effect.rs:730–783,1237–1305` | Recorded conflicts; indexed members, both tails, actual allowed input and local returns. |
| `candidate_context.rs:3456–3482`; `lib.rs:15214–15250` | Whole child provenance, successful relation interning/dependency recording, queue reservation and transfer. |
| `candidate_context.rs:3992–4076` | Replay stored Context composition, source union, transformer composition and exact generation/skip owners; the unchanged `keyOf` readback. |
| `candidate_context.rs:4230–4254,4318–4331`; `candidate_intrusion.rs:568–708` | Copy selection, all-prefix canonicalization, absorption, complete carrier history and native post-check lookup. |
| `lib.rs:13507–13518,14288–14420,14443–14456` | Full processing-relation/generation duplicate guard; Context then Dispatch; legal settlement cuts. |

`Availability` is raw success data for entry preparation, parser allocation,
child admission/enqueue, bound origin, physical insertion/readback, Replay,
conflict recording and final publication. `registered` is the actual selected
negative Allowance presence test. No field asserts coverage or semantic truth.
The callback data must come from the same execution; assigning arbitrary true
booleans is not native correspondence.

## 7. Exact remaining owners and falsification boundary

The first remaining native task is **CONTEXT-COMMITTED-READBACK** at
`step_typed_drain`/`candidate_context_execute_relation` and the common history
owner. Translate the successful parser iterations to `ScanRun`, derive the
local `expand` result from the actual callback returns, and align its installed
body with the same frame's completed Effect Dispatch. The graph publication
is an erased successful macro-step. Native discharge publication occurs
earlier, between Context callbacks and Dispatch. A failed or still-active
Dispatch must remain pending or be erased by the same transaction; it must
not be read back as an installed complete body.

In particular, for `discharged.contains(relation)` and `pair_is_current`, find
the **prior same full relation owner** and its constructed body/transport path
in that same committed history. The native flags alone do not prove this.
Repeated operation IDs, new Replay occurrences of an existing key, nested
rollback and generation changes must retain their actual birth identities.
At a merge, prove the actual Transport/current-none/empty-worklist settlement
cut, including earlier queued work from the same settlement loop. This is a
specific execution/control readback obligation, not a new full Context law.

Then the existing **VALUE-DISPATCH** owner must consume the exact forwarded
`ValueRequest` with all indexed Function/tuple/record/variant children and
source record adaptation. The **TERMINAL-DIAGNOSTICS/ACK** owner must eliminate
pending expansion owners and recorded conflict leaves and associate the exact
ordered acknowledgements with actual ReturnReady. Finally the
**ROW/CONTEXT-SEMANTICS and SOURCE-INFERENCE** owners must interpret the retained
fibers and directed Contexts and construct the original shared source witness.

A missing original-parent edge, omitted parser weight, nonempty filter run
with an omitted callback, changed child source/transformer, or a claimed
successful nonzero self-child directly falsifies the proposed local readback.
An actual terminal frame with a corresponding pending graph owner or unhandled
conflict falsifies the proposed accepted-history projection. None was proved
reachable for an accepted supported source here. There is no claim of compiler
unsoundness, impossibility, whole-language soundness or production readiness.

## 8. Verification

Pinned native Lake reports `5.0.0-src+eb6cafb (Lean version 4.35.0)` and Lean
reports `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Checks used
the isolated `context-expansion-r4/project`, one Lean thread, `-M1024`, no
dependencies/installations and a 120-second whole-check deadline. Sixteen
focused calls were consumed out of twenty. No root import, shared cache,
native code, test expectation, status file or Git object was changed.

Call 01 preserves the sandboxed Lake configuration-detection failure. Calls
02–08 preserve declaration, dependent-elimination and option-bind proof
repairs; call 11 preserves a record-update layout error. Calls 09–10 and
12–13 checked coherent constructive milestones. Call 14 preserves the audit
counter's missing type annotation. Call 15 passed the kernel/axiom census,
but default pretty printing abbreviated proof arguments in generated recursor
types; it was not accepted as the complete-type receipt. Call 16 enables
unabridged proof/deep-term printing and is the final complete receipt.

The final census visits **all 855 originating declarations**, including every
private/generated declaration, and records their complete types and transitive
axioms. It contains **296 theorem constants**, including all **50 named roots**
and 12 private theorem constants. Every printed block was reconciled with the
JSON inventory; no type contains a pretty-printer omission.

| Complete axiom set | Theorem constants | All declarations |
| --- | ---: | ---: |
| None | 196 | 632 |
| `propext` | 51 | 102 |
| `propext`, `Quot.sound` | 49 | 121 |

There is no `Classical.choice`, project axiom, proof hole, native-evaluation
assumption or kernel bypass in this dependency audit. The final call took
2.249 seconds; child CPU was 1.961 user + 0.232 system seconds, and maximum
observed child RSS was 1,006,124 KiB. The source search's `admit` matches name
the executable native admission projection, not a proof tactic.

The full input/source snapshots, sixteen immutable main-source snapshots,
material failed audit sources, commands/exits, all compiled-output hashes and
complete declaration inventory are retained under
`/workspace/scratch/f98087c7ac1a/context-expansion-r4`.
`manifest.json` and `freeze.json` identify the exact review bytes. The primary
owns fresh independent review, integration, original-gate status and Git.
