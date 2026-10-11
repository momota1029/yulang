# Oracle direct/provider: constructive typed-boundary adequacy attempt

Date: 2026-10-12
Status: frozen research derivation; independent review pending; M and original H OPEN
Claim class: bounded native construction derivations and a minimized operational premise
Y3 baseline: `1e33acf04be76ac420cab2014a00c4e1f1fcfa4d`
Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle read root: `/tmp/yulang2-oracle-read`
Exclusive lease: this note only; leaf, no delegation, execution or Git mutations

## 1. Frozen statement and exclusions

The assignment is the same-task premise M from the [direct/provider boundary
note](2026-10-12-oracle-direct-provider-hygiene-counterexample-proof.md) §5,
using the actual source:

```yulang
pub act tick:
    pub ping: () -> ()
my direct(cb: (() -> [tick] ())) = cb
my provider() = tick::ping()
my observed_direct() = (direct provider) ()
```

Fix a to direct's concrete annotation occurrence, sigma to its original lexical
scope, cb to its original formal binder, alpha to that annotation's SubtractId,
u to the actual direct reference in observed_direct, and alpha_u to the actual
inference scheme-instantiator image. Fix b to provider's ApplicationArgument
origin at its own ping application, p to the actual provider argument of the
inner application, and k to that same inner application's returned-provider
outer Call. Here b is an application origin, not the cb binder. All type/effect
paths and Unit/tick operands denote the resolved objects of this source.

**M:** derive the joint interpretation of b's contribution through this
provider/formal/return/outer-Call spine against a/alpha_u, including the actual
TaskSolver comparisons, selected same-task actual/consumer/ref signatures,
instances, adapters/markers, thunk force and complete output. Establish the
contribution's attachment status and complete-output membership; in the
independent case show that attachment-local consumption/exclusion cannot
license R's omission. An authentic specialization rejection is a separate
possible outcome and must come from an actual failing owner, rather than
being inferred from an undesirable inferred scheme.

Original [H](2026-10-11-oracle-global-effect-hygiene-proof.md) §1 keeps every
successfully lowered source P, every composed-negative occurrence and its
original scope/binders, every actual copy/instantiation and actual Call/output
route. Independent same-family survival, connected symbolic tails, retained
current/future checks, correlated lineage and safe publication remain required.
H's latent source Calls do not acquire a new top-level-execution requirement.
Complete Call, global soundness and required principality are separate parent
requirements. No universal quantifier is discharged by this bounded attempt.

Authority: [annotation hygiene integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–4; [contextual attachments](../design/2026-10-10-contextual-attachment-admission-design.md)
§§1,3–4,6; [complete Call contributions](../design/2026-10-07-complete-call-contribution-definition.md)
§§2–4; [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5. Complete Call retains actual returned-provider dispatch and future use,
the whole argument, callee computation and independent alternative evidence.
The selected successor carrier is not silently installed as Oracle semantics.

Dependencies: reviewed [R](2026-10-12-oracle-provider-row-replay-proof.md), the
frozen counterexample-boundary note, and the primary-supplied independently
reviewed [specialization audit](../progress/2026-10-12-oracle-direct-provider-specialization-audit.md).
Their source identities and inference result are inputs; their row/projection/
cancellation arguments are not repeated. Shared assumptions are pinned source
bytes, normal completed owner calls, successful resolved lookups and fresh
allocation without exhaustion. They do not supply a scheduled task, solved
maps, an adapter, force, independence, rejection or output.

## 2. Native task construction: what a real seed must determine

All Oracle locators below are relative to the pinned read root. Production
Specializer2 begins with empty instance and pending-instance tables
(`crates/specialize/src/specialize2/emit.rs:4–18`). Its public specialization
entry schedules only the arena's runtime roots (:47–100): an Expr root calls
`solve_root_expr`; a ComputedDef root calls `ensure_computed_def_instance`.
The latter obtains its seed from `solve_computed_def_signature` (:104–110),
which instantiates the actual installed definition scheme, compares the actual
body in both directions and resolves that same body
(`task_solver.rs:77–116`). Thus this is an authentic seed owner, not permission
to supply an independently chosen signature.

The frozen source-route proof establishes no runtime root in the literal
four-definition fragment. The primary's complementary audit also confirms
that the historical `--poly` observation constructs and prints poly, without
scheduling specialization. Applying the actual Specializer2 root loop to that
empty-root arena therefore produces no pending definition instance and no
body SolvedTask for observed_direct/direct/provider. This is a direct
initial-state/loop derivation, not an Oracle invocation and not a rejection of
the source. It leaves its latent source Calls and R unchanged.

`ensure_def_instance` retains one inference seed and computes distinct runtime
and marker surfaces from it (`emit.rs:112–157`). Its key is the definition plus
closed runtime surface; the inference seed is stored in PendingInstance rather
than reconstructed from the printed scheme. The worklist consumer calls
`solve_def_body` with that retained inference seed, records the solved task,
emits the body, then applies the marker wrapper (:166–200).

`solve_def_body` is construction-directed (`task_solver.rs:29–51`): infer the
actual body under the seed, consume it at the seed, obtain the actual
ExpressionActual and DefinitionPredicate occurrence records, enqueue their
materialized comparison, and finish. For a lambda with concrete argument Effect,
`expr_with_signature` chooses `lambda_expr_with_signature` (:298–308). The
owning lambda path binds the actual formal to the supplied four-port argument
shape and constrains its actual body against the seed's result shape
(`task_solver/control.rs:269–312`). The bare cb expression then uses that same
local binding (`task_solver.rs:428–433`). The seed matters to the actual cb
type; one cannot substitute provider's standalone displayed type here.

No source-preserving symbolic call to this seed owner has been constructed in
this packet. Naming `solve_def_body(observed, signature)` with a desired
signature would assume the selected boundary under examination. Naming the
ComputedDef path alone would assume its scheduling. Consequently the proof
does not fabricate an emitted same-task witness for this literal program.

## 3. Same-task map correlation does not certify provider preservation

There is a constructive local fact stronger than an inventory of map fields.
For any normal TaskSolver finish, fix an actual ordinary defined-reference
expression q whose recorded consumer is C. Assuming successful resolution of
C, the relevant maps are generated as follows:

```text
actual_type_of(q)   = close_resolved_runtime_surface(resolve(C), Value)
consumer_type_of(q) = close_resolved_runtime_surface(resolve(C), Value)
ref_signature(q)   = close_resolved_inference_surface(resolve(C), Value)
```

The resolver also has the documented partial-candidate fallback when C remains
undetermined. This statement does not equate the two closing operations or
assume which C the discriminator generates.

Derivation: `task_solver/finish.rs:250–272` first recognizes an actual resolved
Var whose target is `Def::Let { body: Some(..) }` (:318–329) and resolves its
consumer **as its emitted actual**, before the required-expression and generic
actual-type branches. The consumer map at :332–349 resolves that same C.
The ordinary ref-signature loop at :152–170 resolves C when present, using
the instantiated actual only when no consumer exists. The signature resolver
at :352–365 closes the inference surface; the actual/consumer resolvers close
the runtime surface. `emit_var` then passes exactly this ref signature to
`ensure_def_instance` (`emit.rs:409–421`).

Hence agreement of a solved reference's actual, consumer and selected signature
does not independently establish that the original provider contribution was
preserved: they can be readings of one consumer. This is a source-derived
correlation fact, not a claim that the discriminator receives a pure consumer
or that this policy is globally unsound. It identifies the real preservation
premise needed before using the selected maps in M.

Occurrence anchoring is also real but bounded. `materialized_occurrence`
obtains sidecar root anchors for the actual owner and role, marking a missing
record Incomplete (`task_solver.rs:142–178`). `constrain_materialized_subtype`
interns those root/position anchors and completeness with the actual comparison
(`type_graph.rs:121–145`). Those constructors authenticate comparison
provenance; they neither prove comparison validity nor supply an event-specific
attachment interpretation. No complete anchor is assumed here.

## 4. A minimized native obstruction to a rejection shortcut

A second constructive local derivation rules out the shortcut “a tick-to-pure
consumer must be rejected by TaskSolver.” Fix the actual resolved nullary tick
concrete type T. Consider one processed native comparison with empty weights:

```text
Type::EffectRow([T]) <= Type::EffectRow([]).
```

The pinned native row owner returns `Ok(())` and generates no child comparison
for this processing step. This is a counterexample to the *local assertion*
that this owner rejects every unmatched closed concrete lower. It is not an
H counterexample, actual discriminator task result, completed-program soundness
refutation or executable probe.

Derivation from the production consumer:

1. The unequal rows pass the equality shortcuts and select the Row/Row branch
   of `process_subtype` (`type_graph.rs:519–541,857–864`).
2. `constrain_effect_rows_weighted` splits both closed rows into concrete items
   with no symbolic tail (`type_graph/effect_rows.rs:5–18,274–305`).
3. With no upper item, T is placed in `lower_extra` (:19–26).
4. The only forwarding of that extra requires `Some(upper_tail)` (:37–47).
   The upper tail is None, so it emits nothing. There is no upper-extra branch.
5. The tail pair is `(None,None)`, selecting the final `Ok(())` (:59–65).

Queue activation is not assumed away: `constrain_materialized_subtype` interns
the comparison; the native interner queues a new unequal constraint
(`type_graph.rs:121–145,170–209`), and normal `finish` invokes
`solve_role_demands`, which calls `solve_constraints`
(`finish.rs:125–128`; `type_graph.rs:426–430`). The local result above concerns
the actual processing event; it does not establish that this comparison occurs
for observed_direct. Equal family payloads, attachments and alpha are not
used in this construction.

Thus neither occurrence anchors nor a successful native row comparison alone
can supply the required independent concrete-effect preservation/rejection law.
The exact discriminator's selected maps and source construction still need to
be derived. The discovery narrows the inspection to a concrete owning consumer
rather than assuming generic subtype success proves its semantic adequacy.

## 5. The stack/marker/force bridge still needs its construction history

The scheme materializer has a different operation from inference's actual
use instantiator. `types/mod.rs:147–178` freshens quantified TypeVars through
the task graph, then materializes the stored scheme. Its stack converter
(`types/materialize.rs:396–414`) copies each poly `entry.id.0` into mono
`StackWeightEntry.id`; it is not the inference alpha-to-alpha_u freshening map
consumed by R. This local code fact forbids treating their numeric IDs as an
already established same-use interpretation. It does not prove that no lawful
constructional interpretation exists.

Emit chooses adapters from the same task's actual/consumer maps
(`emit.rs:809–924,1013–1057`), with runtime closure and boundary classification.
`runtime_shape.rs:875–924` builds a FunctionAdapter when a function contract
requires it, including for equivalent function surfaces with an argument
contract. Hygiene derives concrete path/depth/guard plans from source/target
runtime shapes and that actual argument contract (`hygiene.rs:15–93`).
The runtime consumer allocates fresh GuardIds from those plans
(`mono-runtime/src/runtime/flow.rs:391–414`). Those guard allocations are not
an alpha_u equality certificate.

The actual force distinction is preserved. Applying the emitted EffectOp
returns `Thunk::Effect` (`runtime/flow.rs:29–32`). A reached
`force_thunk(Thunk::Effect)` emits a Request (`runtime/thunk.rs:117–126`), whose
path/payload are preserved while active marker plans decorate its guards
(`runtime/flow.rs:136–153`). The ForceThunk evaluator evaluates its actual
operand and reaches that force consumer (`runtime/eval.rs:43–53`). Adapters
adapt the actual argument, call their underlying function, then adapt its
actual result (`runtime/flow.rs:99–136`). In particular a Thunk-to-value result
adaptation forces the supplied thunk (`runtime/thunk.rs:28–35`).

These are source-derived conditional operational transitions. Choosing a
Thunk-to-value boundary would choose the missing selected map. Choosing the
marker guards would choose the missing plan. The absence of source Catch or
the distinct application origin b does not provide either choice, or establish
attachment independence. No event, force or output is inferred merely from
the source App or from a stored static route.

## 6. Exact remaining owner artifact and economy audit

The attempted bridge stops at the following **joint native construction
artifact**, not another R/projection/cancellation lemma:

> Starting from the same frozen poly arena and its authentic sidecar, provide
> a source-preserving symbolic invocation at the native seed owner, with its
> actual installed-scheme seed and scheduling justification. Derive the
> observed/direct/provider tasks and all actual/consumer/ref-signature maps
> they select, including the consumer-to-provider preservation premise in §3.
> Supply the constructional interpretation from a/alpha_u and b through those
> tasks to the selected marker/thunk/force history and the complete outer Call
> output. If an actual owner rejects, retain that exact rejection instead.

The seed/scheduling and selected-map owner is
`solve_computed_def_signature → ensure_def_instance → drain_pending_instances`,
with `TaskSolver::finish` and `emit_var` selecting the subsequent provider
instances. The concrete comparison owner requiring preservation evidence is
`TypeGraph::constrain_effect_rows_weighted`; §4 shows why its success is not
that evidence. The operational interpretation owners are actual annotation/
scheme materialization, argument-contract/hygiene emission and the reached
runtime adapter/force consumers. A single authenticated artifact must join
them for this source; collecting marginal maps or unrelated requests is
insufficient.

This is a localized source/consumer correspondence obligation. It adds no
source restriction, interpretation, new annotation, generalized inference
requirement or runtime-root condition to H. For the literal program, the lack
of scheduled instances is an evidence limitation; it is not the hygiene claim's
negation and does not remove latent Calls from its domain. This packet neither
establishes M nor shows M impossible. A semantic complete-Call proof need not
execute the literal program, but must independently justify its actual native
interpretation before using that interpretation as the counterexample bridge.

The previous attachment route and specialization-record route already left
this same semantic premise open. This attempt attacks actual native consumer
construction instead of renaming it: §§3–4 invalidate two specific shortcuts.
The required contribution/output guarantee is class A; preserving ordinary
higher-order inference is class B. Recovering alpha_u attachment from numeric
stack/GuardIds or coincident resolved maps is class D. The relevant phases
already know their own source/use/consumer/plan operands, but the inspected
records do not establish their required interpretation. Another abstract
transition checker or proof with a supplied pure consumer would assume it.
No third equivalent conditional proof is recommended. Classification changes
neither the parent gate nor the authoritative contract, and no new certificate
or compiler edit is adopted by this note.

One next action for the primary: obtain the exact joint seeded-task/consumer
artifact at these owners, with independent checking of the concrete-row
consumer in §4 before interpreting successful selected maps as adequacy. Any
minimal instrumentation or native owner invocation requires a new bounded
packet; none was run here.

## 7. Checks, resource use and frozen dependencies

Commands performed: bounded `rg`/`sed`/`cat` source and governing-section reads;
read-only `git rev-parse`, `git branch --show-current`, `git status --short`;
Python SHA-256 and byte comparisons against `git show` for the eight direct
Y3 dependencies and eight decisive Oracle owners. All eight Y3 dependencies
matched the assigned baseline; all eight Oracle owners matched the pinned
revision, whose HEAD was confirmed. Final narrow link/whitespace and dependency
rechecks are recorded in the submission report. Aggregate reads that truncated
were followed by narrow reads of the decisive definitions. Guessed type/scheme
paths that did not exist were replaced with the located actual owners.

No Oracle invocation, executable checker, build, test, compiler edit, Git
mutation, question-board change, child launch or shared-record write occurred.
One proof leaf; at most three lightweight read shells active in the initial
independent read batch, then sequential reads; zero heavyweight
processes, experiments and measurement samples. Shell operations were
subsecond; CPU/RSS and reasoning wall time were not instrumented. The packet
was bounded by 45 minutes. The primary supplied complementary audit findings;
they were checked against the owning source rather than accepted as a SolvedTask.

Requested routing: normal `gpt-6.1-sol` / `high` prover leaf. The live schema
lists prover; `.codex/config.toml` registers it with Sol/high defaults and
`.codex/agents/prover.toml` omits model/effort pins. Observed runtime model/effort
metadata is unavailable, hence unknown. No Astra override or hot reload is
claimed. Independent review is pending; these derivations do not self-certify.

| Direct Y3 dependency | SHA-256 |
| --- | --- |
| original H | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| reviewed R | `7cf7803bcc79ddd5ce255aa337b2bebf46e27353e07088f3ea928c6d24a77ba5` |
| counterexample boundary | `3e548eda14ec0101febdd949733dc2c1fe6ab3770d34892c9bd60668bbeef268` |
| specialization audit | `86a8e35c432018d2b38fa2e7a34b1496ea7c65db1ab0d431e3ec8dfe00af2495` |
| annotation hygiene integration | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| contextual attachment admission | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| complete Call contributions | `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e` |
| top-level inference principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |

| Decisive Oracle dependency | SHA-256 |
| --- | --- |
| `specialize2/task_solver.rs` | `cc534583e8fd154b51e8c857ef7b17df19fe68e9410fd9acb74c1d13cb1d2f66` |
| `task_solver/finish.rs` | `8ee9baf8bdac1ada4efb6f33331efab15e9f2a61674a7c492180ceac7acf0d28` |
| `type_graph/effect_rows.rs` | `845b954e5bc87e591b16cceff80eef19eb888154e52683087956b6bcf4904678` |
| `types/materialize.rs` | `8c02aa7ca9d8e0394e4f4f915086537548d2dae748f19d22d12675b502588183` |
| `types/mod.rs` | `ccf204a0f8e32eebbf8556f5b3519f7197f07d580c8231d6687b64ef2ddf4c6f` |
| `specialize2/emit.rs` | `7318b132cef4217ae089d084577fb28f3abed34a5728474ee8569e4079d71e7c` |
| `mono-runtime/runtime/thunk.rs` | `27b6d57ee711dbb7b8bb8da9ec5c05c46ad8ec7f01a29f381664ca3aa4509739` |
| `mono-runtime/runtime/flow.rs` | `83331d4d18066e8361a1ef3f89de2dffeddb7e0e2acb8e910bd5edd44dfffd40` |

Unverified scope: a discriminator SolvedTask, native seed invocation/scheduling,
selected instances/adapters/markers, reached provider force, complete output,
attachment independence, source rejection, global soundness and principality.
No full source-case census or all-program impossibility is claimed.

## Commit packet

- Exact leased path: `notes/theory/2026-10-12-oracle-typed-boundary-adequacy-proof.md`.
- Baseline SHA: `1e33acf04be76ac420cab2014a00c4e1f1fcfa4d`.
- Changed dependency hashes: none; direct Y3 and decisive Oracle bytes matched
  their pins at the pre-write comparison; final recheck belongs to submission.
- Review status: frozen unreviewed research derivation; M/H OPEN. No compiler,
  semantic, proof-status or production authority is claimed.
- Checks already run: narrow source/locator inspection, revision/byte/hash
  comparison, followed by submission whitespace/link checks; no execution/tests.
- Proposed one-line message:
  `research: derive Oracle typed boundary consumer obstruction`.
- Shared-record deltas left for the primary/curator: link the actual/ref consumer
  correlation and minimized native closed-row nonrejection derivation; retain M
  at the joint seed/selected-map/attachment/force interpretation owner and H
  OPEN. Do not record a source-qualified counterexample, rejection, impossibility
  or root-based narrowing. No shared record was edited.
