# R337 — ordinary K0 context source census

**Status:** Frozen primary source census for R337-J-REVIEW; compiler sources remain read-only.
This is the native correspondence companion to the R337 constructive proof
lane. It is not an independent review and does not close D1 until the exact
source manifest and both frozen artifacts receive fresh review.

## Scope and fixed evidence

The fixed claim is the R336 revision-4 `ValidK0` claim: one authentic,
nonrecursive definition, empty outer environment, ordinary candidate entry,
and only literal, parameter Name, annotation-free Value Lambda, Apply,
else-complete If, Group, and binding-free Block/StatementBlock. The exact
source-domain conditions and the prohibition on treating this as full A/B,
native preservation, runtime soundness, principality, or production closure
are inherited from the pinned R336 contract/note and the user's audit
(`b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`).
The audit's intended order remains K0 → G/N/M/W/Z → S0; this census supplies
only the open D1 context/metadata premise.

R337 contract SHA-256:
`0d71e3c740aa3d48667e3a9d62d15b835084a432e394fe79cc30d2b9d4cc9a3e`.
The compiler baseline and all eleven context/source owners are pinned in that
contract. I re-hashed the working sources and audit during this census; every
digest matched the contract/audit pins. No compiler/HIR/runtime file changed.

## Entry and source reachability

`CandidateInference::solve` enters `solve_mode(hir, false, false)`
(`shadow_apply.rs:1584–1586`): scoped experiment and operation-v1 are both
off. The candidate batch is collected with candidate Value/effect graphs on
and the `scoped` bit forwarded unchanged (`shadow_apply.rs:1790–1800`);
`start_candidate_graph` copies that bit to `context.scoped_enabled`
(`candidate_scheme.rs:2264–2268`). Thus ordinary K0 starts with
`scoped_enabled = false`; context vectors/maps are freshly empty and relation
scope ID zero denotes `ScopedFlow::default()` (`candidate_context.rs:915–1000,
2832–2835`). `GraphState::default()` supplies fresh effect-algebra/context
state, and `candidate_effect::State::initialize` only allocates a brand; it
does not seed a view, weight, relation, or context node
(`candidate_effect.rs:303–312`). This is an entry fact, not the lifecycle
proof by itself.

The source walk schedules only actual HIR children, then runs the admitted
actions through the ordinary candidate expression driver
(`candidate_source.rs:1204–1278, 1346–1369, 2410–2465`; `lib.rs:10637–10677`).
Under `ValidK0`, the generated facts are the R336 table: literal atom/pure
bounds; parameter Name alias and pure bounds; Lambda's function ports plus
entry/return Effect rows; Apply's function demand and invocation Effect row;
If branch/condition links; Group/block value/effect forwarding; and the
definition root Value link. There are no source effect labels or source
Allowances in that list. A Name endpoint is its registered formal row, not its
separately allocated occurrence Value component (`candidate_source.rs:1094–
1137`).

The candidate-source actions that can introduce annotation, operation, or
primitive signatures (`Ascription`, `LocalAnnotation`, `FormalAnnotation`,
`FormalEntry`, `Operation`, `Primitive`, `CatchOperation`, `Annotation`, and
`WhereClause`) are outside `ValidK0`; the same is true of `Local`, `Install`,
`Module`, `Operator`, and `FieldBoundV1` routes. The root action is an ordinary
`Link`, not `Annotation` (`candidate_source.rs:2140–2171, 2410–2465`). The
K0 assumption also excludes imports, local let generalization, additional
definitions, roles/members, and operators, so it supplies no `DefinitionUse`
or captured member graph. These are source-domain premises, not facts inferred
from `solve` returning `Ok`.

### Allowance origin census

The ordinary source-signature builder that emits an
`EffectEndpointKey::Allowance` is `candidate_signature_effect`
(`candidate_effect.rs:2143–2270`): it creates a view through
`candidate_signature_view`, then places that view at a negative effect upper.
The view's executable `closed_weight` exists only for a closed-tail source row
(`candidate_effect.rs:859–907`). Its reachable callers are
annotation/signature, operation, primitive, or formal-signature admission
(`candidate_effect.rs:1016, 1527–1528, 1996, 2102–2116, 2159–2269`); their source
actions/forms are excluded by K0. Two additional operation-specific paths are
explicit in the owner: `candidate_catch_operation_inner` emits an upper
Allowance for its operation-v1 callback row (`candidate_effect.rs:1016–1033`),
and `candidate_field_bound_v1_inner` reuses that retained view when admitting a
field bound (`candidate_effect.rs:1080–1105`). `CatchOperation` is outside
K0; `FieldBoundV1` additionally requires `operation_v1`, which ordinary
`solve` fixes to false. These paths therefore do not seed an Allowance either.

Other production occurrences are transports or consumers of an already
existing view: extrusion maps an existing Allowance (`candidate_extrusion.rs:
180–200, 350–385`); scheme reconstruction remaps an `EffectOperand::Allowance`
captured in an existing graph (`candidate_scheme.rs:4300–4320`); and context
execution can form an upper Allowance only from a context filter's retained
view (`candidate_context.rs:3830–3870`). `candidate_register_capture_bound`
can record a capture incidence only for an existing `EffectRow <: Allowance`
bound whose view has a tail (`candidate_effect.rs:675–683`; caller
`candidate_extrusion.rs:862`). The operation-v1 `FieldBoundV1` path can reuse
only its retained CatchOperation view as described above. None is a source
origin. The K0 scheme/import routes that could provide an existing captured
operand are unreachable by the restrictions above; extrusion has no source
Allowance to copy. Context execution is downstream of the context invariant
and returns before reading filters when its relation context is identity. This
distinguishes apparent endpoint constructors/consumers from an actual
reachable source of one.

Consequently, conditional on the authentic K0 source/action correspondence,
every reachable K0 Effect endpoint is an Effect row or the pure distinguished
endpoint (`EffectBottom`/`EmptyNegative`); no relation's upper is a closed
Allowance. Then `candidate_closed_allowance` returns `None` and
`candidate_context_source` returns `IDENTITY`
(`candidate_context.rs:3361–3372`). This is the key source premise for the
identity induction. The source census does not claim that the Rust preflight
alone recognizes the complete mathematical `ValidK0` judgment.

## Reachable mutation and caller inventory

The following inventory treats state/evidence retention as distinct from
semantic context creation. `ContextExpr` only represents the latter. The
production context constructors in the pinned context owner are:

| Transition | Production caller / effect | K0 preservation case |
| --- | --- | --- |
| Source seed (`candidate_context_seed[_with_formal]`) | `run_candidate_typed_drain` / `start_typed_drain`, before each admitted source or replay work item (`lib.rs:14028, 14200`) | `candidate_context_source(pair)=IDENTITY`; scoped branch is skipped because mode is false; seed uses default flow. Formal and inferred-entry receipts are passive metadata. |
| Admission (`candidate_context_admit`) | `candidate_enqueue_evidence` from ordinary bound/effect admission (`candidate_effect.rs:517`) | New source and processing-parent contexts both come from the same no-Allowance lemma; `relation()` inherits the processing flow, which is default. |
| Function ports | `candidate_step_function_dispatch` → `candidate_function_port_admit` (`lib.rs:14973`) | Reachable for Lambda/Apply. Local context is identity; inherited `post_check_context(parent)` is identity. No `Swap` is interned because the guard requires nonidentity inherited context; no `PrefixLeft` is interned because local context is identity. Default parent flow contains no demand/transformer to split. |
| Tuple/record/variant ports | corresponding candidate dispatchers in `lib.rs` → `candidate_*_port_admit` | Excluded by K0. If included in this context induction, each copies `post_check_context(parent)` and parent flow; its only local wrapper is a closed-Allowance `PrefixLeft`, ruled out by the same source premise. |
| Bound construction / attachment | `candidate_bound_origin_with_evidence` → `candidate_context_bound` (`candidate_effect.rs:520–552`); bound admission attaches relation (`candidate_context.rs:3888–3935`) | Ordinary mode takes the non-scoped branch, which routes every cause through `candidate_context_bound`; the specialized extrusion-link context constructor is used only by scoped mode. Origin source is identity. Child gets either checked-boundary identity or `post_check_context(parent)`; its scoped payload is default because scoped is disabled. Derived dependency and attachment do not mutate contexts. |
| Task transport and execution | typed-drain transport and `candidate_context_execute` (`lib.rs:14096, 14105, 14343, 14351`) | Canonical-equivalent task transport preserves post-check context and flow. Execution's identity fast path returns `Ok(false)` before filter extraction, effect admission, or discharge (`candidate_context.rs:3767–3885`). |
| Whole-Value rewrite | two extrusion/rewrite arms in `lib.rs:14487, 14754` → `candidate_context_value_rewrite` | Requires parent transformer zero; K0 parent also has no demand. Pair source is identity; child inherits default flow and gets `Derived` evidence only. |
| Equality/canonicalization transport | `candidate_intrusion.rs:693` → `candidate_context_canonicalize_bounds` (`candidate_context.rs:4230–4248`) | Witness transport and the additional derived relation inherit `post_check_context(parent)` and parent flow; both are identity/default under the induction. |
| Bound witness transport | `candidate_effect.rs:697` → `candidate_context_transport_witness_with_evidence` (`candidate_context.rs:4318–4351`) | Transports the parent's post-check identity and flow. Witness changes endpoint provenance only. |
| Replay / opposite-bound restoration | `candidate_extrusion.rs:1030–1110` → begin/step/drive replay (`candidate_context.rs:3992–4228`) | With identity lower/upper contexts it selects `IDENTITY`, avoiding `ContextExpr::Replay`; `compose_scopes(0,0)=0` and upper demand is `None`. Child dependencies, queue cursors, and restoration receipts preserve metadata but do not create a context. |
| Boundary-0 root graph capture | SCC/source schedule → `capture_candidate_graph_owned(..., boundary=0, ...)` (`candidate_scheme.rs:2872–2905, 2520–2530`) | This capture is reachable even in K0. Its bounds reference relations with identity context; `context_payloads(IDENTITY,...)` yields no weights (`candidate_scheme.rs:2678–2703`; `candidate_context.rs:1696–1726`), and default flow has no latent demand. E0 rows/pure leaves capture as rows/leaves; there is no `EffectOperand` or context view. Capture retains the graph for possible uses but does not itself invoke FreshUse. |
| Fresh/captured transport | `candidate_scheme.rs:4620–4626` → `candidate_context_fresh_transport_scoped`; roots are source relation contexts renamed at `candidate_context.rs:1540–1640` | K0 root capture is reachable, but no K0 `Module`/definition use, import, local generalization, or member use supplies the FreshUse caller. Even for an authentic graph captured under the invariant, its context map sends identity roots to identity; with scoped disabled it forcibly stores default flow. Keep arbitrary caller-supplied ContextIds outside this source-qualified case. |
| Retained/captured attachment metadata | fresh-use caller → `candidate_context_fresh_bundle`; `candidate_context_reuse_fresh_relation` validates an already-created relation | Bundle links add no context node. Reuse is read-only. `candidate_context_transport_bundle` is dead-code annotated and has no production caller; test-only compatibility transport helpers are excluded. |
| Context execution/discharge | `candidate_context_execute_relation` → `candidate_zero_word_filters` | Under identity, early return makes the discharge branch unreachable; hence `post_check_context` remains the original identity. No residual or discharge entry can bootstrap a nonidentity context. |

`candidate_context_source` is the only production origin constructor for a
`PrefixLeft`. Function port can wrap a nonidentity parent in `Swap` and can
compose a local PrefixLeft; Tuple/Record/Variant use the same PrefixLeft rule.
The replay operation is the only production path that derives a `Replay` node
from two live relation contexts; `rename_contexts_impl` can copy a Replay node
already present in a captured DAG. All these creation/copy branches are
identity branches under the two source invariants. `rename_contexts_impl`
cannot add a nonidentity node from an identity root.
No other pinned production file calls the private context interner or directly
constructs `ContextExpr` (`rg` census over all eleven pinned owners).

## Induction boundary and unresolved review checks

Jointly induct over successful source construction prefixes, not over the
finished type derivation:

1. The source-action lemma excludes closed Allowance origins and keeps ordinary
   mode false.
2. The base state plus seed/admit gives `(ScopedFlow::default(), IDENTITY)`.
3. Every bound, Function child, rewrite, canonicalization, task transport,
   and identity replay consumes an already-invariant parent; each row above
   retains default flow and identity context.
4. Identity execution is inert, so it cannot discharge a relation or create
   a residual; therefore `post_check_context` stays identity for the next
   transition.

This establishes the planned preservation shape conditional on R336's
authentic K0-to-source-action premise. The independent reviewer must challenge:
every call site in the exact source manifest; all
`candidate_signature_effect` callers and imported/captured operand creation;
the unreachability of `Action::Module`/`FreshUse` under the exact K0 source
predicate; the possible discharge/residual cases; and `rename_fresh_contexts`
on identity roots. This census and the proof handoff are frozen together for
one fresh independent review. The primary census grant was charged in full
(1,500s) at assignment; observed census wall interval from the shared R337
start at 04:24:43 UTC to this freeze was about 570s. No tests, Cargo, compiler
edits, probes, or runtime execution were used.
