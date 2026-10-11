# Oracle direct/provider: source route, origins and the counterexample boundary

Date: 2026-10-12
Status: frozen bounded characterization; counterexample not established; independent review pending
Claim class: source-construction lemmas plus a precise operational attachment obstruction
Assigned R baseline: `148db454b6417890572a577ce4ea1c9618b59b52`
Observed Y3 follow-on snapshot: `e52400a52bf490d8fb8ec1cc1bc03e8b008c1801`
Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle read root: `/tmp/yulang2-oracle-read`
Exclusive lease: this file; leaf, no delegation, Git mutations or Oracle execution

## 1. Frozen target and hypotheses

The target is to decide whether the same fragment from reviewed
[R](2026-10-12-oracle-provider-row-replay-proof.md) supplies a counterexample
to original [H](2026-10-11-oracle-global-effect-hygiene-proof.md) §1:

```yulang
pub act tick:
    pub ping: () -> ()
my direct(cb: (() -> [tick] ())) = cb
my provider() = tick::ping()
my observed_direct() = (direct provider) ()
```

A counterexample must join these facts for the *same* source route: accepted
source; actual cb/provider value flow through direct's return; an outer Call
whose complete output contains the provider's ping contribution; authentic
classification of that contribution against the original annotation
attachment and its fresh-use image; and the inferred output omission proved
by R. The provider, occurrence, scope, binder, use and output cannot be chosen
independently. This note establishes the source/inference route, larger-source
isolation and distinct raw source origins. It does not establish the last
operational attachment/output join, and therefore does not assert a counterexample.

Governing sources are [hygiene integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–2, [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5, and original H §1. H continues to quantify all successfully lowered
Oracle programs and composed-negative occurrences, their original lexical
scopes/binders, actual copies/instantiations and actual Call/output routes.
Its independent same-family survival, connected-tail, retained-check and
safe-publication conclusions are unchanged. In particular, this note adds
no requirement that every latent function body be invoked as a top-level
runtime root. Runtime soundness and complete Call adequacy remain distinct
parent obligations, as H's own statement specifies.

Static hypotheses are the pinned source bytes, successful source resolution,
fresh allocation without exhaustion, and R's normal completed inference/query
conditions. Historical acceptance evidence is exactly the frozen
[larger-source probe](../progress/2026-10-11-oracle-callback-reuse-projection-probe.md):
its specified binary/hash and command exited zero, with no diagnostic, and
printed provider `[tick]` and observed_direct pure. That is existing
lowering/inference evidence; it is not a runtime invocation, emitted mono
program, Request trace, or attachment certificate. No new execution is assumed.

## 2. The actual source value and Call route

Oracle paths below are relative to `crates/infer/src/` unless otherwise given.
The identities here are source DefId/RefId/ExprId owners; they are not inferred
from identical type coordinates or display names.

### 2.1 direct returns its exact formal reference in poly

`lowering/expr/lambda.rs:665–735` lowers the actual cb formal. Its variable
pattern creates one Arg DefId and records it in the local binding
(`lowering/pattern.rs:221–280`). In the body, lexical lookup selects that
same local binding before global lookup (`lowering/name_ref.rs:65–74`).
`lower_local_name` at :142–169 resolves the body RefId directly to local.def
and emits `Expr::Var(reference)`. It does not select a global provider,
instantiate a different callback, or emit a source application.

The named skeleton substitution at `lambda.rs:797–808` changes the inferred
Value/Effect coordinates, but retains `body.expr`. The wrapper at :954–975
constructs `Expr::Lambda(param.pat, body.expr)`. The public connection at
`lowering/expr/mod.rs:309–341` is a subtype edge, not a replacement of the
source body. Thus direct's poly expression is exactly a lambda whose body
references its own formal Arg. This is a producer-level identity lemma.

### 2.2 observed_direct contains the actual nested applications

Global lexical lookup for direct/provider creates actual global RefUses with
the selected target DefIds (`lowering/name_ref.rs:83–115`). Each source
application at `lowering/expr/tail.rs:630–679` obtains its own source boundary
and calls the complete application constructor at :535–628. That constructor
emits `Expr::App(callee.expr, arg.expr)` and the four-port Function demand;
it forwards this call's Effect and callee evaluation Effect to its output.
The parenthesized result remains the callee of the next application.
Therefore observed's body is the actual poly tree

```text
App(App(Var(ref_direct), Var(ref_provider)), Lit(Unit))
```

with both references resolving to the selected ordinary declarations above.
Its outer callee is the result of *that same* inner App. R establishes native
admission and replay activation of both actual Function demands, together
with the pure result-Effect export. This source/inference Call-output route
already belongs to H's source domain; a top-level invocation is not needed
to authenticate the nested source applications or their inferred output.

This conclusion does not equate a poly reference with a raw runtime Closure
object. The actual emitted runtime path can contain adapters and thunk
boundaries (§5). The precise proven identity is the source formal/ref/result
spine, including its actual global provider argument and outer result use.

## 3. Larger-source isolation and accepted-source correspondence

The frozen successful dump includes extra through/route and observed functions.
Their omission cannot simply be assumed harmless. The complete value-reference
dependency census for that source is:

| Definition | Outgoing global value targets |
| --- | --- |
| ping | none; signature declaration |
| direct | none; cb is local |
| through | none; cb/x are local |
| route | none; cb and both identity binders are local |
| provider | ping |
| observed_direct | direct, provider |
| observed_through | through, provider |
| observed_route | route, provider |

The lambda/operation names in this census are resolved by the actual
local-before-global name owner (§2), not inferred as ordinary global use
edges because their spelling resembles a definition. No definition refers
to its internal self. The effect name in an annotation is a resolved type
declaration operand, not a global Value RefUse to provider/direct.

The graph is acyclic. `scc.rs:266–313,328–356` settles each completed component,
emits QuantifyComponent, then emits InstantiateUse for its incoming use edges.
`analysis/session/selection.rs:1041–1117` consumes that order; ordinary global
reference constructors do not directly connect the original target root.
Consequently neither extra observed function adds an open-use constraint
to the original provider, and through/route add none to the original direct.
They use installed schemes. Consistent per-use freshening is owned by
`instantiate.rs:732–748`, so extra uses do not share direct-use x_u/α_u merely
because they instantiate the same original quantifiers. Direct/through/route
also start with separate method annotation/closed-row maps
(`lowering/expr/method_body.rs:55–87`).

All global targets and nominal effect declarations used by the R slice are
unchanged in the larger source. The only additional edges involving that
slice are the two incoming provider uses just enumerated. Therefore R's
ordinary direct/provider installed shapes and observed_direct's native use
component occur in the larger source up to fresh-ID renaming. This is a
source/SCC isolation proof for the displayed finite graph, not a general
claim that arbitrary omitted declarations cannot affect inference.

The larger-source acceptance record and R's static output result are thus
consistent witnesses for this same source/inference route. The dump does not
authenticate numeric records or imply successful specialization/runtime
publication. That distinction does not retract the accepted inference route.

## 4. Authentic raw origins, and what they do not classify

The annotation and ping operation are not one source occurrence.
`lambda.rs:1270–1281` selects AnnConstraintLowerer for direct's actual formal
annotation. `annotation/constraints.rs:54–79` allocates its Annotation source
boundary/origin a. `constraints/machine/entry.rs:433–450` appends new source
boundary and origin records; two allocations in the same session are distinct
under the fresh-allocation hypothesis. `annotation/constraints.rs:134–144`
uses a for the paired annotation connection. The concrete atom-set constructor
at :657–690 allocates α and its tick grant; :593–600 declares its stack fact.
The ordinary copy uses the actual α→α_u map established by R's dependency.

Provider's ping reference resolves to the operation DefId and records its
actual operation path (`lowering/expr/block_local.rs:1029–1063`). Its positive
operation Effect is a concrete Row, with no α (`lowering/signature_effect.rs:78–107`).
The early operation-signature hook uses **UnknownInternal**, a shared origin
constant; that constant is not a unique request/event identity and must not
be cited as authentic independent attachment evidence.

Provider's actual `tick::ping()` source App separately allocates boundary/origin
b of kind ApplicationArgument (`tail.rs:630–679`). Its complete Function
demand carries b and derives the operation's return-Effect comparison. Thus
b ≠ a. The two Apps in observed allocate still other boundaries, and their
parent DefId is observed, not direct. The provider application syntax, its
source span when span recording is enabled, its parent definition, and its
operation target are all distinct from the cb annotation constructor.
No annotation constructor executes ping, and no ping constructor allocates
direct's α. These are source-origin and construction-lineage facts.

They do **not** decide the attachment predicate required by H. A provider
contribution can have a distinct origin and nevertheless be attached to a
receiving callback contract for a particular invocation. Distinct raw source
origin is therefore insufficient to prove that its eventual outer output
event is independent of α_u on the exact complete Call route. Nominal tick
equality and absence of a provider-local α are also insufficient.

The governing integration explicitly reuses attachment separation conditional
on supplied owner/profile/attachment derivations; it does not produce that
raw bridge. The existing [attached-subtraction probe](../progress/2026-10-05-effect-attachment-subtraction-playground.md)
likewise separates source contribution, attachment and complete-output
reachability, and states that its flags are assumed. The successor's selected
contextual carrier cannot be silently installed as Oracle semantics or used
as an authenticated Oracle attachment record.

## 5. Actual operational owners and the first missing join

Production `specialize::specialize` delegates to Specializer2
(`crates/specialize/src/lib.rs:68–78`), not to the legacy Specializer helpers.
Its `specialize2/emit.rs:112–195` selects an inference/runtime/marker signature,
solves the actual definition body using TaskSolver and the provenance sidecar,
emits it, and applies the marker wrapper. TaskSolver's body entry is
`specialize2/task_solver.rs:29–51`; its actual/consumer/ref signatures are
resolved by `task_solver/finish.rs:131–180`. These are additional native
constructors/consumers; R's inference scheme is not itself a SolvedTask.

For the same source spine, `emit.rs:246–278,377–421` selects Local for cb,
EffectOp for ping and actual specialized InstanceRefs for direct/provider.
It preserves the two Apply constructors but subjects arguments and expressions
to actual/consumer boundaries. `emit_lambda_body` at :723–746 also adapts
the body to its inferred return. `emit.rs:809–924,1013–1057` and
`runtime_shape.rs:875–924` can emit FunctionAdapter, MakeThunk or ForceThunk;
unsupported boundaries can return UnsatisfiedSubtype. The actual path
depends on that same SolvedTask's types/ref signatures and authenticated
occurrence provenance, not solely on the source App tree.

The pinned mono-runtime provides the decisive operational distinction:

- `runtime/eval.rs:84–96` evaluates Apply and calls apply_value;
  :121–128 constructs a Closure, and :12–19 reads its actual local value.
- `runtime/bind.rs:86–90` binds that actual argument value to the formal;
  `runtime/flow.rs:74–84` runs the body in that environment.
- Adapters retain the underlying function but adapt both argument and return
  and install marker plans (`runtime/flow.rs:99–136`). They cannot simply be
  omitted when asserting exact runtime-value or activation identity.
- `runtime/flow.rs:29–32` applying EffectOp constructs `Thunk::Effect`.
  It does **not** yet emit a Request. `runtime/thunk.rs:117–126` emits the
  request only on force, using `runtime/flow.rs:136–153`.
- Source Catch is the handler constructor; ordinary marker frames carry
  boundary/visibility information. If a tick request reaches the root with
  no matching handler/host, `runtime/engine.rs:46–64` reports UnhandledEffect;
  `root_effect.rs:3–16` has no default handler for this tick path.

This source slice has no source Catch. That establishes the absence of a
source handler, but it does not establish request execution: the actual
specialized adaptation/force route remains necessary. In particular, neither
the formula “Apply provider” nor raw origin b alone proves “ping Request
executes with no handler.” Assuming the force transition would assume the
consumer being audited.

**First unproved H join M:** for the exact provider contribution originating
at b and transported through the actual formal/ref/return/outer-App spine,
establish its attachment status against a/α_u and its membership in the
complete output of that outer Call (including its actual adaptations and
force). In the independent case, prove there is no valid attachment-local
consumption/exclusion that licenses R's omission. The source owners are
TaskSolver's materialized occurrence/provenance entry
(`task_solver.rs:142–178`), its same-task actual/consumer/ref-signature solve,
and the emit/adaptation/force owners above. The minimum useful evidence is
that joined source-to-attachment/output lemma or an authenticated same-task
record which supplies those relationships—not independently selected event,
tail or marginal provider witnesses.

No theorem or record read here establishes M. This is the stop boundary.
The exact source route qualifies for H; M is an unresolved correspondence
within that route, not an exclusion of latent bodies from H's quantifiers.

Proof-obligation economy audit: H's independent-contribution/output guarantee
is a class-A correctness obligation, not an optional stronger characterization.
Recovering attachment merely from family support or unequal origins would be
reconstruction debt: the source formal/application constructors know the value
flow, while TaskSolver/emit know the actual typed adaptation and force path.
This lane inspected those owning constructions instead of repeating R's row
or cancellation derivation. They retain useful source/provenance and solved
boundary records, but no inspected result connects them to M's event-specific
attachment/complete-output predicate. No proof-only relation, new annotation,
source restriction or compiler certificate is adopted here. Before another
equivalent attachment argument, the primary should inspect or obtain that
exact existing native correspondence/evidence at these owners. Classification
does not discharge M or alter the original A/B gate.

## 6. Three observations kept distinct

1. **Source/inference Call and output:** established in §§2–3; R gives its
   inferred pure result. This route qualifies for H's source scope.
2. **Executing the literal dump program:** there is no top-level invocation
   of observed_direct. The lambda wrapper returns Computation::value
   (`lambda.rs:954–975`; `typing.rs:42–44`); BindingFetch is FetchValue
   (`typing.rs:79–94`), so `lowering/body/methods.rs:390–398` publishes no
   ComputedDef root. `body/mod.rs:2136–2141` publishes expression roots, and
   this source contains none. Specializer2 consumes runtime_roots
   (`emit.rs:47–87`). Hence the supplied dump is not a Request trace.
   This is **not** the H obstruction and imposes no new execution premise on H.
3. **Operational adequacy/soundness:** still unproved. A symbolic invocation
   of the exported observed function requires the same native specialization,
   adaptation and force join in §5. Adding a top-level invocation would be a
   new source execution experiment, which this lane is not authorized to run.

Thus R plus accepted larger-source inference is a source-qualified candidate
effect loss, not yet an H counterexample. The literal-program execution
premise is absent; the latent source Call remains valid; M remains the precise
attachment/complete-output premise needed for the counterexample conclusion.
Neither H nor its negation is established here.

## 7. Checks, dependency fingerprints and commit packet

Static checks: read governing sections, original H §1, reviewed R, larger
source/dump and the listed construction/consumer owners; confirmed pinned
Oracle HEAD; checked dependency hashes and local Markdown links/whitespace.
No Oracle invocation, build/test, executable model, compiler edit, Git mutation
or shared-record update. One leaf, no jobs spawned. Sol/high requested;
observed model/effort metadata unavailable (unknown). Budget: bounded 35-minute
static attempt; no measurement/execution budget consumed. Independent review
is pending; this producer does not promote its own result.

| Dependency | SHA-256 |
| --- | --- |
| reviewed R | `7cf7803bcc79ddd5ce255aa337b2bebf46e27353e07088f3ea928c6d24a77ba5` |
| direct-use discharge | `b9b2552ff6a681b04eab443a251e500138586a727e83b6ca542f1fd74ed74c80` |
| original H | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| larger-source probe | `975c2f7460ca5a9663938485cc2ce8669160b864c19928151589c9904016ccd2` |
| hygiene integration | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| top-level principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |

Changed path: `notes/theory/2026-10-12-oracle-direct-provider-hygiene-counterexample-proof.md`.
R itself was not edited. No dependency hash changed during this lane.
Checkpoint baseline is the observed Y3 snapshot above, consuming reviewed R
from the primary's assigned baseline. Proposed message:
`research: trace Oracle direct/provider counterexample attachment boundary`.
Shared-record delta left to primary/curator: add the source-route identity,
larger-source isolation and raw-origin distinction; retain original H OPEN
with M at the actual source-to-attachment/complete-output owner. Do not
record a counterexample or use missing top-level runtime execution to narrow H.
Next action: assign that precise joined native specialization/attachment/output
premise, using the same source owners and avoiding another R/cancellation scan.
