# Playground Catch and effect hygiene: assurance boundary

Date: 2026-10-15
Status: independently reviewed research-only local derivations and conditional correspondence;
original source hygiene, soundness and required principality remain OPEN.
Review: fresh M2 `compiler_referee`; no findings in the bounded claims. No
Oracle execution, complete source adequacy or global soundness was certified.
Baseline: `e9790f96f154ef0ddf67cb45aa26a569148569d7`, branch `research/simple-sub-intrusion`.
Lease: this file only. Method: static constructor/consumer audit and application
of existing proofs; no compiler edits, builds, tests, probes or Oracle execution.

## 1. Frozen parent and governing inputs

For every accepted computation in the originally supported source domain, every
real request and complete Call interpretation under one shared original scoped
assignment `xi=(nu,K,D)`, preserve its original source binders, provider,
attachment, witnesses and residual lineage. An effect may disappear from the
outward computation only through its source-authorized actual handling. A handler
must not capture a protected foreign request without the applicable local grant.
Releasing scope `s` changes only that protection: membership, attribution, grants
and independent protections survive, including through capture and FreshUse.
Required ordinary inference and principality retain their separate obligations.
No witness may be chosen independently for a marginal endpoint or printed row.

This is the unchanged parent requirement, not a theorem proved below. In
particular, a conservative effect estimate is insufficient to prove value
preservation/progress, operational handler eligibility, complete Call, or principal
inference. Experimental unavailability does not narrow the parent's source domain.

Governing sections: [inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5 and §1.1; [annotation integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–5, especially §1.1; [directional decision](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
§§2–4, including §§2.1–2.2; [compose decision](../design/2026-10-15-compose-scoped-effect-release.md),
“Scope of the operation.” The retracted integration §6 output supplies no oracle.

Accepted discriminators: omitted `cb` lets `signal` escape relay and its result
initializer into the block; annotated callback/computation formals permit handling
`signal`, return `1`, accept an extra compatible `write`, and retain `write` outward.
`compose id g` releases the argument scope also through `f`'s result; an independent
scope survives. These are requirements, not new observations in this audit.

## 2. Existing results actually reused

| Existing result | Application here | Unchanged prerequisite |
| --- | --- | --- |
| [Typed-boundary package](../design/2026-10-02-typed-boundary-realization-draft.md) §6, “Transport and lifetime theorem package” | Typed profile transport composes, retains source witnesses and creates no authority. | Authentic profile, matching typed correspondence, receipt/observation and active original owner. |
| [Concrete capture corollary](../progress/2026-10-05-concrete-capture-profile-derivation.md) | A concrete contravariant contract can establish receiver-local eligibility. | Source-established profile and same-view incidence; eligibility still requires actual ordered selection and OpCompat. |
| [Protection-only filter](../progress/2026-10-05-handler-protection-filter-derivation.md) | Release changes protection queries while preserving grants and underlying incidence. | Exact full witness selected for release; sibling paths and independent witnesses retained. |
| [Scoped kernel construction](2026-10-15-compose-scoped-release-construction.md) §2 | Apply scope-specific release and injective alpha-equivariance to copied scoped flows. | One injective scope/tag map shared by all references and incoming state. |
| [Ownership/capture derivation](2026-10-15-effect-scope-ownership-capture.md) §§1–3,7 | Explicit region ownership preserves local/external distinction; Value actions remain identity; Effect replay follows lower then upper. | Correct original capture frontier, complete latent inventory and actual activation. |
| [Native residual P](2026-10-14-native-handler-residual-cut.md) §§1–3,5 | Existing headed Allowance can absorb members and forward other exact endpoints to a tail. | Authentic contribution-local U input, identity context in its stated sense, successful complete processing; least-residual claim retains its own hypotheses. |

These supply useful conditional steps. None constructs a missing source permission
or proves that a stored bound has activated. The older pure injective parent
transport result is not substituted for qualifying parent/copy equality.

## 3. Actual constructor/consumer correspondence

All code locators below refer to the baseline; paths are under `crates/yu-solver/src/`
unless prefixed otherwise. “Present” means the stated local action is constructed,
not that the full semantic premise has been established.

| Required fact / quantified objects | Actual owner and consumer | Current disposition and risk |
| --- | --- | --- |
| For each source Catch H, original scrutinee S and every arm A retain their effect input. | `candidate_source.rs:840`, Work::Finish: slot 51 emits `S <= E_H` and `E_A <= E_H`; Work::CatchArms `:732` emits packet actions; executor `:1298` calls `candidate_catch_operation`. | Present unconditional source edges; no Catch residual constructor or protected/consumable partition. Missing precision and selected ordinary handling behavior. |
| Each raw k uses declaration response B and original scrutinee value V, with outside entry/suffix effects. | `candidate_effect.rs:819`: one declaration environment pairs A/B; slots 64/65 constrain entry and full S into returned row R; paired Function uses B and V. | Present conservative full-S constraints; exact suffix and shallow runtime correspondence remain open. Full-S conservatism alone proves neither packet soundness nor value preservation. |
| Each actual annotation has original position, composed polarity, resolved atoms and retained symbolic connection. | `candidate_formal_entry_annotation` `:1169` equates the outer symbolic tail with formal entry; concrete atoms create no closed cap. `candidate_formal_effect_port:1138` and `candidate_signature_effect:1559` own nested construction. | Outer computation routing exists. Concrete negative callback ports are unavailable (`Some(_)` refusal / negative-concrete refusal), and no executable local handling grant is produced by the outer entry action. Missing required annotated inference, not evidence of unsafe capture. |
| Each omitted protected-variable source upper use qualifies its exact Function demand; lower/provider effects receive no reverse seed. | `candidate_source.rs:685` retains OmittedFormal; Apply `:963` retains source input; `candidate_context_seed:2850` consults authenticated `call.introduction`, retaining original demand, use instance, output scope and input tag. | Bounded native qualifier exists. All source aliases, returned callees and recursive instances are not covered by this experiment; full source adequacy remains open. |
| Each qualified comparison introduces actions on the actual matching Effect ports. | `candidate_function_port_admit`, `candidate_context.rs:2989`: authentic upper demand root check; AE gets StampInput, RE gets ProtectBody; Value ports get identity. Source slot 2 `:2879` gets Release(argument-scope). | Actual native introduction sites identified. Deferred qualifier/source-provider completeness is a separate premise, as is semantic event eligibility. |
| For each captured local scope/tag, one fresh use preserves nominal identity relationships and external scopes. | Source region/inventory construction `candidate_source.rs:29–260`; capture `candidate_scheme.rs:766`; preparation `:1052,:1242`; bound activation preparation `:1328`. | Shared maps, explicit owned forest and retained FreshUse exist. Correct source frontier and complete latent/future references remain semantic premises. Row genericity is separate. |
| For each original lower/upper fiber pair, activation composes its actions in route order. | `candidate_context.rs:3386` composes lower then upper; `candidate_extrusion.rs:731,:797` own restoration/replay; `begin_candidate_fresh_bound:1328` supplies mapped relation, original BoundKey, antecedent and common context_use. | Source owners exist; queue admission or retained maps do not alone establish eventual complete drain, all-history coverage or future semantic receipt. |
| For each concrete contribution delivered to a headed residual view, only authorized consumed contributions disappear. | `candidate_check_effect_operand`, `candidate_effect.rs:966`, uses resolved family membership; nonmembers forward to the same tail. `candidate_context_execute_relation:3150` executes zero-word allowance checks separately. | Executable absorption is available elsewhere; it does not inspect active scopes, operation coverage or actual selection. U-certified routing is missing for Catch. Premature whole-row use risks safety. |
| Current complete executing view determines actual handler eligibility. | Native scopes are observed by `candidate_context_execute_relation:3161`; `evaluate_observation:2506` evaluates a route transformer on empty input/protection sets. | This is an observer, not a scope-aware Catch selection/subtraction consumer. Complete Call/Receive/Observe/activity correspondence remains open. |

## 4. Local derivations at current source owners

**L1 — Catch generation retains every input effect as a lower requirement.**
For every Catch successfully processed by Work::Finish, with its actual S, E_H,
and arm effect rows E_i, the generated constraint set contains `S <= E_H` and
each `E_i <= E_H`. This follows directly from the unconditional scrutinee emit
and the loop over every arm; the presence of a value arm changes only the
slot-52 value edge. No arm-family test conditions an effect edge. These facts
are appended to source actions after formation and admitted by their executor.

Consequently, **conditional on effect-generation adequacy and sound processing
and publication of those actual constraints**, every tracked scrutinee/arm lower
is required outward at H. This is a local no-removal argument, not a theorem
that every real runtime effect was tracked or that all generated work completes.
It also explains why retaining `signal` in the omitted case cannot distinguish
genuine protection from the current direct-case overapproximation.

**L2 — successful mapped-flow preparation preserves the scoped release frame.**
Fix a captured bound with `relation=Some(parent)` visited by the preparation
loop, its valid retained flow and exact scope s, any initial state (T,U), and
one successful FreshUse with an injective inventory map rho on that complete
support, identity on external IDs. In `prepare_candidate_fresh_use:1242`, every
transformer and demand uses the same `scope_remap`; `begin_candidate_fresh_bound`
passes that prepared flow to actual mapped relation construction. Applying the
existing kernel and ownership results gives:

```text
Release_s(T,U) = (T, U minus {s})
rho(Release_s(T,U)) = Release_rho(s)(rho(T),rho(U)).
```

Thus every t != s remains protected exactly when it was before this isolated
release, after the same shared renaming. The kernel has no member/grant field;
this operation changes neither. Concrete operand reconstruction at
`candidate_scheme.rs:1115` separately copies each stored contribution's resolved
effect and origin into a fresh contribution instance, and retains member index
while remapping its view. This establishes label/origin retention for those
visited nodes, not completeness of capture or runtime event identity.

These are independently reviewed local derivations with stated source premises.
They do not establish that every semantic route is
represented, that no extra executable fiber exists, or that a handler consumes
the resulting scoped state. Experimental self-edge/provenance refusals preserve
the original parent gate and are not proposed source-language restrictions.

## 5. Earliest missing premise and decisive discriminant

For selective handling the missing source output remains: for the same original
request, source/provider fiber, annotation boundary, current receiver and shared
xi, establish its applicable protection/grant and that ordered matching actually
consumes it; route every independent/protected/unmatched same-family survivor
outside the absorbing input. `Work::CatchArms` knows resolved arm identities but
constructs packet typing, not that joint disposition. Concrete formal annotation
formation also lacks executable permission. Scopes recorded on relations do not
fill either gap. A family may contain two operations with only one handled arm;
arm-family presence therefore cannot certify guaranteed consumption.

The [existing consumption audit](../progress/2026-10-15-catch-consumption-coverage-source-audit.md)
already isolates this U premise. Re-proving P or rerunning a raw-template
reachability/family-equality checker would leave it untouched. Economy audit:
this is A/B correctness and required inference; reconstructing discarded original
boundary/provider evidence later is D debt. Retain and consume evidence at its
formation/selection owner; no new characterization layer or source restriction
is justified by this audit.

Minimal proposed executable discriminator, **not run here**: use the existing
`hygiene-direct.yu` and `hygiene-callback.yu` operation bodies, requiring the whole
result computation to be `[] int` as in the saved baseline experiment. Direct
handling should permit it; omitted callback handling should conflict. The current
full-S construction predicts conflict for both, exposing incompleteness rather
than proving protection. The outside-arm control must still conflict. For the
next permission construction, the selected computation-formal example with extra
`write` must accept its input and retain `write` outward; its currently unsupported
callback counterpart cannot be relabeled a successful hygiene check. A proposed
cut additionally needs the two-operation/one-arm same-family survivor control.
The primary's verification owner should run these through the real parser/HIR,
current native solver and actual Yulang2 oracle, preserving each tool's supported
syntax and observing the enclosing computation rather than only a final Name.

Safety risk: enabling family-only absorption before this joint evidence exists
can lose protected, unmatched or outside effects. Completeness risk today:
full-S forwarding and missing permission reject required pure handling cases.
Neither establishes a current accepted-program unsoundness counterexample.
Global value/effect soundness, operational shallow control, all-path replay,
generalization/intrusion correctness and principality remain unverified here.

## 6. Freeze and commit packet

Checks: static `rg`, bounded `sed`/`cat`, HEAD/status, scoped baseline diff and
SHA-256 snapshot; artifact whitespace, fences and relative links checked.
No executable semantic check, Oracle run, build/test, network,
Git mutation or delegation. One leaf, lightweight reads, allocated <=15 minutes;
CPU/peak RAM not measured. Requested Sol/high; observed effective model/effort
unknown (no runtime metadata). Role registration/configuration inspected; no
Astra launch or hot-reload claim. Independent review belongs to the primary.

Direct dependency SHA-256 snapshot (all match baseline; no changed dependency):

```text
f4120e2c828695bb5ca5adcc86e05cc7eb1199b6ba9e926daf4aa69e9e0804da  crates/yu-solver/src/candidate_source.rs
e634ca871e80b99b83e2fbb617edd27ba966cc3b58cab647141a063866114733  crates/yu-solver/src/candidate_effect.rs
72bdca0b4e81d587966e695bfaacef31fcc9c91e5fe67e94c9538b066fb79a86  crates/yu-solver/src/candidate_context.rs
c2d043f455434625db2338f5b98161c9d83b9e3769ae98b37af7d997fddc5ade  crates/yu-solver/src/candidate_scheme.rs
9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a  crates/yu-solver/src/candidate_scope.rs
a5564766c4b257f1bf51089a603e9bb23930c95f17047b0ab892fd3edd39c3db  tools/inference-playground/src/lib.rs
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
4a98b5136a9d0d1bdddf135727c5e8779b579bf3c0b76d0524d01c951df34fd4  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
f11c6594e43c29fbfdbca1638b5c548cecc12a5beb192cac743e60f022c1cc73  notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md
fd56f819f9b33adc5d75cbfdae378c90903e4aa3a266fc053c05dda315d40679  notes/design/2026-10-15-compose-scoped-effect-release.md
44d69d6506f14c1658d7670ef68c46348d1315ce98ff1d2677f68993c5e00ea6  notes/theory/2026-10-15-effect-scope-ownership-capture.md
773a1ed4c2ebe7503438c57a06acd23e03fbc1fd0d6ae30260848c4430fe676e  notes/theory/2026-10-15-compose-scoped-release-construction.md
469677cc50b1dfd5327fa330e85bb83124c9e17cec391866dbf71ee23c40d50b  notes/theory/2026-10-14-native-handler-residual-cut.md
82402427727102e9afdf3065da4f6b6e2e836b4571b1355ece088dbda36f1cc1  notes/progress/2026-10-05-handler-protection-filter-derivation.md
a7ef12555b688e0e7f22c1c9d8936ab952282da08896f49646cfe78c0afbfc79  notes/progress/2026-10-05-concrete-capture-profile-derivation.md
```

Exact leased path: `notes/theory/2026-10-15-playground-hygiene-soundness-audit.md`.
Baseline SHA: `e9790f96f154ef0ddf67cb45aa26a569148569d7`.
Review: fresh independent `compiler_referee`, no findings in this bounded
constructor correspondence; no parent closure or production certification.
Proposed checkpoint: `research: audit playground Catch hygiene assurance boundary`.
Shared-record deltas for primary/curator: link L1/L2 as bounded conditional
correspondence; retain source U, concrete permission, runtime eligibility,
soundness/principality and production OPEN. No shared records edited.
One next action: assign the authentic Catch/annotation formation and consuming
input partition to its existing owner, with the same-family survivor discriminant
and fresh independent review before enabling subtraction. Writes stop at handoff.
