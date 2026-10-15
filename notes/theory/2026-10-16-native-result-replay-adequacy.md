# Native first Result: executable replay and the remaining satisfaction premise

Status: independently reviewed research; direct bounded operational lemmas and a localized
missing semantic premise. FIRST-RESULT ADEQUACY, B, complete Call, hygiene,
soundness and principality remain OPEN. No source counterexample established.
Baseline supplied by primary: `d40452204`; native sources unchanged from
`0a9af0da5080469f930da0032aa96d7d89d358c5` by the primary's baseline assertion
and the matching source hashes below. Sole output lease: this file.

Independent review: `ordinary_carrier_semantic` found no findings at SHA-256
`75c4f8d923b95b55b27e849aa32c2fb37ed7db854b18e97712a945146ba95c52`.
Closure is limited to production Value nondischarge, Result-context inheritance
and the actual ordered Replay activation route. No general composition of
concrete comparison successes, complete activation, common source/native model
or parent adequacy follows. The primary assigned the remaining generation
interpretation at slots 43/44 and Apply slot 0 to a normal Sol proof lane.

## 1. Frozen objective and authority

Keep the original `receive(f: () -> 'a) { my g = f(); g() }`, definition d,
formal f, annotation a, scope S, shared alpha, beta_f, and uses u1/u2 from
the [source interpretation](2026-10-15-native-call-result-source-interpretation.md)
§1. For **every original xi=(nu,K,D)** and **every original returning complete
Call witness z at u1**, retain that same z's returned W_z and matching
callee-result view F_R,z. Neither input may choose a different provider,
assignment, return binder, pending Bind suffix, or dependent challenge.
The target remains the two-input tagged image

```text
Result(u1,xi,z) = M_W* W_z union_tagged M_res* F_R,z,
M_res(Result.q,q) at matching existing typed paths.
```

K, predicate identities, original scopes and inherited lineage remain shared.
Immediate ResultEffect is not a latent Result path. Retained copying,
canonicalization and subsequent local use must not silently change these
binders. The scoped collector's Local-callee rejection does not restrict this
source quantifier. This pass asks whether actual Replay/post-check operations
already give the missing source/native commuting square.

Governing sections: typed-boundary realization §6, **One relational transport
operation**; typed computation core §6 Application/Binding/Name; callback
context delivery §§2,2.1,4; inference top-level principles §§1–4, including
§1.1's source generation and accumulation clarification. Operational method
and limits follow agent-orchestration **Model routing and Astra escalation**
and **Proof delegation and decomposition**, compiler-engineering **Natural
compiler behavior and proof-obligation economy**, research-lab **Evidence
quality and stopping unproductive loops**, and git-concurrency **Disjoint-file
mode**. No new semantic decision is proposed.

The reviewed source interpretation supplies origin decoding and coordinate
correspondence, expressly not a native constraint-model valuation. The reviewed
falsification note establishes no source-qualified loss. Their initially
supplied hashes changed through primary-only review metadata; the primary
explicitly confirmed both review-metadata and later integration-metadata
updates (integrated at `f75299ea4`), with mathematical content unchanged.
The final stable hashes are listed below. This pass
uses neither note's unresolved semantic bridge as an assumption.

## 2. Direct operational result: a Function parent is not discharged

**Claim class: bounded operational lemma, constructed here; review pending.**
For an authentic live `RelationId p` whose retained `RelationKey.pair` is
Value, `post_check_context(p) = relations[p].key.context`. In particular this
holds for the actual positive/negative Function comparison that admits the
first Result child. Scope: states constructed by the inspected production
context methods, not arbitrary fabricated test state.

Proof by inspection of the complete mutation owner:

1. `relation_with_scoped`, `candidate_context.rs:2570–2602`, interns a key
   containing the typed pair and does not mutate that pair in place. Effect
   and Value pairs cannot share this key. Transport constructs another
   relation when the pair changes.
2. The only insertion into `discharged` is
   `candidate_context_execute_relation`, line 3283. With identity context it
   returns at 3227. With no filters it returns at 3231. With filters it matches
   `LiveConstraintTask::Effect` at 3232–3235; Value returns an error before
   discharge insertion. Its preceding assertion ties the task to the retained
   relation pair. Thus that insertion cannot target a Value relation.
3. State initialization has no discharged entries; rollback at 1840–1843
   removes discharge entries and their residuals. It does not create a Value
   discharge. In a valid retained state this preserves the invariant, including
   relation-ID reuse after rollback.
4. `post_check_context`, 2799–2804, selects a residual only for a member of
   `discharged`. The Value case therefore selects the original context.

Consequently `candidate_function_port_admit`, 3020–3063, gives Result the
parent's original context, prefixed by an authentic child-local weight when
one exists. Result uses Preserve; it does not perform Swap. The scoped demand
is consumed with transformer zero for Result, separately from AE/RE. This
proves a real post-check preservation fact; it does **not** identify that
context with the entire source packet. A context may already have been
constructed from other parents, and those constructors still need semantic
interpretation. Value contexts containing unsupported filters may fail;
this lemma does not prove all original source histories avoid that failure.

## 3. What Replay actually activates

`candidate_replay_bound`, `candidate_extrusion.rs:799–842`, reads the live
canonical owner and each opposite bound. Regardless of insertion polarity,
it orders the inputs lower then upper and forms the actual endpoint task
`lower <: upper`. It calls `candidate_context_begin_replay` and then drives
the resulting operation. These are actual consumers, not retained-only edges.

At `candidate_context.rs:3408–3469`, let L,U be the current lower/upper
bound-relation lists and L0,U0 their saved old suffixes. The two loops visit

```text
(L \ L0) × U    and    L0 × (U \ U0).
```

The quadrants are disjoint. This establishes enumeration of the newly paired
**retained relations** for the captured heads, assuming those old cursors
denote suffixes as maintained by append-only bound registration and the saved
progress record. An incoming FreshUse sets the old cursors to None and visits
the full product. Ordinary replay can skip a dependency already present;
this is not a proof that a previously failed or suspended operation completed.

For each visited pair the constructor reads both original contexts, forms
`Replay(lower_context,upper_context)` unless both are identity, unions checking
source references, composes scoped transformers, and retains the upper demand.
It records the exact ordered parents and BoundKeys in `Dependency::Replay`.
It does **not** compare providers or evaluate a source-fiber join. The product
is required ordinary propagation, not itself a counterexample to jointness.

Activation is explicit: `replay_operation_queue_next` (2041–2046) packages the
stored task with that child RelationId and its acknowledgement;
`candidate_context_consume_replay_child` (3547–3589) enqueues it or runs the
provenance-aware drain. `candidate_context_drive_replay` (3598–3609) distinguishes
Queued from Complete. The live drain at `lib.rs:12120–12161` transports that
relation, executes its context, then dispatches the task. Function dispatch
at 12590–12618 constructs field 3's covariant Value inequality; admission
retains its parent and `FunctionPort(Result,Preserve)`.

These establish the local emitted task and its real activation route.
They do not prove termination, fairness across arbitrary future mutations,
success of every drain, or complete replay after every recovery history.
In particular, storing a progress head or receiving Queued is not Complete.

## 4. Copying and merging do not supply the missing semantics

The original Apply recipe at `candidate_source.rs:978–1020` and native demand
at `shadow_apply.rs:1548–1625` identify the result component in Function field
3. Actual extrusion rebuilds the four fields in order and retains parent/copy
records (`candidate_extrusion.rs:93–128,220–255,343–370`); the reviewed input
establishes their coordinate correspondence.

Relation interning can identify children with the same complete key. However,
`dependency` at `candidate_context.rs:2660–2718` deduplicates the **whole
dependency**, including ordered parents, separately from relation interning.
Different Replay or FunctionPort derivations therefore need not disappear
when their child relation is shared. `union_sources` is a checking-source
set union, not a union of typed packet aliases.

Canonicalization at 3613–3630 transports each changed bound key, preserves
the post-check context and source association, and retains its derivation.
FreshUse at 3660–3675 retains source BoundKey, target BoundKey, parent relation
and use identity. Local installation stores the initializer's actual root
(`candidate_scheme.rs:1429–1448`); the Name publication barrier at 1616–1637
restores captured bounds before admitting its fresh root. These owners provide
specific maps on which a semantic invariant can be checked. They do not make
row equality a source-provider equality. No claim here establishes semantic
preservation for all copied contexts or generalization histories.

## 5. The absent premise is satisfaction, not runtime packet evaluation

There are two distinct meanings of evaluator here:

- The live `candidate_context_execute_relation` consumes zero-word effect
  filters. It registers/replays actual Allowance bounds and records residuals
  (3190–3289). It does not evaluate complete source Calls.
- `evaluate_context` (1684–1730) folds a context into `DetachedWeight`:
  ordered words, filters and pops. All discovered callers are in
  `candidate_context_tests.rs`. Its arguments and result carry no original
  z, source typed-view packet, or shared K,D valuation. The nearby
  `retained_input` closure is a certificate inventory, not a source evaluator.

Neither absence implies that inference must execute the source program or
materialize packets. Native inference may remain constraint generation,
accumulation and propagation. A denotational simulation is sufficient, but
the source-indexed annotation alone is not that simulation.

The precise first missing premise is the following **single common-model
extension**, at the generation owners rather than at a detached fold:

> Given the original source environment/xi and its complete Call witness z,
> construct one interpretation of the actual generated native Value/Effect
> variables and typed occurrence views which interprets the original formal
> annotation admissions and this Apply's actual callee/demand admission as
> predicates in that same environment, proving their satisfaction when their
> original source obligations hold and retaining unresolved obligations;
> at the shared result origin it represents W_z and F_R,z by the two tagged
> images, and its meaning of native context/Allowance checks agrees with the
> existing source typed-boundary predicates under the same K,nu,D. Extend it
> along actual parent/copy and fresh-use maps without selecting new source
> witnesses or equating distinct views merely because rows are equal.

This is not assumed by §§2–4. It requires a satisfaction interpretation of
generated constraints and agreement with their consumers, not merely assigning
the source answer to a native occurrence. It must not demand that every
original xi solve every accumulated constraint: unresolved source obligations
remain predicates under that xi. The original pointwise representation claim
still covers every original xi,z; no new source-validity restriction is adopted.

Why ordinary replay helps, but does not finish this premise: in a *single*
native interpretation, satisfaction of `L <: a` and `a <: U` gives `L <: U`
by transitivity of the chosen native subtype relation. One shared assignment
preserves correlation; no independent marginal choice is needed. This is a
conditional algebraic step, not yet a proof about packet-valued contexts.
The common interpretation, its context semantics and the source introduction
cases are exactly what have not been constructed. Choosing separate models
for the two parents and combining them is invalid. Likewise, assigning the
desired tagged image to every Replay child without checking the actual
Effect/Allowance consumers merely repeats the previous forward annotation.

The existing source relation supplies the required z and both packet inlets;
it can serve as the semantic environment of this extension without changing
source meaning. The existing native relation retains enough indices for the
reviewed coordinate interpretation. Neither fact alone proves the extension
exists or is preserved. No contradiction establishes that a new storage
mechanism is needed. The result of this bounded pass is therefore an exact
unavoidable premise for this proof route, **not** an impossibility theorem
about the native compiler or a justification to add a packet evaluator.

## 6. Economy audit and one next owner action

The ownership audit and source decoder reached this same semantic premise by
different routes. This pass removes a narrower concern through the direct
Value post-check lemma and establishes the actual replay activation route.
It stops before a fourth interpretation-only variant. The remaining premise
is A/B because it connects original source result meaning to accepted native
constraints and their consumers. It is not optional converse completeness.
No discarded packet/profile fact has been demonstrated, so D-style registry
or per-result evidence redesign is not justified by this evidence.

**Next action for the primary:** assign one normal Sol constructive packet to
the *source constraint-generation owner*, with the exact common-model
extension above as its conclusion. Start with actual formal slot 43/44
(`candidate_effect.rs:1185–1224`) and Apply slot 0
(`shadow_apply.rs:1548–1625`), using the original complete Call relation as the
shared semantic environment. Require a native satisfaction judgment for those
actual constraints, including unknown annotation rows; then derive replay
transitivity and Function Result projection in that same model. At the first
effect predicate reached, check the real Allowance consumer
(`candidate_context.rs:3236–3273`, `candidate_extrusion.rs:876`, and
`candidate_effect.rs:967–1030`), rather than
declaring context interpretation by definition. Any copied endpoint must use
its actual retained map. Success is a derivation of that base and its local
preservation; a failure must identify a concrete generated atom whose source
entailment fails or an exact undefined semantic constructor. Stop at that
atom. Do not repeat origin decoding, add a synthetic packet evaluator, require
solving at generation, or remove the scoped Local-callee guard.

This is a ready proof task at an actual constructor/consumer seam. If it
exposes a genuinely missing compiler operation, return that exact operation
for primary design adjudication and a bounded implementation packet; the
present note does not authorize production changes. No new probe is proposed
as a substitute for the universal source satisfaction argument.

## 7. Checks, resource use and freeze

Method: one bounded static constructive pass, actual source/call-site reads,
mutation-owner search and dependency hashes. No tests, builds, executable
probes, Git commands, external requests or delegates. At most one lightweight
shell process ran at a time; zero heavy processes. Allocated wall budget:
approximately 15 minutes; CPU/RAM and exact elapsed wall time uninstrumented.
No performance samples. Only the leased file was written.

Requested route, confirmed by primary: `gpt-6-astra` / `low`, exceptional proof
leaf, one decision point after the localized Sol routes.
`.codex/agents/prover.toml` has no model/effort pins;
`.codex/config.toml` registers it and defaults ordinary leaves to Sol/high.
Observed effective model/effort metadata: unknown. The leaf does not certify
that an override ran. No further escalation or delegation occurred.

Frozen dependencies (SHA-256):

```text
593d424e5db01f58f171983e6d8a4551381e54455b19dbb6469e13993e860390  notes/theory/2026-10-15-native-call-result-source-interpretation.md
677de269229fb818aebbf8df9f76ebcfc646612904ec0b6c1c10f8af6211f68f  notes/theory/2026-10-16-native-result-origin-falsification.md
9e3cf4d00f50a897d00cb211d8bca3517551f33d4274bef556cefd96c9c2ff82  notes/progress/2026-10-15-native-call-result-profile-transport-audit.md
9f71c8c40d6850bffccb27d7393bf6219f0ceca5cf1fe1e738073ea943706083  crates/yu-solver/src/candidate_context.rs
2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b  crates/yu-solver/src/candidate_extrusion.rs
26abb65f09f2dcf7b3f798329d7f9cf867d3e6196b4cd79c03b3b558d90566e5  crates/yu-solver/src/candidate_source.rs
270ee70b331e4095f404fafafdf0731b57dd451c130cdf251aea2b5944d7cc6c  crates/yu-solver/src/shadow_apply.rs
a37c0c605802fc482c20a59199eea7a09b56ab966454db2b11dfe2d62b1dead7  crates/yu-solver/src/lib.rs
436687cbc8c4ea372d0066f3f8a8e46cfc28223ade163f49864cd3c5039c60e6  crates/yu-solver/src/candidate_scheme.rs
deee5a0892b02bc9ee23a1f2a35c76175094c558ed7dfb2cf55a7e115ac54225  crates/yu-solver/src/candidate_effect.rs
9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a  crates/yu-solver/src/candidate_scope.rs
1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb  notes/design/2026-10-02-typed-boundary-realization-draft.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
```

## Commit packet

- Exact lease: `notes/theory/2026-10-16-native-result-replay-adequacy.md`.
- Baseline: `d40452204`; no dependencies edited. Two input hashes changed
  from the packet through primary-confirmed review/integration metadata only, as recorded
  above. Native hashes match the prior audit; Git-tree comparison remains
  primary-owned.
- Review: producer derivation only, independent review pending; original
  theorem and production gates OPEN. Full source reachability, effect
  agreement, complete replay, generalization and abnormal histories unverified.
- Checks: static owner/caller reads, sole-discharge-insertion search,
  dependency hashes and final whitespace scan. No executable verification.
- Proposed checkpoint: `research: isolate native Result satisfaction bridge`.
- Shared deltas left to primary/curator: retain FIRST-RESULT ADEQUACY OPEN;
  record the bounded Value post-check lemma and actual replay activation
  path; route the precise common-model base to source constraint generation.
  Do not create a requirement that inference evaluate source packets.

Frozen at handoff; no further producer writes without a returned lease.
