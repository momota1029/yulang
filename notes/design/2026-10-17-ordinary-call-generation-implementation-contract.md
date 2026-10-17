# Implementation/source recipe for the module `id 0` Call

Date: 2026-10-17  
Status: frozen Luna implementation recipe; no code lease  
Claim class: provisional candidate source evidence and owner-mapped implementation recipe  
Sprint: `ordinary-call-original-generation-20261017`, revision 2  
Contract SHA-256: `a1a409b84b5f9750266eea3790a9e098fce8af32e30348f17ee2d1ac1ffb1c21`  
Baseline: `0717a882c`  
Exact source: `my id x = x; my answer = id 0`  
Original theorem conditions discharged: **0**

This recipe uses the existing candidate path to add a falsifiable source
observation for this exact direct module-name/literal call. It does not add an
Application typing rule, alter admission, or promote candidate facts to
original judgments. The missing original producer and the conditional rule
proposal remain open and unadopted.

## 1. Frozen inputs and source-owner route

All rev2 dependencies were rechecked before this recipe. Relevant direct pins:

| Input | SHA-256 | Owner evidence used |
| --- | --- | --- |
| `candidate_source.rs` | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` | Source traversal, Lambda/Apply recipes, ModuleDef actions and source schedules |
| `candidate_call.rs` | `cbad9cf51a05343eb7a29ab77aac520891467a8aa4edc3201ea3d91f978984a1` | Borrowed source-call observation, formal-only provenance, pending suppliers |
| `shadow_apply.rs` | `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf` | Candidate solver entry/consumer APIs and explicit unresolved-premise set |
| `candidate_scheme.rs` | `52b7281946de755003ee8f3b3d18cbc2df6cc6db5566b4e5ecf391b74a92640a` | Candidate SCC graph capture and open-use routing |
| `lib.rs` | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` | Ordinary batch collection, `Action::Module` routing and candidate Apply admission |
| `research_accepted_call_vertical.rs` | `9c3dea05d11c49bae09520d5f6fe27430f1706185232daf2cf8e8d801a42d71a` | Existing candidate vertical regression and observation assertions |
| original-generation proof | `bd2a690517118c8826dfe1a2fe9db53c829a1638bd2e6a1fd5aa01a252735aab` | First missing original introduction and owner TODOs |
| original-generation handoff | `1ff0c3dc71c4b7e09de5e00ff47b158627cc67320d29d820d38d76ed330b98d3` | Frozen proof obligations and exact falsifiers |

The actual path in the inspected code is:

1. `ConstraintBatch::collect_candidate_mode` traverses the source. The Lambda
   branch retains its parameter/formal registration and `LambdaRecipe`; the
   formal `Name(x)` is tracked by the formal-name table. The module `Name(id)`
   instead retains `PendingDefinitionUse` and `Action::Module`. These identities
   remain separate even though the module definition's value is a Lambda.
2. The Apply branch retains `CandidateRelation::Apply` and one
   `ApplySourceInput` with source owner, callee, argument, result/effect ports,
   checking occurrence, cause, and an optional formal-name identity. The direct
   module Name has no formal-name identity. The literal is an actual Integer
   source child, not a lexical Name use.
3. When its scheduled actions execute, `Action::Module` routes the actual
   definition use through `route_candidate_open_use` for an active SCC use or
   `route_incoming` otherwise. `candidate_scheme.rs` retains candidate graph
   capture and distinct fresh-use routing; `lib.rs` owns the incoming route and
   transaction. This is candidate graph/use behavior, not source publication
   correspondence for the original typing rules.
4. The Apply action reaches `InferenceSession::admit_candidate_fact`. It checks
   that the retained Apply input and recipe have matching source occurrence and
   endpoints, constructs a native four-port negative Function demand with a
   fresh invocation-effect row, then admits the callee-to-demand pair and
   effect links. Ordinary propagation consumes that pair in the candidate
   solver. `CandidateInference::source_call` can then validate the borrowed
   HIR Apply and native ports. `fresh_use` and `export(answer)` are available
   candidate consumers for this source.
5. No runtime executor is invoked by this candidate API. The export is a
   candidate graph observation, not execution of `answer`; an empty candidate
   conflict set is not a successful original Call derivation or source/native
   theorem.

The public `PendingApplicationOccurrence` in `lib.rs` is structural HIR
evidence with direct Name resolution only. It is not an admitted constraint or
Function recipe. `PendingCallConstruction::suppliers` currently keeps
`OriginalGenCall0`, `ArgumentReifyAndWholeCarrier`, and complete receiver/result
suppliers pending for this non-formal call. `shadow_apply::UNRESOLVED` also
names module source typing/admission and module receiving/export correspondence.
These are honest missing obligations; the API does not discharge them.

## 2. Narrow future code lease that is safe before semantic adoption

There is one useful, reversible candidate-evidence slice that can be leased
without deciding the original rule. It adds an exact module-callee observer and
keeps the corresponding module obligations visible in the pending supplier
view. It cannot turn the candidate path into production typing.

Minimum exact future paths:

- `crates/yu-solver/src/candidate_call.rs`
- `crates/yu-solver/tests/research_accepted_call_vertical.rs`

Potential changes under a separately issued code lease:

1. Add a borrowed `module_callee_target()` observation on
   `CandidateSourceCall`. It returns the `DefId` only when the already
   validated direct callee source is `Name(ModuleDef(target))`; otherwise it
   returns `None`. It must not inspect a solved endpoint, infer a formal from a
   Lambda value, peel arbitrary wrappers, select a provider/root, or create a
   source certificate.
2. Extend `PendingCallSupplier`/`PendingCallConstruction::suppliers` with the
   two module-specific unresolved items already present in the canonical
   `UnresolvedPremise` list: module Name source typing/admission, and module
   use receiving/export correspondence. Yield them only for an actual direct
   `ModuleDef` callee. Keep all original Call suppliers pending. No inference
   gate or language behavior changes.
3. Add one case to `research_accepted_call_vertical.rs` for the fixed source.
   Assert ordinary HIR lowering succeeds, exactly one Apply is observed, its
   actual callee target is `id`, the argument source is Integer `0`, and no
   formal registration/lexical formal use is attached. Assert its pending
   construction retains the original Call, whole-carrier and complete-result
   suppliers plus both module-specific unresolved suppliers. Then assert the
   existing candidate solve has no candidate conflicts, the module callee
   occurrence has the candidate fresh-use observation, and `answer` has a
   nonempty candidate export. These assertions describe source-to-candidate
   constraints, propagation and candidate consumption only; do not call this
   execution or semantic admission evidence.

This test is the decisive falsifier for the instrumentation: fail if `id` is
classified as a formal, if the argument is not the actual literal occurrence,
if the candidate Apply loses its checking occurrence/ports, if the module use
does not reach the existing candidate route/consumer, or if any required
original/module supplier disappears before it has an authentic owner. A green
test supports only the exact candidate evidence above. It cannot establish
`e_c`, original `Gen-Call-0`, O0 substitution, runtime behavior, or any parent
theorem condition.

`candidate_source.rs`, `candidate_scheme.rs`, `lib.rs`, and
`shadow_apply.rs` need no changes for this observational slice: their current
owners already generate the inputs, route the module use, propagate the
candidate pair, and expose the consumer. If the proposed regression shows one
of those stages is missing, stop and return that exact source owner through
Luna before expanding the code lease. Do not repair it with a default seed,
formal-root fallback, provider cast, endpoint match, source-admission bypass,
or a restored withdrawn Simple-sub path.

The instrumentation is provisional. Luna owns cleanup: remove the temporary
module-callee accessor and candidate-only supplier names after an authentic
module-name Application producer supersedes them, or remove them if the
original rule is declined. Keep the separate `UnresolvedPremise` items until
their original owners actually derive the judgments they describe.

## 3. Complexity, observable changes, and adoption boundary

The proposed accessor is a direct borrow from the already checked callee
expression, O(1) time and zero new per-call storage. Extending the static
supplier iterator adds a constant number of observations only for direct
module-name callees; it allocates no new vectors. The focused test adds no
runtime cost. This slice therefore has O(C) total observation work for C
observed calls and changes no asymptotic behavior, scheduling, or inference
results. There is no performance reason to spend the user's complexity
authorization here.

If a later, authorized original producer needs to join many module-use records
to many Apply records, use a one-pass keyed index as the default: expected
O(U+C) construction/lookup time and O(U) additional storage for U source uses
and C calls. Repeatedly scanning every use for every call is O(U*C) with lower
index storage, and is an explicit time/space alternative if measured memory
pressure justifies it. Either algorithm still must validate the actual source
identity and owner; complexity tradeoffs cannot supply missing judgments or
change admission. No such index is needed or licensed by this slice.

No production or observable language behavior changes under the recipe.
Adopting the proof's `Gen-ModuleName-Literal*` formation proposal remains a
separate semantic decision because the pinned original formation family has
no constructor for this module Name plus literal Application. The proposal
preserves the generic open source-rule reduct under its stated local premises,
but has not been embedded into the original family at the full indices and
does not prove that the existing Code-Call consumer accepts the new record.
Options at that boundary are:

- leave the source producer open and keep these candidate observations
  provisional; or
- review and adopt an explicit formation extension, while separately proving
  its original-family embedding, source publication/root-use map, complete
  Call telescope and consumer substitution.

The second option changes which source derivations are available. This recipe
does not choose it. Neither option licenses changing whole-carrier meaning,
provider/challenge domains, guards, full Call arms, diagnostics, or runtime
behavior to obtain a green test.

## 4. Original proof/source work that remains

The proof handoff identifies the first missing original constructor as the
joint module-binding use to original Application-demand introduction at the
actual `Name(id)` callee. Its concrete source owners remain:

- `MODULE-DECL-USE-SCOPE`: Source Generalize/FinalRoot plus the actual module
  registration/reference owner must produce one whole-tuple use map with the
  fixed provider and source anchors. `PendingDefinitionUse`, `Action::Module`,
  the routed candidate graph and a candidate `fresh_use` are not this original
  binding certificate. Falsifier: replacing `d_id` with formal `d_x`, or using
  a candidate/native endpoint as the publication/root derivation.
- `MODULE-CALL-SIGNATURE-APPLICATION`: the original Application/Call rule
  owner must build the one full dependent telescope and every original
  conjunct, including guards, complete carrier, all independently licensed
  arms, result incidence and authentic occurrence before satisfaction.
  `admit_candidate_fact` constructs only a candidate inequality. Falsifier: a
  dropped arm/guard, endpoint-only formation, chosen provider, or successful
  candidate check used as an origin.
- `MODULE-GENCALL-ORIGINAL-EMBED`: after actual owner inputs and separately
  authorized rule adoption, embed the module root and literal constructors in
  the original formation families, then apply adopted O0 to authentic `e_c`
  and substitute it into the named Code-Call consumer. The current conditional
  erasure result is not that embedding.

Until those judgments exist, there is no authentic original `e_c`; O0 has no
record to consume here. Literal `Emit-Original-Literal-Arg` can produce only
the local whole-argument conjunct once its real demand/reification premises
exist. The native ID theorem does not select `d_id`'s actual public root.
Constraint propagation, if candidate or later ordinary inference computes a
solution, cannot repair these missing introduction premises.

The source set remains exactly the fixed source. All original A/B quantifiers
and all other parent gates remain open: F1/FK1, N-Transport, complete Call
satisfaction, source/native adequacy, soundness, principality and termination.
No accepted-call theorem or execution result is claimed.

## 5. Reused evidence, rejected shortcuts, and verification limits

Reused:

- The existing HIR admission and candidate vertical tests establish owner
  patterns for formal-call candidates and module fresh-use observations. Their
  source strings differ from the fixed module-Name/literal case.
- The current candidate source producer retains Lambda, ModuleDef, Apply and
  literal source identities. `candidate_scheme` and `lib.rs` route module
  uses; candidate Apply admission builds the four-port demand before
  satisfaction; candidate observation exposes native ports and unresolved
  premises.
- The frozen proof's child-constructor expansion and the two CLEAN proof
  reviews are reused only within their stated conditional scopes.

Rejected as substitutes for the missing original rule: old Name/Name
Gen-Call-0; formal-callee `Gen-Call-Syntax`; candidate Apply endpoints/native
Function facts; `ApplySourceInput`; module routing or candidate fresh use;
O0 applied without authentic `e_c`; literal-only whole-argument emission;
the unadopted rule proposal; and any withdrawn Simple-sub bypass.

No code, tests, Cargo, build, executable probe, formatter, or Git operation was
run or is authorized in this recipe lane. This document is not implementation
evidence and has no independent review yet. No original condition is closed.

## 6. Freeze and runtime receipt

Exact writes are limited to this recipe and
`tasks/agent-loop/inbox/20261017-ordinary-call-generation-implementation-contract.md`.
No scratch or generated path was created. No descendants were launched.

Role requested: Luna/high, `gpt-6-luna` / high. Effective model and effort:
UNKNOWN; no runtime model metadata was exposed to this worker. Assignment cap:
720 seconds. Exact active-work telemetry was unavailable; conservatively charge
the full 720-second author envelope at STOP. Only a clock receipt taken during
the work is available, so no exact active duration is claimed. The next step
inside the envelope is freeze both exact outputs, hash them, and return the
implementation owner map, safe provisional code slice, unresolved premise
owners, and review boundary to Luna. Any source/test lease requires a separate
reviewed contract revision and resource allocation.
