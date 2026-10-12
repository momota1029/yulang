# Active-root Call: source and operational owner crosswalk

Date: 2026-10-13
Status: frozen, unreviewed bounded source correspondence; research only
Baseline: `f44d4e660d7eb1cf43d9cf863fb4fe0a834a8778`
Lease: this file only; complementary static audit, no delegation

## Objective, method and claim boundary

Trace the Y3 producers and consumers needed to relate nested g's `f y`,
its extrusion, g publication and two independent uses to the original
source Generalize rules. The discriminator remains:

```text
let rec f = lambda x.
  let g = lambda y. (lambda z. y) (f y)
  in {a = succ (g 0), b = g true}
in f
```

This text identifies the existing reference witness, not an asserted Y3
parse/admission instance. The trace below concerns the represented parameterized
local-binding route. No executable realization of this entire term was produced.
`LocalSourceForm` has no Record form; Boolean/`succ` source contracts and the
whole witness's elaboration were not established here. This does not reject
the language source or narrow its supported semantics.

Method: inspect actual field definitions, construction branches and their direct
consumers, then compare them with the selected source-rule premises. Hypothesis
for the operational trace: an authentic LocalSource supplies the indicated
resolved local f/g and formal y occurrences. No `K_g`, complete `Q_c`, or C
source-telescope assignment is assumed. The result is a bounded owner
characterization, not a constructive parent theorem or independent review.

## Governing sections and accepted decisions

- Top-level inference principles, §§1–5: native constraint accumulation,
  extrusion/generalization, natural inference and separate proof obligations.
- Source Generalize selection, §§2–4, and selected construction §2 L1–L5,
  §§3.1, 3.3–3.4, 4 and 5.1–5.3: source registration supplies the validating
  component; owning rules supply typed records and original telescopes; Build
  preserves every clause; publication allocation consumes these facts.
- Local self-recursive binding, Selected source behavior, Proposed
  source-to-solver seam and Required invariants: nested references to an active
  outer initializer constrain its existing monomorphic root; installation
  follows intrinsic actions; later uses capture/freshen the live root.
- Source Call generation construction, §§4.2–4.4; original Call formation,
  §§2–4; source-interface definition, §§2–4; complete Call contribution
  definition, §§2–3: lexical/checking occurrences, whole-carrier, entry,
  receiver, invocation and result/future interfaces retain their joint indices.
  A native negative Function does not supply those source judgments.
- Parent-copy decision, Selected operation, Apply-result source-fragment
  ownership, Nested Apply membership and Definition-root Value ownership;
  association clarification, Approved extrusion-event qualification,
  Definition-root origin and Qualification; copied-row decision, Decision and
  Scope: actual occurrence G/F and its signed pairs qualify through the
  independently constructed Value-reference graph. Type rows/bounds, levels
  and copied descriptions cannot replace those Value incidences.

The existing native shared-C map and conditional two-use discriminator are
dependencies of the primary's proof work, not rederived or reclassified here.
This packet neither selects fresh C_i nor turns qualification into registration.

## Exact producers, identities and consumers

Crate paths in the following table omit the leading `crates/`; abbreviated
filenames refer to the already named owning crate file. Locations refer to
the pinned source hashes below.

| Cut | Concrete Y3 producer and retained data | Direct consumer / limitation |
| --- | --- | --- |
| Local declaration and y introduction | `yu-hir/src/module/local_source.rs:729–805` constructs `HirLocalId`, binder source identity, initializer index, parameter IDs, lexical `LocalSourceScope`, and `local_parameter_owners`. The initializer's Lambda chain starts at `LocalInitializer(g)` and advances through its parameter scopes (`329–365`). | Lexical lookup and candidate scheduling consume these IDs. These are authentic lexical identities; they are not `K_g`, `Desc(K_g,y,Value,sigma_y,Delta_y)`, or complete event telescopes. |
| Active f visibility | `local_source.rs:329–373` temporarily installs parameterized f before its initializer, retains it while a nested initializer forms, then restores/publishes sequentially. Identifier formation `636–657` retains `Name{resolution:Local(f)}`. | `candidate_source.rs:296–325` maintains `active_initializers[local] = endpoints[initializer]` during planning and removes it at Install. The same active endpoint is used by all matching recursive references. |
| Inner resolved f Name | `candidate_source.rs:375–390` detects active f and emits `Action::Link{occurrence,endpoint,target:pos.value}`. `candidate_source.rs:665–668` obtains the active endpoint's positive Term and calls `admit_candidate_value_link(...,30,lower,upper)`. | `candidate_scheme.rs:1337–1347` records constraint provenance and drives `constrain_live_value`. The Name has its own component/facade row; the action supplies a constraint from the existing active root. It does **not** establish literal row identity or a complete provider certificate. The scheduled Link omits f's local handle and its active-versus-established classification. |
| y formal recipe | `candidate_source.rs:189–200` associates the retained Lambda parameter ID with a parameter recipe and `FormalRegistrationInput{owner,lambda,parameter,recipe_position,native_root}`. | Parameter endpoints serve the native demand. This native registration is not the source component/telescope declaration required by Generalize. |
| Original App syntax and demand recipe | `candidate_source.rs:394–411` stores `CandidateRelation::Apply` plus `ApplySourceInput`: source expression/callee/argument indices, native endpoints/effects, level, checking occurrence and cause. Its `owner` is `source.definition_root()`, the module definition owner of the whole carrier. | `shadow_apply.rs:1310–1404` validates the recipe, creates the four-port negative Function, records a `NativeInterface` and admits `callee <: demand`. No nested definition-root G / resolved receiver F occurrence certificate is emitted by this step. |
| Available Call reader | `candidate_call.rs:282–437` authenticates source ownership, lexical indices, scopes, checking cause, negative Function ports and optional formal registration. | `CandidateSourceCall` exposes native coordinates; `PendingCallConstruction` explicitly requests original Gen-Call-0, whole-carrier and dispatch/result/future suppliers (`214–243`). For callee `Local(f)`, the parameter-only `formal_name` producer supplies no formal registration. This is missing evidence, not a source error or prohibition. |
| Level-aware extrusion | `lib.rs:12411–12447` passes a structural endpoint, polarity and receiving row's numeric level to `candidate_extrude`; the latter is declared in `candidate_extrusion.rs:21–26`. Its per-operation polar memo is indexed by `(endpoint,polarity,target)`; wrong-level row creation invokes parent retention (`95–124`). | `candidate_intrusion.rs:171–221` emits `Parent{copy,parent,polarity,target}`. Its vector index identifies a stored pair; no invocation/occurrence ID groups the actual pairs, and no source Value origin or receiver is stored. `(C,B,+)` / `(D,R,-)` are the reference witness's names; this pass does not assert actual Rust row ordinals or exact emitted pair count. |
| Present intrusion consumer | `candidate_intrusion.rs:358–489` traverses solver Value/Effect rows, both bound sides and Function ports, then compares components of type copy/parent endpoints. | Canonical merging consumes those pairs and propagates bounds. This consumer is the existing type-dependency SCC mechanism. Its graph and activation input do not implement the approved independently sourced Value-reference G/F test. Successful merging would not establish that corrected correspondence. |
| g publication | `candidate_source.rs:306–328` orders Install after initializer actions and keeps the one-shot effect edge; `644–647` schedules publication of the exposed endpoint. `candidate_scheme.rs:1320–1334` stores `LocalScheme{id,root,boundary}`. | Publication retains a live root/boundary. It emits neither `ScopedClosure(p_g,K_g,T,...,N_g,R_g)` nor a complete source relation and binder classification. Numeric boundary and root reachability cannot substitute for these records. |
| Two later g Names | Each nonactive resolved `Local(g)` emits its own `Action::Local{slot,occurrence,value,level}` (`candidate_source.rs:387`). `candidate_scheme.rs:1360–1386` captures the same installed live root anew and prepares a distinct FreshUse for each route. | `prepare_candidate_fresh_use:981–1025` builds one canonical-row map per route, copying only local rows above graph boundary that are not nongeneric. `step_candidate_local_use:1500–1537` restores captured bounds and links that route's root to its Name facade. `commit_local_use:227–235` retains `LocalFreshRoute{slot,local,occurrence,graph,rows}`. These are concrete operational maps; they do not label original `new(p_g,i,g)` frames or allocate absent source telescopes/equality clauses. |

The direct active Link and the later Local routes are different constructors
with different retained payloads. The active f Name does not go through
`LocalScheme`, capture, or fresh use. Independent g routes each have a fresh
map, but references to fixed native rows remain shared according to the actual
row rule. No classification of a generated coordinate as source Shared,
Established, ViewLogic or EventProof follows from that rule.

## First missing producer/consumer seam

At g's original **definition registration plus inherited active-f reference**,
the selected Generalize consumer needs the actual validating component and
typed dependency relation. The concrete declaration record supplies g's lexical
ID; the active-Name branch knows f's local identity and exact live endpoint.
Neither constructs the active dependency's original source law/record. The
scheduled Link then preserves only the constraint incidence. This is the first
active-root-specific missing bridge; even the earlier parameter recipe is
only a partial lexical/native proxy for its required Desc declaration.

The selected §3.3 records cover registered Internal peers and installed
Mono/Established captures. The active outer f is not made either kind by this
branch. §5.1 explicitly **consumes** the registered component; it does not
derive it from SCC membership. Thus §5.1 cannot classify this dependency,
and §5.2 cannot allocate the complete g program from the current payloads.

Downstream, a second concrete loss is independently visible: the App record
has source indices and native ports, but the extrusion signature and Parent
record have no approved e/G/F grouping. Existing constraint occurrences,
FunctionPort dependencies (`candidate_context.rs:2559–2606`), replay origins
and physical bound storage retain native derivation incidence. They are not
original definition registration, whole-carrier admission, or source equality
operand telescopes. Completing event retention alone would therefore not
establish Generalize's classification/allocation law.

These statements identify absent fields/outputs in the inspected constructors
and their exact consumer mismatch. They are not a whole-repository impossibility
claim: another adopted constructor could supply a law, but no such application
for this active-root case was established here. No complete `Q_c`, original
source admission, equality transport, C allocation or principal coverage was
derived. The parent A/B gates remain OPEN.

## Checks, independence and omitted scope

Commands: bounded `rg`/`sed`/`cat` owner reads and `sha256sum`; one leased
Markdown write. An initial read-only baseline/status inspection resolved the
pinned full SHA and reported no dirty paths. No Git mutation, compiler edit,
test, build, executable probe, mutation experiment, reference execution or
measurement sample occurred. Several combined documentary captures truncated;
the decisive structs and owning branches were subsequently read narrowly.

This evidence is independent of a toy transition oracle: it reads the actual
Y3 producers/consumers and separately selected source premises. Shared
assumptions are the pinned source, accepted language decisions and authenticity
of the hypothetical represented local source. It does not prove the source
laws by replaying an assumed checker. Seeds/ranges are inapplicable. No runtime
trace, full-source HIR admission, complete primitive/effect/Call semantics,
recursive L4, all-path rollback/replay, termination, soundness or principality
was checked. At most three lightweight read commands were batched concurrently;
zero heavyweight processes.
CPU/RSS and exact elapsed wall time were not measured; no worker budget was
numerically specified. No delegation occurred.

Failure/invalidation conditions: a dependency hash changes; f uses a different
source constructor (including module routing or zero-header Lambda forms);
another source law is adopted for the active dependency; or the primary supplies
an authentic complete registration/Call artifact omitted by this bounded trace.
Revalidate that dependency cone before using this crosswalk for proof closure.

Recommended next action: the primary should assign the constructive lane the
local source/operational law at **g registration and its active-f Name/demand
accumulation**, with the actual direct-Link and published-use maps fixed as
targets. It must supply the inherited relation, B telescope and complete
equality operand transport before applying Source Generalize; route any genuine
contradiction through design authority. Further bound-store/SCC reconstruction
or another assumed allocation probe does not supply this premise.

## Frozen dependency SHA-256

```text
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389 notes/design/2026-10-11-yulang-inference-top-level-principles.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38 notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240 notes/theory/2026-10-08-source-generalize-definition-and-proof.md
38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895 notes/design/2026-10-10-local-self-recursive-binding.md
4940e031b83d3d0315f17beb51ba2e952ec64ae7d57d9ae0d086024c7305ca9f notes/design/2026-10-07-original-call-formation-definition.md
6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073 notes/progress/2026-10-06-source-call-generation-construction.md
20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c notes/design/2026-10-08-call-source-interface-definition.md
4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e notes/design/2026-10-07-complete-call-contribution-definition.md
6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b notes/design/2026-10-10-parent-copy-scc-intrusion.md
28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775 notes/design/2026-10-12-intrusion-value-type-association.md
7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd notes/design/2026-10-12-value-reference-copied-row-ownership.md
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed crates/yu-hir/src/module/local_source.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49 crates/yu-solver/src/candidate_source.rs
79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35 crates/yu-solver/src/candidate_call.rs
cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411 crates/yu-solver/src/shadow_apply.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1 crates/yu-solver/src/candidate_scheme.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0 crates/yu-solver/src/candidate_extrusion.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0 crates/yu-solver/src/candidate_intrusion.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987 crates/yu-solver/src/candidate_context.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94 crates/yu-solver/src/lib.rs
```

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-13-active-root-call-owner-crosswalk.md`.
- Baseline: `f44d4e660d7eb1cf43d9cf863fb4fe0a834a8778`.
- Dependency changes: none by this worker; frozen hashes above. Integration
  revalidation belongs to the primary.
- Claim/review status: unreviewed bounded source correspondence; no theorem,
  source rejection, new semantic selection or implementation authority.
- Checks already run: field/branch/consumer inspection and dependency SHA-256;
  zero tests, builds, probes or measurements.
- Proposed message: `research: map active-root Call producers and publication seam`.
- Shared deltas intentionally left to primary/curator: link this crosswalk to
  the existing active-root law gate; name g registration plus inherited active-f
  dependency as the first source bridge and extrusion e/G/F retention as the
  downstream operational seam; preserve all original OPEN A/B and complete
  Call/Generalize gates. No shared record changed. Writes stop at handoff.
