# `invoke`: actual literal emission and a missing formal declaration

Date: 2026-10-11
Status: independently reviewed bounded source characterization; original theorem OPEN
Baseline: `67b8119ca22313dc3e8d5ede623ae19dc2a65425`
Exclusive producer lease: this file only
Claim class: actual constructor trace and minimized input obstruction, not a conditional Call theorem
Implementation, semantic adoption, soundness/principality certification: none

## 1. Frozen objective and hypotheses

Construct the actual tagged complete Call emission for
`my invoke f = f 1` from the resolved source and the selected declarations.
The requested conclusion is an authentic formation derivation, not a record
whose fields assume that formation. The source supplies the actual lambda
`L`, its unannotated formal `d_f`, lexical Name `u_f`, Call `c`, integer
occurrence `a` with payload `1`, `Resolve(u_f,d_f)`, and
`epsilon:ArgumentChild(c,a)`. The lambda has no free captures. No Name
declaration is introduced for `a`.

The source statement ranges over the actual resolved instance and its lawful
nominal renamings, at the original binder tree `B`, ordered joint context
`X`, scope `Delta_c`, lexical context `T_c`, and shared `xi=(nu,K,D)`.
Semantic coordinates remain at their original binders. Formation must retain
their entire dependent schemas for every legal whole assignment, independently
admitted context/history and actual output provider; it does not choose an
assignment or inhabit an event fiber. Empty semantic fibers must remain
possible. Actual-provider suffixes are families over the provider later
returned by the callee, not a provider selected during generation.

The old selected index order is original formation §2:

```text
(B,X,xi,Delta_c;
 d_f,A_f,R_f,u_f,u_x,c,u,U_e,beta,p0,p_out(c),ElimOrigin).
```

Its existing `u_x` is the Name/Name argument use. A literal is not a term
of that old argument domain. The requested q1 extension must retain the old
tuple verbatim on its old branch and carry the actual literal incidence in a
distinct tagged branch, with each dependent field at its original preceding
binders. No complete new literal telescope has been produced merely by
displaying that old tuple. In particular `u` must stay distinct from `u_f`,
`F_c=U_e` is the scoped complete demand, `beta=(d_f,R_f)` retains formal
registration, and `p0` stays distinct from the complete output `p_out(c)`.

Required outputs: actual formal/Name/literal Data and Result derivations;
complete images and catalogues; tagged argument Reify/Delay; a complete
Function demand; distinct upper checking occurrence and callee, whole-argument,
WF, complete-operation and complete-result predicate origins; source-owned
provider-dependent suffix, role/protection and output origins; and a tagged
emission with whole-action and unchanged old-family behavior. Truth of those
predicates, independent admission, solving and later Call discharge are
separate duties. Complete effects, protection, all declared arms, complete
world/provider/future domains, witness alternatives and residual lineage are
required throughout.

Hypotheses admitted here are the actual resolved source and the already
selected scoped definitions below. No `Fam_delta` application, complete
declaration graph, `FullLiteralBuild_orig`, `OriginalArgReifyProducer_orig`,
emitted member, `H_oldext`, old-family compatibility, or H0–H3 of the recent
conditional proof is assumed. The assignment expressly requires establishing
the actual declaration applications. Their absence stops this derivation.

## 2. Exact governing definitions

- [Top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
  §§1–5: native Simple-sub generation/accumulation/propagation, levels,
  extrusion/intrusion and generalization; no eager per-constraint solution or
  search for another typing.
- [Emission q1](../../questions/2026-10-10-original-literal-call-emission/approved-answer.md),
  “Proposed decision and authorized scope”: construction direction, not
  adoption of emitted membership or implementation.
- [Reify q2 direction](../design/2026-10-10-call-reify-construction-direction.md),
  “Scope” and “Required next construction”: tagged old/new registry sorts,
  structural argument license, suspension and distinct `J_lit`.
- [Registry adoption](../design/2026-10-10-original-registry-constructor-adoption-proposal.md)
  §§1–2: six adopted API choices, with actual complete local application and
  independently fixed original conformance still required. Its frozen
  [definition source](2026-10-10-source-owned-original-registry-construction.md)
  §§2, 4.1–4.2 supplies raw-P owner interfaces, not the missing applications.
- [Source Generalize](../design/2026-10-08-source-generalize-definition.md)
  §§2–3 and [its source proof](2026-10-08-source-generalize-definition-and-proof.md)
  §§2–4: ordinary Parameter role/Desc and direct rule generation. L1–L5 remain
  genuine local law inputs; approval does not instantiate an unavailable law.
- [Call input](2026-10-07-call-input-construction-proof.md) §§3.1–3.4:
  actual original Data/Code, parameter entry, argument origin and complete Call
  consumers. [Original formation](../design/2026-10-07-original-call-formation-definition.md)
  §§2–4 defines O0 on actual emitted records.
- [Source interfaces](../design/2026-10-08-call-source-interface-definition.md)
  §§2–4 and [complete contributions](../design/2026-10-07-complete-call-contribution-definition.md)
  §§2–4 retain actual declarations, all arms, open carrier hole and
  provider-dependent futures; static incidence supplies no operator law/C0.

The previous [pre-Call construction](2026-10-11-adopted-invoke-precall-construction.md)
and [complete Call attempt](2026-10-11-invoke-complete-call-proof-attempt.md)
are inspected as failed routes, not premises. The unadopted
`RuleCall_L`/`CertCall_L` envelope in the older literal pipeline is excluded.

## 3. Actual native constructor and consumer trace

This is a reading of the owning code, not an executed compiler test or a
transition model. The relevant entry is `CandidateInference::solve`
(`shadow_apply.rs:75`), which preflights actual LocalSource and calls
`collect_candidate_mode(hir,true,true)`. `lib.rs:1126` selects actual
`hir.local_source(root)` in graph-effect mode and calls
`candidate_source.rs:168`, `emit_candidate_source`.

1. At `candidate_source.rs:178–246`, the collector allocates a parameter
   recipe for each actual Lambda formal, stores its owner/lambda/parameter
   identity, and maps the actual resolved Name to that same parameter recipe.
   These are `FormalRegistrationInput`/`FormalNameInput` fields, not a whole
   original Value entry or registry `Reg_src`. Initialization at `:532–559`
   later supplies their native positive root from that exact recipe.
2. `Work::Visit` at `:252–281` pushes Finish before its children. The stack
   visits callee and argument before finishing Apply; the source level is
   retained. No predicate satisfaction is needed to generate the recipe.
3. The actual Integer arm at `:336–350` emits exactly four scalar facts:
   `Int+ <= value(a)`, `value(a) <= Int-`,
   `EffectBottom+ <= effect(a)`, `effect(a) <= EmptyEffect-`.
   Its wildcard payload is not converted to a semantic primitive certificate.
   The resolved Parameter Name arm retains the same parameter endpoint and
   emits its evaluation purity facts (`:362–391`).
4. Apply at `:394–413` retains both child endpoints/effect positions, the
   result/application positions, source owner, level and recipe. It allocates
   `ConstraintOccurrenceId(c,0)` and the matching Cause, stores an
   `ApplySourceInput` with `native=None`, and schedules `Action::Candidate`.
   Thus the scalar checking provenance belongs to `c`, separately from the
   lexical source `u_f`. No cast to the complete original upper judgment occurs.
5. `execute_candidate_action` (`candidate_source.rs:660–672`) dispatches that
   action to `admit_candidate_fact` (`shadow_apply.rs:1304`). This function
   validates its exact retained source operands. In graph-effect mode it
   allocates an invocation row at the application's effect level, then calls
   `negative_function_term(argument+, argument_effect+, invocation_effect-,
   result-)` at `:1362`. It records the native interface, admits provenance,
   and calls `constrain_live_value` (`:1394–1401`). It also admits and actively
   calls the effect constraint consumer on callee-evaluation and invocation
   links into the application effect (`:1422–1464`). These are actual activation
   calls; a stored relation alone was not used to infer activation.
6. `candidate_call::observe` (`:282–383`) checks actual HIR ownership, scopes,
   child identity, checking Cause, native port polarity/kind and exact negative
   Function children. `PendingCallConstruction::suppliers` (`:224–243`)
   still returns `OriginalGenCall0`, `ArgumentReifyAndWholeCarrier` and
   `ReceiverDispatchAndCompleteResultFutureInterfaces`, plus the formal's
   whole-registration/route/checking-exposure suppliers.

The derived source fact is precise: this path generates and actively submits
the native constraints above while retaining source incidence. It does not
construct the requested complete original fields. `NativeInterface`
(`candidate_call.rs:49–60`) contains Terms and a row number; it has no original
Data/Result proof, typed tagged suspension, complete declaration application,
whole-argument witness interface, operator alternatives or actual-provider
suffix. The exposed pending-supplier API confirms this boundary without
being the sole reason for it. This does not establish complete replay,
termination, hygiene, soundness or principality.

## 4. A concrete formal-port obstruction

The adopted definition forms the unannotated formal header and ordinary
`Desc`/Value role. A required `Declare-Owned-Port` application needs
`complete Fam_delta at (p,I,h,endpoint,source-incidence)`
(registry definition `:371–376`). One concrete owned port is
`ReceivedWholeCarrier`, with intrinsic address
`r_in=FieldPort(k_f,ReceivedWholeCarrier)` (`:548–573`).

At this same raw `P`, header, endpoint, source incidence and actual scope map,
the required input is the **entire declared local input telescope/domain**
of that carrier/entry port and a checked ordered application. It includes
every actual preceding parameter, field domain, opaque alternative, static
license and required local operation. This input is not supplied by the source
token, scalar parameter row or nominal FieldPort address.

No concrete full telescope for this `Fam_delta` is supplied in the inspected
owning declarations. The registry definition `:349–359` names the complete
family as genuine input, and its adopted authority §2 expressly says
`Delta_in^orig` names a required declaration, not a supplied signature.
Original `Entry-Value` (`call-input proof:230–237`) consumes ParameterOrigin,
received carrier/view and receipt/rebind ports; it does not introduce their
complete local domain. Typed-core §§6,9 gives entry behavior and role, not
that raw-P-indexed constructor telescope. Generalize L1/L2 likewise requires
genuine independent local declarations rather than instantiating them.

This missing port input is exact, but a hidden first binder `z_i:U_i` is not
known. The reviewed registry ordering includes `ParameterOrigin` and static-
license construction before entry assembly, and the evidence here does not
establish whether their original introduction applications precede this port
declaration. Naming `z_i`, imposing a simplified domain or asserting that its
type requires a later decoder would invent the missing signature. The source
declaration/import phase must expose this complete family; the formal
construction must apply it in its original order at the point required by the
actual introduction dependencies. This is a concrete missing formal input,
not a claim that it is the earliest missing premise. It is not evidence that
the source is ill typed or that the demanded theorem is false.

The six adopted owner APIs determine how to consume the family; they do not
instantiate it. The source row `Law(delta,complete local signature)` can
retain a supplied declaration, but cannot create its unknown binder domains.
There is consequently no actual same-P literal Data/Result prefix to feed
the Call outputs in this packet.

## 5. Later requested origins and the current q2 boundary

| Required origin | Actual producer/consumer and status at this baseline |
| --- | --- |
| Literal Data/Result and `J_a` | Selected Original-ResultLiteral §3; adopted registry §4.2 DataLiteral/ResultLiteral/Image. Full Int/Return/Prefix applications and `T_c` are required; scalar Integer facts supply none of those complete inputs. |
| Tagged argument Reify/Delay and `J_lit` | q2 selects Reify proof §3 CodeUse/BorrowRef/AllocateArg/SuspendLicense/Original-CallArgReify† and §4.4 StructuralReturn/Prefix plus intact OldImage. They have actual definitions in the selected tagged interpretation. Their genuine `q_ca`, ChildCode, typed event/schema/catalogue/reference inputs remain unavailable here. |
| Complete demand and distinct upper checking origin | Old Name/Name Gen-Call-0, source generation §4.2, forms a complete variable from its original Name operands; original O0 consumes its demand. Native NegativeFunction and `ConstraintOccurrenceId(c,0)` are scalar construction/provenance, without a full typed literal demand/checking introduction. |
| Whole-argument compatibility | Code-Call §3.4 requires its original origin at `J_a,CarrierContract(F_c)` and the same actual Reify incidence. `Int <= argument` or empty argument effect is not that declaration application. `J_lit` remains distinct from `J_a`; the exact whole hole attachment/map is still required. |
| Complete operation/result and Call output | Original complete contribution §2 requires authentic `Q_e/SpecCall_e`; source IF constructs placements only for actual complete declarations/uses. Original Code-Call retains output `Comp(E_c,A_c)` and all operator/predicate origins. Native result/effect rows do not supply this complete operation or its CIncl origin. |
| Actual-provider-dependent suffix | Code-Call §3.4 defines Suffix on actual provider `U`: receipt, its entry, body, designated consumer and native/complete return, with all original pending tails. Native `F_c` cannot choose `U` or construct its actual declared field maps. |
| Old-family conservation and whole actions | q2 uses literal/argument sorts beside the exact old registry, with projections and complete field maps. Old consumers retain the whole old P and all witness domains. A new literal emitted-family/O0 definition and its active consumers have not been constructed; conserving the q2 old registry alone cannot prove this larger claim. |

This identifies why the earlier OriginalArgReifyProducer cut must not simply
be repeated: q2 selected its tagged producer, including suspension and image
construction. The remaining obstacle is its actual earlier inputs and complete
Call hookup. No untagged original-registry extension or old-domain equality is
assumed. No conditional theorem with those unavailable inputs is added here.

## 6. Is emitted membership necessary?

For the **existing selected O0 route**, yes: OC-CallEff's first operand is an
actual emitted record (original formation §4). Code-Call's selected presentation
also explicitly consumes actual Application/Gen-Call-0 origin plus additional
operand origins. OSig-Demand reads a complete demand without emission, but
does not produce those source origins. Dropping the first operand would change
these particular constructor applications.

For **native constraint generation**, no: the actual activation chain in §3
uses source recipes and terms, with no `EmittedGenCall0` operand. The historical
observer inventory is independently excluded from that entry, as recorded by
the [withdrawal authority](../design/2026-10-10-simple-sub-legacy-withdrawal.md),
“Implemented discarded observer inventory retirement.” Actual LocalSource
Call inputs still remain; the two inventories must not be identified.

For **complete Call meaning/soundness/principality**, no universal necessity
of this nominal emitted-family representation has been established. Source
Generalize's selected Build (§4) directly composes complete local rule clauses,
binders and all declared alternatives by source recursion. Its input is those
actual complete rule catalogues, not a theorem that every source belongs to
the historical Name/Name family. Complete source meaning retains the callee
Bind, inert whole argument, same actual returned receiver, all pending/abstract
arms and output-dependent futures regardless of their eventual record layout.
Thus a direct source-to-native-constraint adequacy proof is a possible method
under the current principles; it cannot be dismissed merely for omitting this
packaging. This is not a completed adequacy proof or a retirement decision.

In this source, that direct method still lacks the complete original local
law and consumer correspondence. A direct proof need not first realize the
raw-P decoder or the named `Fam_delta` API if it independently derives the
actual complete port/operation domains and laws at their operational owners.
The missing §4 application belongs to the selected emission construction;
it is not hereby installed as a prerequisite for every possible direct proof.
Scalar purity supplies neither that application nor an independent complete
operational derivation. There is no demonstrated complete alternative
construction allowing the original parent theorem to close. Existing O0/O1
consumers remain explicit if this route is used; retiring their proof edge
would need the primary's replacement/consumer evidence, not reclassification.

## 7. Economy audit, status and next evidence

Two different prior methods left the premise untouched: the adopted pre-Call
rank/decoder derivation assumed the complete declaration graph, and the
complete Call receiver elimination assumed genuine child/checking formation.
This packet instead traces actual constructor applications and activation,
then stops at an unavailable local domain. Another conditional Build,
more endpoint probes, a different model or a new `FullLiteralBuild` name would
not supply it.

Under compiler-engineering's economy rule, complete local application is A
correctness; the ordinary invoke inference requirement remains B. Retaining
source scope/operand/registration/phase evidence at their owning constructors
can remove D reconstruction debt. It cannot manufacture missing primitive,
port, license or operator laws. Universal foreign-registry equivalence would
be C and is not needed here. No parent status or semantics is changed.

No original theorem edge is closed unconditionally by this contribution.
The native source activation trace is a bounded constructor fact, not the
requested complete source theorem. No genuine source counterexample is found.

The smallest next evidence is the actual complete ReceivedWholeCarrier local
declaration at the formal source-registration owner, with its raw-P argument
presentation, original ordered binder domains, every arm and static license,
followed by its ordered application at `h_f/r_in`. q1/q2/q3 and the six-choice
adoption have already selected the construction directions and owner API;
they did not supply this original declaration. No new user decision is shown
necessary just from an omitted signature. Locate/elaborate the existing actual
contract first. If none exists and a new domain or observable local meaning
must be selected, the primary must expose that concrete choice through the
existing design/review/approval process. This leaf cannot fill it by convention.

## 8. Verification, resources and commit packet

Reads: focused `cat`, `sed`, `rg`; read-only HEAD/status inspection.
No tests, builds, compiler execution, probes, measurements, Git mutation,
delegation or external/user contact. Prior test fixtures were inspected only
as source locators, with no claim that they passed. Peak RSS, CPU seconds and
exact reasoning wall time were not instrumented; the assigned wall limit is
30 minutes. Only lightweight inspection processes were used, with at most
three concurrent initial reads and no persistent/heavyweight process.

Requested runtime: Sol (`gpt-6.1-sol`)/high. Observed effective model/effort:
unknown; no runtime metadata was exposed. Prover role config omits pins;
config's default Sol/high is not runtime observation. No Astra job or leaf
was launched.

Coverage excludes an exhaustive foreign-kernel search, all-source inference,
recursive/annotated Call extension, full propagation/replay/level/extrusion/
intrusion proofs, independent C0/admission, public extraction/generalization,
effect hygiene, soundness, required principality, production and F5 cutover.
The artifact is producer-authored and received a narrow independent
compiler-referee review. That review found a major unsupported firstness claim
in §4; the primary corrected it, and a delta review accepted the repair. The
review certifies only the bounded source characterization, not exhaustive
declaration absence or theorem closure.

Commit packet:

- Exact leased path: `notes/theory/2026-10-11-invoke-literal-emission-construction-proof.md`.
- Baseline SHA: `67b8119ca22313dc3e8d5ede623ae19dc2a65425`.
- Changed direct dependency hashes: none; all 27 direct semantic/source inputs
  below byte-match the frozen baseline and working tree at freeze.
- Checks already run: documentary constructor/consumer inspection; 27 pinned
  dependency byte/hash comparisons; artifact local-link and whitespace scan
  (all links resolve, no trailing whitespace). No semantic executable check.
- Proposed checkpoint message: `research: characterize invoke literal emission inputs`.
- Shared-record deltas for primary/curator: retain original theorem OPEN;
  record ReceivedWholeCarrier's unavailable complete Fam telescope/application;
  distinguish selected q2 producer from unavailable source inputs; distinguish
  existing O0 record dependency from native generation and unproved complete
  adequacy. No status promotion or dependency retirement is proposed.
- One next action: obtain/elaborate the complete formal ReceivedWholeCarrier
  declaration at its source owner, then check its original ordered application
  and its dependency order relative to ParameterOrigin/static-license formation.

Direct input SHA-256 snapshot (policy/config reads are not semantic premises):

```text
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
77855c8526e1c105d40fac4dfc58455560fcc6135d280f2302e9809de717c4a8  questions/2026-10-10-original-literal-call-emission/approved-answer.md
d4240c3f9938db958eb1068df2a8f4a35cf4d23721da2eb6cec9f5f3b5bc1516  questions/2026-10-09-original-literal-result-owner/approved-answer.md
4e39f5fc709183cf1bd7b5e4bac1a3da34c62acce7e8e34d089ef9072dc48d37  questions/2026-10-10-call-reify-registry-construction/q2/approved-answer.md
ee4881d97d8f37f7eb70c4ebbd07910ebec297e552a64a0703ff6a8743ccd74b  questions/2026-10-10-call-reify-registry-construction/q3/approved-answer.md
13616d24f2367a08180ccd94c510aca4a7d730821c19be5c4ee6c99bb1f4ad9f  questions/2026-10-11-source-owned-registry-adoption/q1/approved-answer.md
850a6a035d0e4b6ad3be761205d24c51b4b894fcc5e795c4dc30415e529c5a30  notes/design/2026-10-10-call-reify-construction-direction.md
2d6439507f01f38234909f98d86b1d2fbe31d3c7dd60d453cf1c199604020451  notes/design/2026-10-10-original-registry-constructor-adoption-proposal.md
9bc209159fee600ed7bc3e389ceef54aeaaa72c7e9f67235e4fc9e2a5c26cfbb  notes/theory/2026-10-10-source-owned-original-registry-construction.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38  notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240  notes/theory/2026-10-08-source-generalize-definition-and-proof.md
f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6  notes/theory/2026-10-07-call-input-construction-proof.md
4940e031b83d3d0315f17beb51ba2e952ec64ae7d57d9ae0d086024c7305ca9f  notes/design/2026-10-07-original-call-formation-definition.md
20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c  notes/design/2026-10-08-call-source-interface-definition.md
4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e  notes/design/2026-10-07-complete-call-contribution-definition.md
897a7bc108349d9ba8eec905f4490e564f54c71d8df11d7b72ad25016452d6ee  notes/theory/2026-10-11-adopted-invoke-precall-construction.md
45e93da2ef8335ab8cc2dfb1f0ab5c7e17f2bf2430fb20d699a9bdc91c33cdf9  notes/theory/2026-10-11-invoke-complete-call-proof-attempt.md
6d382a248ad7f1c4bbcf7b14231f21448e957640d96b35e7efec333bc019e564  notes/theory/2026-10-10-original-call-reify-constructor-proof.md
0c5c58022c6834651fedff6c14d8cdf96002831c0c2d25292843abbae64d3924  notes/theory/2026-10-09-original-literal-result-owner-extension-candidate.md
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e  notes/design/2026-10-02-typed-computation-core-elaboration.md
93c2bf1c425522fdb41d0f4120d8430597a6091014741a64546e9fedb7bcf79a  notes/design/2026-10-10-simple-sub-legacy-withdrawal.md
6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073  notes/progress/2026-10-06-source-call-generation-construction.md
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35  crates/yu-solver/src/candidate_call.rs
230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6  crates/yu-solver/src/shadow_apply.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
394c763e5b4e2de6ae692ffacf22c07db8958f00129a47f1332f238c9a8eb5eb  crates/yu-core/src/shadow_call_formation.rs
```
