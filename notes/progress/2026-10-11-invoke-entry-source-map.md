# Actual invoke Parameter/Lambda entry: source correspondence frontier

Date: 2026-10-11
Status: frozen unreviewed research characterization; no theorem closure
Baseline: `1876f777358489d01c9755fa63a8d5876aa729a2`
Lease: this file only
Method: source-owner and local-law correspondence; zero builds or probes
Scope: the actual unannotated formal at `L,d_f` in `my invoke f = f 1`
Excludes: ordinary Int/application row derivation, full Call, principality,
production implementation and new semantic definitions

## 1. Result and governing meaning

The actual source determines one unannotated Value formal, its shared lexical
identity and endpoint, and the entry order before body execution. The current
candidate compiler retains that same formal root and a Lambda-owned entry
effect edge. Those are concrete source/construction facts. They do not supply
the complete typed origin, received-carrier view, receipt and rebind evidence
required by a whole-entry correspondence theorem.

The first unelaborated original static application in the inspected semantic
cone is `ParameterOrigin(L,d_f,Value(A_f),r_f)` together with its original
received-carrier/designated-view port introduction. Call-input §3.2 consumes
these premises; it does not introduce their complete dependent signature.
Typed-core §§6,9 determines their intended role and operational order, while
retaining typed-flow/receipt premises. This is a missing local formation law
at the owning Parameter, before any claim about completed Call.

This gap is present when attempting a **complete typed** direct Build-to-native
entry bridge without any raw registry. It does not refute or block by itself
the narrower value projection: erasure can retain the same value endpoint and
Function skeleton while omitting those entry evidence fields. A theorem about
that erasure must retain its exact scope. The adopted registry adds a separate
requirement to instantiate complete original local declarations at raw `P`;
an unavailable decoder argument would be an additional representation failure,
but none is established here.

Authority is the primary's selected meaning, read through:

- Top-level inference principles §§1–5: ordinary Simple-sub construction,
  genuine proofs and only necessary abnormal-path safety.
- Charter §21 (`:572`): unannotated `f` selects `Value(A_f)`, one designated
  force/rebind inside the same receiver, irrespective of body use or effects.
- Typed-core §6 (`:303`), parameter generation (`:333`) and §9 (`:904`):
  entry/body/result order and separation of `J_arg`, `J_body`, `J_call`.
- Selected Generalize definition §§2–3; its proof §§2–4: actual owning
  constructors, Desc scope before challenges, original local laws L1–L5.
- Call-input construction §3.2 (`:198`) and §3.3 (`:255`): Capture,
  Entry-Value and Data-Lambda with their original premises.
- Adopted registry proposal §§1–2: the raw owner/port/API representation for
  the bounded pre-Call fragment, distinct from authentic original applications.

Typed-core as a whole remains Draft. Its source-role meaning is selected by
charter §21 and the Generalize definition; this note does not adopt its wider
package. No full `Fam_delta[mu_delta]`, `EmittedGenCall0`, synthetic origin,
receipt, Force/rebind or empty entry effect is assumed.

## 2. Actual source introduction, before semantic challenges

Use `L` for this retained source Lambda and `d_f` for its actual parameter
identity; these are locators for existing source records, not new registry
addresses. The structural derivation has the following order.

1. `module.rs::lower_plan`, `:1394–1412`, allocates one
   `HirParameterId(definition_root,ordinal)` from the admitted formal. For this
   single formal the ordinal is zero. `HirParameterId::eq` at `:304` compares
   its owner and ordinal. The public parameter record at `:383` stores its
   id/name/range; it carries no complete entry certificate.
2. `module/local_source.rs::form`, `:286–317`, copies that same id and source
   key into `LocalSourceParameter`. The actual absence of an annotation is
   retained as `annotation: None`. It installs the parameter lexical binding
   before constructing `LocalSourceForm::Lambda {parameter,body}`. The body
   scope is `LocalSourceScope::Parameter(parameter.id)`; the formal's preceding
   source scope is the definition scope. These source scopes are evidence of
   lexical placement, not an implementation of the full dependent type tree.
3. `candidate_source.rs::emit_candidate_source`, `:188–211`, allocates one
   parameter recipe position and `FormalRegistrationInput` linking owner,
   Lambda index, actual parameter id and that position. `:216–220` makes each
   lexical Parameter Name use `CandidateEndpoint::Parameter` of that same
   recipe; `:239–245` retains `FormalNameInput` back to the registration.
4. `candidate_source.rs::initialize_candidate_source_levels`, `:532–560`,
   sets the formal level from its Lambda visit and retains one positive native
   parameter root after checking recipe identity. Later uses borrow that root.
   This root is an actual `Term`, not a `ParameterOrigin` proof or a decoded
   registry bundle.
5. The selected semantic Parameter rule is Generalize proof §3.1 (`:158`
   onward), with owning Desc rule §3.3 (`:237` onward). It introduces one
   flexible `A_f` at `sigma_f` before the invocation challenge, preserving its
   preceding dependency telescope. Charter §21 fixes `Value(A_f)` before
   synthesizing the body. A solved Function shape and actual received witness
   cannot select that outer role or introduce another formal type.

The source's free-binding graph has no lexical captured binding: `f` is its
own formal and `1` is a primitive occurrence. Capture-Lambda at Call-input
`:204–218` therefore gives the Empty lexical capture instance. This does not
remove independent primitive, world, profile or entry laws.

Generic `HirParameter`/`NameResolution` equality is weaker than full handle
identity (`module.rs:403,427`); the candidate observer uses the direct parameter
handle and owner checks. `candidate_call.rs::observe`, `:282` onward, checks
actual Lambda/Name/parameter/source-scope incidence and the retained native
ports. Its success is structural artifact evidence, with pending semantic
suppliers still exposed by `PendingCallConstruction::suppliers`, `:224–247`.

## 3. Entry derivation and exact local-law owners

The source-selected expansion is obtained directly from typed-core §9
(`:928–951`) for `P=Value(A_f)`:

```text
actual receiver activation and source boundary/receipt;
Force_argument(t) >>= (v,C').
    RebindResultPath(t,v,C');
    Run(body f 1 with f := Value(v), C') >>= ReturnFromInvocation
```

This is an ordered symbolic entry/body skeleton. It is not a completed
invocation witness. Construction runs none of it. The actual input `t`,
receipt token, returned `v`, current world and body proof are introduced only
at their original event binders. In particular no result or formal binding
exists merely because receipt or a pending Force exists.

| Required item | Exact owner or law | Actual evidence and frontier |
| --- | --- | --- |
| Shared formal/root | HIR `lower_plan`; LocalSource `form`; candidate parameter recipe and root initialization above; Generalize proof §§3.1,3.3 | Actual identity and shared native endpoint exist. An original typed root/origin/license is a separate semantic field. |
| Value role | Charter §21; typed-core §6 parameter table; Generalize Parameter rule | Unannotated boundary fixes Value before the body. The supplied callable's actual role is not rewritten. |
| Received whole carrier and view | Typed-core §§3,9; Call-input `Entry-Value`, `:230–237` | Whole carrier is received inside the real invocation; Entry-Value requires original `r_in` and its designated typed view. No complete general invocation-port introduction/application for this actual `L,d_f` is supplied by these displays. |
| Receipt | Typed-core §9; source-computation-role §10 (`:578` onward); ordinary computation package §3 (`:157` onward) | Receipt and source boundaries precede Force in the current activation. Typed `Receive` correspondence is a premise; HIR identity and a native root supply no receipt proof. |
| Designated one-layer Force | Typed-core §3 (`:139–147`), §6 and §9; charter §21 | Force uses the existing typed view once. Returning latent data never recursively forces it. Its independent whole carrier contract/consumer law remains necessary. |
| Same-result rebind | Source-computation-role §10 (`:597–609`); ordinary computation §3 (`:166–176`); Call-input Entry-Value | Rebind transports matching result/value paths at the same `nu,K,D`, using the same returned value/provider and `C'`. A Force Return alone is not a typed body binding. |
| Body/return suffix | Typed-core §9 (`:943–967`); Call-input Data-Lambda `:257–279`; ordinary computation §3 | Rebind precedes the entire original body consumer and invocation-return delimiter. Body Result stays distinct from complete Call. The missing body Call is not supplied by this entry derivation. |
| Requests, raw resume and future | Typed-core §9 bind equation; Generalize L5 and Event/EventField/EventProof records; ordinary computation §§2–3 | Preserve request instance/origin, response endpoint, raw handle, actual resumed state, joint dependencies and suffix. No repeated receipt, handler snapshot or revived maker grant. Complete hereditary/future certificates require their independently supplied local laws. |

The first complete application cannot yet be written as a typed constructor
term from just the actual syntax, Desc and native root:

```text
actual L,d_f, Unannotated, preceding source/type-scope dependencies,
Desc(C,d_f,value,sigma_f,Delta_f), Empty lexical Capture,
shared formal endpoint/root and selected Value-entry order
    ? original ParameterOrigin / received-view introduction at these binders
    ? complete receipt / designated Force / same-result rebind port maps
------------------------------------------------------ not established here
authentic Entry-Value and ValueBind at this L,d_f
```

Question marks name the missing formation applications, not fresh witnesses or
new axioms. Their complete ordered input signatures and actual arguments must
come from the original Parameter/entry owners. L2 in Generalize proof (`:91`
onward) requires original constructor laws; citing that requirement does not
provide their instance. L1/L4/L5 similarly keep primitive, initial-world and
future laws independent. This stopping sequent is a minimized **elaboration
obligation**, not a counterexample: the single formal/entry prefix suffices,
before any literal or body-call image. No source rejection follows.

### Existing native inlet evidence and its usable scope

The uniform inlet note §4.1 (`:118` onward) gives the generic owning record
shape `Desc; Intrinsic; ValueInletSchema`. Its §4.2 explicitly retains the
whole carrier, original port map, same-result inclusion, static constraints,
whole-observation constraints and independent current guards; §4.3 and Lemma S
(`:281` onward) supply conditional elimination laws for a **formed** schema
and checked carrier. Those laws do not infer purity or delete production-only
members. This is a real candidate local constructor, not only a field name.

Its §5.1 (`:314` onward) still requires actual source registration, IF0 and
intrinsic incidence, and specifies Pure for its projection case. The selected
native projection definition §2 expressly concerns id/pick projection
formation. The native id whole-argument note §3 uses that actual id
Parameter/IF0 and an explicitly selected empty-residual presentation while
retaining intrinsic guards. Neither supplies the missing actual invoke
formation application or licenses replacing invoke's incident dependencies
by the id tuple. The broader generic record laws may be reused once their
authentic invoke operands are elaborated; this note asserts no impossibility
of that reuse.

## 4. What current native inference retains

`lib.rs::admit_lambda_fact`, `:11233–11261`, reads the actual shared formal
row and actual body endpoint. Candidate mode at `:11267–11338` creates fresh
entry and returned Effect rows at the formal level; Lambda slot 3 links entry
to returned effects and slot 4 links body effects to returned effects. Slot 3
retains Lambda-owned inferred-entry provenance. `:11342` constructs the
positive Function and relates it to the Lambda result component.

This is source evidence that ordinary entry effects are retained even for an
unused formal. It is not the complete relational image required by §9 and
does not establish receipt/Force/rebind typing or exact complete-call effects.
The final Function constraint is emitted after visiting the body; that plan
order is static constraint generation, not evidence that runtime body
execution precedes entry. No eager satisfiability prerequisite is inferred.

The original Simple-sub reference `Typer.scala:62–68` installs one fresh
formal in the environment before typing the body and builds its Function
from that same formal and the body type. It validates the ordinary structural
base for endpoint sharing. It has no Yulang receipt, carrier, protection or
future law. No reference compiler, Oracle or paper experiment was run; the
paper is retained as the primary's selected dependency, not used to prove
these Yulang extensions.

## 5. Protection and future obligations stay active

Function-view Authority §§1.1–4 distinguishes internal provisional protection
from the actual role/entry of the supplied callable. Annotation absence does
not mean empty effects. The directional addendum §§2–4 marks the original
covariant output-effect occurrence of the upper use exposed from protected
`f`; it does not propagate that seed backwards to an existing provider lower.
The seed and use share the formal/root without identifying providers,
occurrences or proof choices. Receipt, live receiver and typed incidence are
still needed to derive event-level protection or capture authority.

Every eventual full entry law must preserve the original complete input
challenge, current guards, response/resumption and output-dependent future
telescopes. It must retain independently licensed alternatives even when no
source execution inhabits one, divergent/pending prefixes without a fabricated
formal result, and latent values returned without further force. No summary
row, native Term, selected empty effect support or successful comparison proves
those facts. These are explicit unverified scope, not additional semantics.

## 6. Direct Build versus adopted raw registry

Generalize proof §4 (`:363` onward) constructs Build from the source rules,
their actual local conjunctions/alternatives and original binder positions.
The direct path needs the original local Parameter/entry application first;
it need not first construct `Seal`, Law rows, decoder ranks or raw-P arguments.
This distinguishes the complete local-law gap from a registry typing gap.

The adopted construction §§4.1–4.2 (`:333–445`, `:509–633`) additionally fixes
`header -> Desc/intrinsic ports -> origin/static licenses -> Entry/ValueBind
-> Register-Parameter -> SharedPositions`. Its source owner permission
eliminates to its exact declaration and scope map; it supplies no original C0,
contribution license or event authority. That interpretation constructs the
new owner case using genuine local port/scope operations and whole Entry
applications. Raw key availability does not provide those applications.

Once a complete direct original application exists, packaging it in the
adopted interpretation needs the ordered typed argument map at the actual raw
P and preceding fields, preserving every original argument, guard and arm.
That additional cut is the existing kernel-conformance note §§3–4. This note
does not rediscover it as the first step of ordinary Simple-sub inference,
assert a late/self decoder dependency, or substitute the registry theorem's
conditional proof for the actual source law.

Recommended next action: elaborate the complete authentic Parameter/received-
view introduction at `L,d_f`, with its receipt/Force/rebind elimination laws
and preceding scope/incidence operands, directly in the selected source
context; only then check its separate raw-P argument map. Keep the narrow
value projection and the full-entry gate distinct.

## 7. Checks, resources and commit packet

Read-only `rg`, `sed`, `cat` and `sha256sum` inspections; one leased note.
No tests, Cargo, compiler execution, Oracle, executable model, mutation,
seed/range enumeration or external process experiment. Inspection commands
completed successfully except a locator search for nonexistent
`crates/yu-infer/src`; actual owners are in `yu-solver`. Bounded searches
are not a whole-repository absence proof. CPU/RSS and exact elapsed time were
not measured; each shell inspection completed in under one second as reported
by the tool, within the assigned 30-minute lane. No child delegation or Git
mutation. Initial read-only HEAD locator confirmed the assigned baseline;
the primary owns the final pinned-revision comparison.

No oracle independence claim: this is direct source/artifact inspection,
sharing the selected semantic laws with the constructive lane. Compiler
structure and original Simple-sub source are separate evidence for structural
sharing, and neither validates Yulang's full semantic entry laws. This
producer has not independently reviewed its own artifact.

Commit packet:

- Exact leased paths: `notes/progress/2026-10-11-invoke-entry-source-map.md`.
- Baseline: `1876f777358489d01c9755fa63a8d5876aa729a2`.
- Review: frozen, unreviewed bounded source characterization.
- Checks: narrow source reads and direct dependency SHA-256 comparison before
  freezing; zero executable checks. Dependency changes during that comparison:
  none. Pinned-HEAD versus working-tree content check remains primary-owned.
- Proposed message: `research: map actual invoke value entry and local-law frontier`.
- Deferred shared deltas: record actual shared formal/native entry provenance;
  keep complete original entry formation OPEN with its precise owner; preserve
  separate raw-registry conformance and value-projection scopes. No task,
  theory-map, design-index, question-board or authority file changed.

### Direct dependency SHA-256 snapshot

```text
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389 notes/design/2026-10-11-yulang-inference-top-level-principles.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed notes/design/2026-09-29-scc-intrusion-redesign-charter.md
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e notes/design/2026-10-02-typed-computation-core-elaboration.md
9a230eb023698666f4c3e518a527009d6915e65f658b230e6da6a29914ca3abb notes/design/2026-10-02-source-computation-role-elaboration.md
ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917 notes/design/2026-10-02-ordinary-computation-semantics-package.md
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1 notes/design/2026-10-05-inferred-function-call-views.md
6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7 notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38 notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240 notes/theory/2026-10-08-source-generalize-definition-and-proof.md
aed6ef63b01f555a5f2804f87a599167c1a30fa999afc0b9d9f11b8ae974a919 notes/design/2026-10-08-native-projection-public-export-definition.md
273e8dae447e9997d586fc07abf48883c76b90988c8906094dd428a48339c2e5 notes/theory/2026-10-08-uniform-value-entry-constructor.md
140c9c907f3ae27120acd84d96c75b2d9a64b437e3e0e71c540c0030864ebb6b notes/theory/2026-10-08-id-public-phase-constructor.md
b8bdf720e50bcfab691f70c08fee8cb32fb2b34f3817099faba512378ebdcb24 notes/theory/2026-10-09-native-id-original-wholearg-construction.md
e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9 notes/design/2026-10-08-native-signature-formation-definition.md
f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6 notes/theory/2026-10-07-call-input-construction-proof.md
2d6439507f01f38234909f98d86b1d2fbe31d3c7dd60d453cf1c199604020451 notes/design/2026-10-10-original-registry-constructor-adoption-proposal.md
9bc209159fee600ed7bc3e389ceef54aeaaa72c7e9f67235e4fc9e2a5c26cfbb notes/theory/2026-10-10-source-owned-original-registry-construction.md
1857e96a4e080b2eeb6f5cf4b50ab946b7baf6052f9380b21de8ea97fb4c43c8 notes/theory/2026-10-10-original-registry-kernel-conformance-attempt.md
943dcab6440ffb70061f08641afa13fa8b36c5689a326d07288b9593e17ba8f5 crates/yu-hir/src/module.rs
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed crates/yu-hir/src/module/local_source.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49 crates/yu-solver/src/candidate_source.rs
79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35 crates/yu-solver/src/candidate_call.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94 crates/yu-solver/src/lib.rs
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9 /home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala
5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698 /home/momota1029/rust/simple-sub-reference-paper.pdf
```
