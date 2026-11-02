# R225 constructive proof handoff — source-to-interface input missing

Date: 2026-11-02. Worker: `/root/r225_source_contextual_proof`, registered
`lean_prover`. Contract SHA-256:
`4d5cea5c80080f4fbe196ca7cba7312bfb88986b8736673388ddfa143ab913a8`.

**Outcome: incomplete source-construction stop. No Lean module or theorem was
constructed; no original App premise was discharged; parent-premise delta 0.**
Roots remain 0/4 and packages 0/5. This report is source inspection, awaiting
independent review. It is neither a counterexample nor an impossibility proof.

## Original claim and source authority

The original parent is
`YulangClosure.SourceProblem.InferenceSoundness`, `Contracts.lean:128`:

```text
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

This is its source-inspected proposition definition, not a checker-printed
theorem. The same `e` must satisfy both conclusions at the original source
scope and solution. `SourceScopedCoverage`, `PrincipalCoverage` and
`InferenceTermination`, in the same namespace at lines 133–154, are unchanged.

The original occurrence-qualified preservation claim is
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5,
with the birth-level correction in
`notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. That correction
does not supply a source Function interface or eliminate source dependencies.
The original source inventory is `docs/yulang-source-type-safety-ja.tex`,
`sec:source` and `sec:all-source`, particularly its App/Lambda rows at
281–283. Its opening notice calls it an unreviewed research manuscript; its
local boundary wording cannot override the selected joint Function semantics.
The adopted SG construction is
`notes/theory/2026-10-08-source-generalize-definition-and-proof.md`
§§3.1–3.3,4: actual role, entry, receipt, designated Force, Return/rebind,
body consumer, and complete Call remain separate required source facts.

The governing correction is callback delivery §§1–3, especially normative B
in §2.1: acquire the already instantiated `F_cb` and original `β, Slots(β)`,
deliver the expected boundary before body constraints, select receiver
Handler role, independently determine parameter entry, synthesize the literal
interface, and check one `F_lit <: F_cb`. The literal endpoints cannot be
copied from `F_cb`. Compatibility boundary §8 explicitly leaves complete
interface formation and annotation/callback overlap open. Its later
"Candidate source owner for callback contextualization" identifies a preceding
source-to-resolved-interface input obligation. The role-elaboration draft is
a locator, not authority to select the absent equations.

## Construction attempt and first missing equation

The intended source-directed recursion at an original App would have to perform
these operations, in this order:

```text
original callee source + original declaration/annotation inputs
  -> source-use instantiation of a callable interface
  -> that interface's Function-valued formal and original callback slot/profile
  -> check the original argument with that expected boundary before its body
  -> construct the literal's own complete interface
  -> register the same interface/descriptor at the original App consumer
```

The **first missing equation** is the source-to-interface instantiation and
formal/slot projection, before argument checking can start. Stable locator:
**R225-SOURCE-INTERFACE-ACQUISITION-1**, owned by Luna's source
declaration/annotation-to-interface elaboration integration. The second missing
equation is **R225-PREBODY-EXPECTED-BOUNDARY-1**, owned by source App checking
and Lambda elaboration. These refine the existing R224 seam rather than
discharge any part of it.

The failure is concrete in the existing definitions:

| Definition and location | Available input/output | Missing construction |
| --- | --- | --- |
| `YulangClosure.OriginalSource.Declaration`, `.Annotation`, `OriginalSourceSyntax.lean:22–23` | Both are `Nat` identifiers retaining source identity. | No declaration/annotation syntax table or interpretation resolving an ID to a complete Function scheme/interface. The original tables are referred to in comments, not constructed here. |
| `.Formal`, `.Formal.entry`, `:31–39` | Optional annotation ID and `outerComputation`; `entry` chooses Value or Computation. | A receiver-role or expected callback-boundary constructor. Parameter entry cannot supply either. |
| `.Binding`, `.Context`, `.lookupBinding`, `:188–205` | Name, owner, kind, component, optional annotation/entry and single-use flag; lexical lookup. | A callable scheme, its use-site instantiation, a Function-valued formal, or original slot profile. Lexical lookup alone is not formal acquisition. |
| `.Definition`, `:423` | Original declaration identity, anchor, lexical context and raw source expression. | A resolved complete interface or an algorithm deriving it. It also is not an input to `sourceRules`. |
| `YulangClosure.OriginalSourceInterpretation.Sorts`, `OriginalSourceInterpretation.lean:23` | Arbitrary types `Descriptor` and `Interface`. | Constructor/eliminator equations for source Function interfaces and original callback slots. |
| `.Inputs`, `:324–372` | `valueForm`, `checkedInlet`, actual provider, complete challenge/observation/Force fields. | A source declaration/annotation resolver or source-use instantiator. `checkedInlet` consumes an existing descriptor and returns an abstract interface; it does not acquire `F_cb, β, Slots(β)` from source. |
| `YulangClosure.OriginalSourceChecking.Reading`, `OriginalSourceChecking.lean:747` | Environment/mode/site/context/endpoint/probe to a positive formula. | A callable-formal projection. Formula readout is downstream interpretation, not source synthesis. |
| `.FunctionShape`, `:823–839` | A finite proof indexed by existing endpoint goals and independently admitted invocations. | A source interface constructor. Taking this proof as acquisition would assume the required registration/readback. |
| `YulangClosure.OriginalSourceCallerSchema.CallerTable`, `OriginalSourceCallerSchema.lean:68–89` | Raw module text and import/export/use locators. | A translation into a typed Function boundary; its stated scope explicitly excludes construction of an `OriginalSource.Binding`. |

This establishes an absent constructor/equation in the selected formalization,
not that Yulang declarations can never determine their interfaces. In
particular an immutable original annotation/declaration syntax input is
different from supplying the desired resolved `F_cb` as a theorem hypothesis.
The former still needs a concrete representation and resolving/instantiating
equations. No such representation or equations were chosen locally.

The generic kernel cannot fill this gap. Its `atom`, `admitted`,
`primitiveCheck`, `structuralShape`, `functionShape`, `boundaryTag`,
`conversion` and `checkingAdmitted` fields (`OriginalSourceGeneration.lean:670`)
are local predicates. Assuming a suitable predicate holds does not construct
the missing source interface. `generated_constraints_imply_source_judgment`
at `:1026` reconstructs the original finite rule grammar from satisfaction
under that kernel; it does not synthesize the concrete local interpretation.

## Unchanged App consumer and failed application

At `OriginalSourceGeneration.lean:111–123`, the original App under one
`.viewLogic` binder retains descriptor formation, whole-argument compatibility,
complete-call certificate, source incidence and callable-image atoms. Its
argument child is exactly:

```text
sourceRules context argument
```

Its callee child is independently `sourceRules context callee`. The existing
`YulangClosure.OriginalSourceChecking.generated_application_ports`
(`OriginalSourceChecking.lean:941`) records this exact tree equation, including
both children and the original endpoints. It contains no expected-boundary
input, selected callback profile or pre-body delivery equation.

Lambda generation at `OriginalSourceGeneration.lean:132–169` extends context
with the original `formal.annotation`, `formal.entry` and single-use flag.
The `.sourceFormalRole` atom carries the annotation ID and parameter entry;
no selected receiver role or callback-boundary field is constructed. Body
generation is `sourceRules bodyContext body` at `:153`. The private
`annotated` wrapper at `:35` places a final written-target boundary around the
constructed body tree. This is not the required role-selecting delivery before
literal body generation.

The unchanged named downstream consumer remains **R224-App-descriptorFormation**.
For `.app mark callee argument`, at the same extended call environment it is:

```text
kernel.atom envCall
  (YulangClosure.OriginalSource.atom .descriptorFormation mark.site context
    [callee.site, argument.site])
```

The associated Value goal remains:

```text
⟨.value, mark.site, context,
  ⟨callee.site, .returnedValue⟩, ⟨mark.site, .descriptor⟩⟩
```

The Computation goal still compares App `callableImage` with App `synthesis`.
`generated_application_checking` at `OriginalSourceChecking.lean:956` and
`generated_application_value_action` at `:1269` extract/action an already
satisfied generated check; they do not derive the missing source interface or
expected-boundary delivery. No result from this packet can be applied to
discharge this descriptor atom, the Value goal, or the original parent. No
conditional theorem assuming these facts was added.

## Scope and preserved obligations

Callback delivery §2 explicitly assumes a known, already instantiated formal
and excludes unknown callees, annotation/callback overlap, import/member
resolution and general acceptance. R225 cannot promote that bounded assumption
to acquisition for every supported source. Top-level principles §1.1 also
requires ordinary unknown types to remain variables constrained by uses;
requiring every inferred callee's final type before generating constraints
would need justification, not follow from this stop. Whether the acquisition
operation retains symbolic constraints or uses a known declared interface
requires an owner-level construction. An overlap rule, if needed, requires its
separately open semantic decision. None was selected here.

Receiver role and parameter entry stay independent. The original Value-entry
tree retains receipt before the Return/rebind event and the shared pattern/body
tree. The semantic obligation is still the complete
`receipt; Force(D) >>= (v => B(v))`, including pending/divergent argument
behavior and every reached body observation. Retained Computation entry has
its distinct consumer behavior. Tree order alone does not prove those local
semantic atoms.

Every future bridge must preserve the same actual provider, receipt, world,
assignment and coupled `ν,K,D`, all Call/effect/readout obligations and the
selected mixed-row receipt. No independent effect-port comparisons,
concrete-success transitivity, effect-erased paper type substitute, new
evidence carrier or replacement source typing was introduced. All original
13 expression, 11 pattern, 3 statement forms and their containers, optional
records, methods, annotations and source scopes remain in the parent domain.
There is no delivered theorem representing a smaller fragment.

## Authentication and execution evidence

All 13 explicit contract pins matched a read-only Python SHA-256 comparison
at intake. These are the five governing authority/locator files, six original
Lean modules, and R224 R2 contract/handoff; the source-role draft is counted
with the authority group. The individual authenticated hashes are exactly
those in the R225 contract. The comparison immediately before freeze also
matched all 13 pins and confirmed the leased Lean module remains absent.
The R224 outcome reviewed the exact R224 handoff and is SHA-256
`a71cf89037bd805b7709747d7a8a1966d18bdb87fb73e96aed7d7abe1ed2db5e`.

Supplementary sources read and hashed:

| Source | SHA-256 |
| --- | --- |
| SG construction | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| Source manuscript | `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166` |
| Original preservation claim | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| Birth-level correction | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |
| Top-level principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |

Read `lean-toolchain` = `leanprover/lean4:v4.35.0`, project args = `-j1
-M1024`, manifest packages = empty. Actual Lean/Lake versions were **NOT RUN**.
The packet assigns all verification/cache writes to Luna and expressly
prohibits this leaf from Lean/Lake/checker execution before a concrete frozen
module. No such module was obtained, so no execution was requested or needed.
Source commands were `cat`, focused `sed`, `rg`, and read-only Python SHA-256
comparison; all returned exit 0. No actual Lean goal or mathematical checker
failure was observed. These reads are not kernel evidence.

Delivered theorem names/types: **none**. `#check`, `#print axioms`, build,
bundled checker: **NOT RUN / no delivered declaration**. There is no empty
axiom-list or checker-acceptance claim. No `sorry`, `admit`, axiom, checker
bypass or stronger theorem premise was written.

## Handoff and cessation

Only this assigned handoff was created. The leased
`notes/theory/lean/YulangClosure/SourceContextualElaborationR225.lean` remains
absent; no scratch, generated, cache or build output exists from this worker.
Zero Lean/Lake/Cargo/test processes, zero Astra, no children/background service,
no Git mutations. No separate elapsed-time counter was instrumented; the leaf
stopped at the concrete source-construction obstruction within its 3,600-second
bound. Model/effort telemetry remains UNKNOWN.

The exact seam was sent to Luna, who requested this frozen handoff and stop.
The next necessary input is an owner-authenticated source-to-interface
representation and resolving/instantiating equations, followed by a source App
checking equation that delivers the same original formal/slot boundary before
body generation. Reissuing this proof target with unchanged source constructors
does not remove that prerequisite. No permission, implementation, scheduling,
review, status or Git decision is made by this leaf. **Writes stop after the
final authentication/hash receipt.**
