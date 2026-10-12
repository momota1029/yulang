# Plain App: scalar projection and the first complete-demand map

Date: 2026-10-12
Status: reviewed research-only source audit; no parent theorem closure
Baseline assigned by primary: `4ae7ac4659312ba3c0f214b9c8697cc2af64ea56`,
branch `research/simple-sub-intrusion`
Producer: researcher leaf `/root/app_projection_falsifier`; no delegation
Exclusive lease: this file only
Method/budget: static source reads and manual relation comparison; zero builds,
tests, executable inference, semantic implementation or Git operations
Requested/effective model and effort: runtime metadata unavailable
Independent review: `compiler_referee`, no findings, 2026-10-12; parent theorem
remains OPEN

## 1. Objective and bounded result

Test the proposed joint correspondence for the unchanged source fragment

```yulang
my invoke f = f 1
```

The [approved follow-up account](2026-10-12-fg-call-c-endpoint-construction.md)
§7 separates unsolved complete-argument clause formation from the native
projection `Int <: s <: Int`, `alpha <: Function(s,r)` and its effect ports.
This audit asks whether the actual constructors supply the joint map between
those objects, with the original complete fields and quantifiers retained.

**Result:** no source-qualified counterexample was established. The inspected
native constructors supply the scalar/effect demand and source coordinates;
the selected source emitter can form the same scoped whole-argument predicate
using an independently formed complete demand. Their connection is still an
unconstructed map. After granting §7's authentic child/registration/scope
inputs, its first missing checking dependency is

```text
native Function^-(s^+,ae^+,e^-,r^-)
    -- joint source construction/readout law not supplied -->
complete F_c and CarrierContract(F_c) at the original Call scope.
```

This is a bounded correspondence obstruction. It is neither a proof that such
a law is impossible nor a claim that the complete source clause cannot be
emitted before solving. The parent soundness, required principality, complete
Call, effect hygiene, progress, termination and cutover gates remain OPEN.

## 2. Governing inputs and explicit hypotheses

Use the primary's §7 account and its original source fragment. The governing
selections are:

- Top-level inference principles §§1–3: native mathematical generation and
  proof before dependent implementation; no typing search or special-case
  satisfiability requirement.
- Inferred Function call views §§1.1–3,5: one original joint `xi=(nu,K,D)`,
  source-owned scope/incidence, actual role preservation and Q-independent
  formation. An unannotated protected seed is not an empty effect row.
- Native literal Call checking §§1–3, selected construction §§3–4: authentic
  registered complete `DataArg` readouts and unsolved original emission. Its
  satisfaction theorem has the actual native id/Int inlet as a premise;
  it supplies no arbitrary-demand readout theorem.
- Reify construction direction: preserve the old registry/image, tagged new
  registration, suspension attachment and distinct source-owned `J_lit`.
  No arbitrary old-image identification or complete App theorem follows.
- Contextual Function membership §§2–3: the same actual provider accepts each
  complete independently admitted challenge; preserve pending and future
  observations and original guards.
- Source-interface definition §§2–4 and selected Theorem IF §§3–6: complete
  declaration/reference interfaces and their actual contextual placement.
  Their input clauses and lawful substitutions remain genuine inputs.

For the comparison below, grant exactly §7's authentic pre-Call declaration
graph, literal child/code and reference derivations, registrations,
complete-view readouts, original scopes and independent descriptor meanings.
These hypotheses are not derived from candidate scalar success. Retain all
original alternatives and independent context/world/authority inputs; do not
choose their missing fields to make the tested check succeed or fail.

## 3. Native and candidate constructors

Original external `Typer.scala:48–83,115–117,166–188,200–207` gives a direct
native derivation for `let invoke = lambda f. f 1 in invoke`:

1. The ordinary let RHS is typed at level 1. Lambda allocates `alpha` there;
   `Var(f)` returns that same monomorphic variable.
2. `Lit(1)` is the primitive Int at level 0. App allocates `r` at level 1 and
   calls `constrain(alpha,Function(Int,r))`.
3. Demand level is 1, so the ordinary upper-bound case records the demand in
   `U(alpha)`. There is no crossing or extrusion pair.
4. Lambda returns `Function(alpha,r)`. Publication/freshening copies the
   relationally connected variables with the shared memo, retaining the
   copied upper bound. It creates no complete carrier/provider interface.

This native implementation has two Function fields, no effect representation,
and no selected Yulang provider/alternative/world contract. It is independent
evidence for these native transitions only.

The candidate has a separately inspectable constructor chain:

| Owner | Actual output | Boundary |
| --- | --- | --- |
| `candidate_source.rs:336–348`, literal Finish | Value bounds `Int^+ <: s^-`, `s^+ <: Int^-`; effect bounds Bottom into argument effect and argument effect into Empty | Actual occurrence rows; no argument reify registration or complete `DataArg` relation is output here |
| `candidate_source.rs:394–413`, Apply Finish | `CandidateRelation::Apply`; `ApplySourceInput` retaining child indices, source level, ports, checking occurrence/cause and formal-use route | `native=None`; no complete `F_c` field |
| `shadow_apply.rs:1312–1400`, `admit_candidate_fact` | Validates recipe/source incidence; allocates invocation effect `e`; constructs negative Function with argument, argument effect, invocation effect and result ports; stores `NativeInterface` | Its `demand` is a native `Term`, with no complete carrier-contract readout |
| `shadow_apply.rs:1426–1446` | Callee evaluation effect and invocation effect flow into application effect | These effect inequalities do not identify receiver phases or future/provider fields |
| `candidate_call.rs:285–429`, observation | Checks original HIR ownership, scope ownership, source-child incidence, four Function ports and formal registration route | Validation consumes existing native fields; it produces no complete descriptor or argument membership proof |

Thus the local native constraint record is, with the original signed ports,

```text
Int^+ <: s^-;  s^+ <: Int^-;
EffectBottom^+ <: ae^-; ae^+ <: EmptyEffect^-;
alpha^+ <: Function^-(s^+,ae^+,e^-,r^-);
callee_eval_effect^+ <: application_effect^-;
e^+ <: application_effect^-.
```

Names and any surrounding source constraints remain at their actual scopes;
this is a local inventory, not the full generated relation. Erasing effects
gives the recorded scalar projection. No premise here says invocation effect
`e` is empty. No equality with a complete Call result is inferred.

The limitation is also explicit in the artifact interface:
`OriginalGenCall0Input::CompleteDemand` remains a required input and
`PendingCallConstruction::suppliers` (`candidate_call.rs:218–244`) retains
`OriginalGenCall0`, `ArgumentReifyAndWholeCarrier`, and
`ReceiverDispatchAndCompleteResultFutureInterfaces`. `shadow_apply.rs:9–52`
keeps Application typing, complete interpretation, provider compatibility
and source admission unresolved. This corroborates the inspected constructor
boundary; those labels alone would not establish a repository-wide absence.

## 4. What the authorized source constructor does supply

Initial-context construction §4.4 allocates one dependent complete Function
variable at the original resolved callee/root scope and emits
`WholeArgCompatible(Result(I_a),CarrierContract(F_c);xi,e_arg)`, together
with its original WF, callee inclusion, ReceiveSchema and complete result
constraints. It explicitly permits unsatisfiable generated clauses.

The selected literal specialization (native id whole-argument construction
§4.2) emits the same original predicate head with
`J_check=DataArg(Int,o_arg)`. It requires authentic forward children,
registration, one complete demand and Function-elimination/ReceiveSchema
source incidence. DataArg's complete field readouts are fixed by that
registration, including its licensed alternatives; they cannot be freely
changed in a countermodel. With these genuine premises, it yields the same
scoped argument clause considered in §7. Satisfaction of that clause is not
a formation premise.

This provides a source-side formation route for the checking relation. It
does not provide an equation or scoped map from the candidate's four-port
native demand to that complete `F_c`. A freshly allocated complete variable
and a freshly allocated native variable cannot be related by name, arrow
shape or matching Int ports alone. The source-call generation construction
§§4.2,5 has the same allocation/formation distinction; its completed source
case is the nested Name/Name component, not a general candidate App bridge.

Code-Call (input construction §3.4) bundles authentic Application/Gen-Call,
Reify, operand-check origins and original complete result/suffix interfaces.
It consumes these inputs without deriving them from the scalar graph.
Theorem IF places a supplied complete checking clause and its original
alternatives through source slots; IF-Insert/IF-Use preserve their full
typed substitutions. They do not construct the absent native-to-complete
readout. No authorized constructor inspected here supplies that joint law.

The first missing dependency is therefore already the checking target's
whole carrier relation. Its downstream fields must stay dependent on the
same source tuple: actual provider/current world and entry, complete Call
result, pending suffix/raw resumption, returned-provider future relations,
and every original W/Z arm at its original insertion/reference. Equal scalar
payload/effect ports establish none of those dependencies. Their meanings
remain fixed by the selected source contracts.

## 5. Falsification classes and the minimized stop

**A — only listed premises.** A bare reduct containing the scalar/effect
inequalities and an unsolved predicate-formation occurrence does not contain
a premise connecting its native demand with `CarrierContract(F_c)`. Giving
that omitted connection an arbitrary truth value would test this reduced
logical signature only. No pair of complete authority-consistent semantic
models was constructed here; no carrier, guard, provider or alternative field
was assigned freely. Such a signature extension would not be a source
counterexample and would not discriminate the original joint-map theorem.

**B — legitimate original derivation.** The original Scala derivation in §3
is genuine for the native two-port calculus. The selected source clause in
§4 is a legitimate conditional formation instance on its authentic inputs.
Neither establishes a complete Yulang typing derivation or a satisfying
arbitrary inferred `F_c` for the source fragment.

**C — source-qualified parent counterexample.** None was found. In particular,
the absence of a constructor bridge is not source rejection; a candidate
conflict would not establish source rejection either. This audit does not
refute the existence of a uniform scoped elaboration that retains provider
parameters and all original alternatives.

The minimized stop is one App and one literal, with no recursion, extrusion,
quotient, second use or extra annotation. Native construction succeeds
locally, authentic literal argument formation is available conditionally,
and the first demand readout map remains unsupported in the inspected chain.
Adding extrusion examples or larger toy searches would leave this premise
untouched.

## 6. Exact next proof dependency

Recommend one constructive App-owner law: from the actual source children,
registration and original scopes, construct one complete `F_c` and its
source-checking clauses jointly with the native coordinates
`alpha,s,ae,e,r`. Supply a lawful whole-tuple map whose projections give the
recorded constraints and whose complete checking readout is exactly
`CarrierContract(F_c)`; retain same-value representation, alternatives,
effects/protection, provider/result/future dependencies and rejection.

Specify which direction is required at each consumer. Forward preservation
of a complete source assignment does not alone prove that each native
solution extends to a complete assignment, or reflection of source rejection
or principal coverage. Those remain separate original obligations. The
minimum new evidence is the complete-demand/registered-inlet readout law at
the owning App, before any downstream Generalize transport or C/B quotient.

## 7. Checks, coverage and dependency snapshot

Checks performed: static `cat`, bounded `sed`/`rg` source reads, manual
constructor substitution, SHA-256 byte capture and a static artifact check
for trailing whitespace/final newline. Final scoped artifact reread checked
the sole leased output and its claim boundaries; it is producer inspection,
not independent review. No executable semantic
oracle or finite checker was run. Original Scala and Rust are independently
read implementations, but share the supplied scalar-transition comparison;
Scala validates no Yulang complete-field semantics. Seeds/ranges/mutations:
none. One literal/App shape only; no claimed exhaustive source search.

Several initial combined reads truncated; decisive constructor windows were
reread narrowly. Two guessed definition paths and a guessed recipe path were
absent. A broad path-location read encountered inaccessible unrelated `/tmp`
directories; only the located external Scala source was consumed. These
failed/incomplete searches supply no absence evidence.

Resource use: one reasoning leaf, sequential lightweight read/hash commands,
zero builds/tests/probes/measurement samples and zero heavyweight processes.
Wall time, CPU accounting and peak RSS were not instrumented. No child,
model-policy change, user question, Git command or shared-file write occurred.

Baseline is primary-pinned; this packet prohibited Git operations. The bytes
below were read from the shared working tree and externally located reference.
Primary-owned baseline comparison is still required; no unchanged-baseline
claim is made from hashing alone. No dependency was changed by this worker.

```text
eb5ca0a72d2ec274f3c27ad1f50fb9211ec1ba8d5c45b803843e22b286bb2200 notes/theory/2026-10-12-fg-call-c-endpoint-construction.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389 notes/design/2026-10-11-yulang-inference-top-level-principles.md
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1 notes/design/2026-10-05-inferred-function-call-views.md
0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0 notes/design/2026-10-08-contextual-function-membership-definition.md
e65be7638ed616f5a88ce7d7bc5fffa06a07ee634df3649bd83cf0a60410d39b notes/design/2026-10-09-native-literal-call-checking-definition.md
850a6a035d0e4b6ad3be761205d24c51b4b894fcc5e795c4dc30415e529c5a30 notes/design/2026-10-10-call-reify-construction-direction.md
20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c notes/design/2026-10-08-call-source-interface-definition.md
b8bdf720e50bcfab691f70c08fee8cb32fb2b34f3817099faba512378ebdcb24 notes/theory/2026-10-09-native-id-original-wholearg-construction.md
f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6 notes/theory/2026-10-07-call-input-construction-proof.md
278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98 notes/theory/2026-10-08-call-source-interface-construction.md
273e8dae447e9997d586fc07abf48883c76b90988c8906094dd428a48339c2e5 notes/theory/2026-10-08-uniform-value-entry-constructor.md
6d382a248ad7f1c4bbcf7b14231f21448e957640d96b35e7efec333bc019e564 notes/theory/2026-10-10-original-call-reify-constructor-proof.md
10e86ed3bac72d91f03c83acf50ed8e8336ab3c3d0df4a90a03cbe4efdc7ef75 notes/progress/2026-10-06-initial-context-source-construction.md
6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073 notes/progress/2026-10-06-source-call-generation-construction.md
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49 crates/yu-solver/src/candidate_source.rs
cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411 crates/yu-solver/src/shadow_apply.rs
79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35 crates/yu-solver/src/candidate_call.rs
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9 /home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala
```

Unverified scope: exact-source parsing/admission/runtime, construction of
all authentic pre-Call inputs, full complete-demand elaboration, all source
paths, generalization/replay/lifecycle, native-to-source reflection,
soundness/principality and independent review.

## Commit packet

- Exact leased path: `notes/theory/2026-10-12-app-call-projection-countermodel.md`.
- Baseline SHA supplied: `4ae7ac4659312ba3c0f214b9c8697cc2af64ea56`;
  baseline-byte comparison remains primary-owned under the no-Git packet.
- Dependency hashes changed by this worker: none; observed hashes above,
  differences from pinned baseline not independently checked.
- Status: frozen unreviewed research-only bounded source audit; no genuine
  source counterexample or theorem closure claimed.
- Checks already run: static rule/constructor reads, manual native derivation,
  dependency-byte SHA-256 capture, artifact whitespace/final-newline check
  and producer scoped reread; no builds/tests or semantic checker.
- Proposed checkpoint message: `research: locate plain App complete-demand projection gap`.
- Shared-record delta intentionally deferred: record the App demand-to-
  `CarrierContract(F_c)` correspondence as the next source/proof dependency;
  preserve authorized unsolved literal emission and original parent gates.

Writes stop before submission for independent frozen review.
