# Goal-indexed checking admission interface — independent core review

## Verdict

**ACCEPT — frozen generic core interface only. No material finding.**

This accepts the exact three-source checkpoint frozen at 2026-10-26
14:13:57 UTC: the appended goal-indexed Kernel admission field, its use in
`Checking.function`, explicit legacy wrapper resets, and matching finite
Function proof leaves/shape/soundness plumbing. It does not accept or inspect
the actively authored `OriginalCheckingAdmission` module, concrete target
admission, no-targetReadback applications, future-event FunctionShape
registration, general L4, or whole original inference soundness.

Reviewer: `/root/original_source_review_r4`, independent of author
`/root/checking_semantics_route_r4`. Review activated at 14:15:32 UTC, within
the granted 1200-second bound. Exact repository write lease: this receipt.
Scratch: `/workspace/scratch/f98087c7ac1a/checking-admission-interface-review-r4/`.
No producer edits, Git, children, shared status/import/configuration edits, or
active author-cache writes. No Lean/checker invocation was needed: **0/2**
focused bundles used. The audit below is independent inspection and
reconciliation of the frozen author evidence, not a new independent build.

## Exact frozen inputs

| Artifact | SHA-256 |
| --- | --- |
| `OriginalSourceGeneration.lean` | `0f25e53350edf9c452fd3c0f461602437ca2adf979859fda5e2492bcc403ae55` |
| `OriginalSourceEnvironment.lean` | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` |
| `OriginalSourceChecking.lean` | `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6` |
| Author interface handoff | `213130219eccf9e5a4f479222be331b19048477ab83abecda0d6a446cd62b8b1` |
| Author `core-freeze.json` | `0ee7c43a90013ce1d86d928890c6703853c8dca975e424fda0f31e27faa2786e` |
| Complete core census | `627818c2aab6fbc4eaf2dc7267bf48fbeddd5603701a2590188e4a1d3efbd84c` |
| Core audit source | `5fde10576ca05c961514553e1da98c7712c31316ac662de9190213f82bcf722b` |
| Exact change patch | `ea00b39a9bcca7e214680808fd29e5b006004d99e0bdbeb358b9dd3c023eca63` |

All **16 pinned entries** (three repository sources, twelve immutable core
artifacts and the handoff) were hashed and copied into reviewer-owned
`evidence/`. Rechecks found no drift. The author core-freeze copies, not the
active new module or main mutable build cache, were used as code evidence.

The reviewer independently regenerated the entire patch from the exact
previous sources, obtaining byte-for-byte equality with `changes.patch`:

- Generation predecessor `ab37f3739d89dff9e7918fb745f5a308a3e597ab4aaa9e5a172fcacaeddabf0b`;
- Environment predecessor `971f67a932a663981bc7f72eaeb818d558c4ab65ed7580057c2f0b2cfeb11f07`;
- Checking predecessor `ed011e4c35e889b13bfe2757271570b683ae06b07b3ed520f7bb8436d4faacef`.

All six changed-source copies in the immutable check2/check3 snapshots match
the frozen final source hashes. Every one of the **32 snapshot-manifest
entries** was separately rehashed. The initial input manifest intentionally
records pre-change source hashes; it is not misrepresented as the final
three-source snapshot. Both baseline and current evidence remain preserved.

## Governing source and mathematical correspondence

Authority remains the adopted
`notes/design/2026-10-08-source-generalize-definition.md` §2 and selected
`notes/theory/2026-10-08-source-generalize-definition-and-proof.md` §§3–5.

SG §3.2(4) requires the same actual callable, the independently defined
checked domain, contravariant domain checking, and covariant observation
transport for every checked challenge. SG §3.2(1) allows finite intermediate
inclusion proofs on the same operand tuple. The old binder-only interface
could not identify a different intermediate checked target. The new field
adds the required enclosing CheckGoal argument without changing the source
binder interface or introducing an inclusion-oracle leaf.

SG §3.4 requires one scoped environment/strategy for joint uses, unchanged
actual event operands, and original Shared/publication identities. The
frozen patch does not modify those constructions. The source-domain and
checking-domain distinction is explicit; it does not form the independent
source challenge by assuming body safety or a successful comparison.

The actual new field is:

```lean
checkingAdmitted : Environment Value → CheckGoal → Binder → ScopedValue Value → Prop :=
  fun environment _ binder candidate => admitted environment binder candidate
```

It is the eighth field. All seven original fields remain with their
original types. The compiled `Kernel.mk`, projection and generated
`Kernel.checkingAdmitted._default` types were inspected; the default depends
on the original admission function and has no axiom dependencies.

Only the finite Function constructor's observation telescope changes:

```lean
observationProof : ∀ value,
  kernel.checkingAdmitted environment goal challenge value →
    Checking kernel (environment.extend challenge value) observation
```

This is the enclosing Function `goal`, not its domain child or observation
child. It keeps the same environment, binder, raw candidate and extension.
`Checking.identity`, `primitive`, `compose`, `structural`, the recursive
`Checkings` relation, direct actual `Boundary` conversion, and all mode/child
incidence fields are unchanged. The generic field itself is not yet a
concrete interpretation of the original target's D_F; that belongs to the
separate active module and is excluded from this acceptance.

## Conservation and wrapper audit

The exhaustive independent diff establishes byte preservation of
`sourceRules`, `clientRules`, raw source grammar/data, `Formula`, `compile`,
`compileForest`, all source `Judgment` quantifier/execution/Shared admissions,
and corresponding `Satisfies` clauses. Every such source admission still
uses `kernel.admitted`. The original initializer-entry/replay split,
publication/alias operations, Shared witness strategy, binder arity,
`ActualEvent`/event-path computation, runtime payloads and source-owned
callable registry are unchanged.

This is conservation of source admissions and representation. It is not a
claim that arbitrary old and new source judgments are equivalent after
intentionally correcting their local Checking semantics. The author handoff
makes that distinction correctly.

| Wrapper | Exact field behavior |
| --- | --- |
| `OriginalSourceEnvironment.admissionKernel` | Sets source `admitted` to the existing concrete `Admitted`; explicitly sets `checkingAdmitted` to that same legacy predicate while ignoring goal. Every other field is copied. |
| `OriginalSourceEnvironment.functionKernel` | Performs the same two explicit admission settings and sets the existing Environment FunctionShape. All other fields are copied. |
| `OriginalSourceInterpretation.literalKernel` / `nameKernel` | Update only atom; both admission fields and all other fields are copied. |
| `OriginalSourceEnvironment.foldedLiteralKernel` / `foldedNameKernel` | Update only atom; both admission fields and all other fields are copied. |
| `OriginalSourceChecking.kernel` | Updates exactly primitiveCheck, structuralShape and functionShape; preserves both admission fields. The new FunctionShape is parameterized by `original.checkingAdmitted`, which is definitionally the preserved final field. |

The two legacy resets are necessary because a Lean record update copies a
stored field rather than recomputing its constructor default. The new
concrete override must be applied after those legacy wrappers. This
checkpoint does not claim that the wrappers commute or prove the final
concrete composition order; the author explicitly assigns that work to the
separate new module.

The existing Environment `function_checking_constructor` continues to use
legacy admission through its now-explicit wrapper. Its `targetReadback`,
semantic child hypotheses, original view/event equations, source FunctionAt,
and target guards/captures remain present. Its proof is valid for that
conditional legacy scope. This patch does not silently reinterpret it as a
no-targetReadback theorem.

## Enclosing-goal proof leaves and soundness

`OriginalSourceChecking.FunctionLeaves` now takes
`Environment → CheckGoal → Binder → ScopedValue → Prop`, retains `goal`
alongside `domain`, `binder` and `observation`, and makes its observation leaf
require `admitted environment goal binder candidate`. The domain leaf still
reads only the original domain child. Neither child changes its actual
endpoint readout or scoped environment.

`FunctionShape.proof` uses that exact indexed leaf relation. Its same-value,
contravariant/covariant endpoint and context fields are unchanged. Its
certificate is still finite `Proof` syntax, not a supplied GoalMeaning or
Function/body-membership oracle.

`function_sound` consumes the observation IH at
`original.checkingAdmitted environment goal binder candidate`. The actual
mutual `Checking.rec` application passes the recursive observation IH from
the same constructor, using the copied field of the constructed checking
kernel. No conversion to `original.admitted`, no target-equality assumption,
and no domain inclusion oracle is added to this generic induction.
The identity, primitive, composition, structural and list branches remain
unchanged. `Proof.sound`, the selected completed Meaning interpretation,
guard registration, and the previously explicit source/native registrations
are not strengthened or silently discharged.

This supplies the precise generic interface needed by the next target-domain
construction. It does not itself supply a correct concrete admission or a
new original source FunctionShape registration.

## Full originating audit and actual verification evidence

The frozen audit uses Lean's originating module index, includes all private
and generated constants, rejects project axioms, prints every full explicit
type and `#print axioms`, and checks the standard-axiom allowance with
`collectAxioms`. It also requires all 152 existing authored root names to
remain theorem constants. The reviewer additionally checked that every one
of those names occurs in the originating type/axiom inventory, rather than
merely elsewhere in the imported environment.

| Origin | Complete unique type/axiom pairs | Theorem constants |
| --- | ---: | ---: |
| OriginalSourceGeneration | 819 | 355 |
| OriginalSourceEnvironment | 753 | 289 |
| OriginalSourceChecking | 827 | 299 |
| Total | **2399** | **943** |

All 2399 BEGIN/END pairs match uniquely. All 2399 normalized per-constant
axiom records match the independent line-by-line log parser. All **152
existing authored root names** have current complete type/axiom pairs. The
actual axiom union is **`propext`, `Quot.sound`, `Classical.choice`**. No
project axiom, `sorryAx`, warning, error or skipped-kernel mechanism appears
in the accepted audit evidence or changed source. The source search for
`sorry`, `admit`, project `axiom`, `unsafe`, `native_decide` and
`skipKernelTC` had no match in the three frozen sources.

Author check2 compiled the core and `OriginalEffectHygiene` import cone with
exit0 and no diagnostics. Author check3 completed the full census with exit0,
no diagnostics and no stop reason. Their reported peak process-group RSS is
1,045,123,072 bytes and 1,197,707,264 bytes respectively, within the assigned
1280 MiB bound. The logged native versions are Lake 5.0.0-src+eb6cafb and
Lean 4.35.0 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
The census command explicitly uses `-j1 -M1024`; the owned project configuration
and author ledger retain the one-CPU/thread and 120-second limits.

There was no core author failure in checks1–3, and no reviewer checker was
started. No optional rerun was needed: the exact small diff, complete census,
source correspondence and immutable compiled snapshots resolved the concrete
interface risks. This is not a claim of a new independent build, a check of
the active module, or a combined shared-default-target integration run.

Reviewer evidence includes the copied complete log, independently reproduced
patch, verified predecessor sources, both snapshot manifests,
`census-and-diff-review.json`, and `evidence/reviewed-types-and-axioms.txt`.
The latter contains all 152 current root types plus critical new/generated
interface types; SHA-256:
`169e4544cda3af2886bc7d58f4f73d19fff80c33822a15921413062d555cc4c2`.
The complete all-originating log remains the authoritative exhaustive list.

## Parent application, residuals and stop

The accepted result is the generic interface and induction correction needed
to instantiate a checked target's independent domain at each Function node.
Original source admissions and shared runtime scopes remain intact. Existing
legacy semantic applications remain conditional and valid.

Still excluded and OPEN: concrete goal-domain construction and recovery;
final wrapper-order projections; arbitrary-descriptor input round-trip;
no-targetReadback observation transport and FunctionAt applications; both
directions of the Bool-domain discriminator; full future-event FunctionShape
registration; other original source/client owner meanings; general L4;
authentic native/source registry realization; and whole inference soundness.
Their later code requires a separate fresh frozen review. No source grammar,
Call/effect obligation, quantified challenge or shared-witness parent goal
is narrowed by this acceptance.

**WRITES STOPPED** after this receipt and the reviewer freeze manifest.
No checker, background process or child belongs to this review. Only the
primary may integrate the accepted core or update shared status.
