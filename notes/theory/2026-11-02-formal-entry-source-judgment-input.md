# R172: independent Lambda inputs and the FormalEntry bridge

Status: **SOURCE INPUT MAP; PARENT OPEN; INDEPENDENT REVIEW PENDING**.
This is a static source comparison, not a new theorem, Lean check, source
counterexample, or implementation authorization.

## Fixed parent and authority

R172 contract: `tasks/agent-loop/sprints/formal-entry-source-judgment-input-r172.md`,
SHA-256 `08d2d7d1579ad01a09351d0244d49d6d76bef03d7e7ece44d63ff0341a4c758c`.
Primary-pinned baseline: `yulang3/008c5fd5bdc17b8a253daf9e5d79916a2db404b0`.
The branch/revision is the primary's supplied pin; this worker ran no Git.

The original parent is `YulangClosure.SourceProblem.InferenceSoundness`,
`notes/theory/lean/YulangClosure/Contracts.lean:127`. For the same concrete
`p : SourceProblem S C X E D A N`, it requires

```text
forall s x d a,
  p.supported s -> p.generates s x d -> p.solves d a ->
  exists e, p.sourceJudgment s x e /\ p.sameScoped s x e a.
```

The four outer variables and one shared `e` remain unchanged. The scope is
source type-inference soundness, including inferred effect rows. No claim
about Rust evaluator/machine correctness is needed for this packet.

The semantic authority used here is Source Generalize design §§2–3,
`notes/design/2026-10-08-source-generalize-definition.md`, selecting construction
§§3–5 in `notes/theory/2026-10-08-source-generalize-definition-and-proof.md`.
Construction §2 states the genuine local premises L1–L5; §§3.1–3.3 specify
Parameter, Lambda, checking, annotation formation, original owners and scopes.
The selected annotation correction is
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.1:
contravariant concrete annotations grant local subtraction permission;
they do not close the supplied input-effect row. Covariant concrete atoms
are allowed at their position. Type variables do not count as concrete atoms,
and nested Function polarity composes. These adopted sources, rather than
an unadopted research draft, govern the comparison.

## Independent Lambda premises

Write `F` for the actual formal, `L` for its Lambda, `P` for its original
pattern and `B` for its original body. The native source rule needs the
following inputs before its conclusion can be used as source typing.

| Input | Independent source requirement | Exact frozen Lean representation | Construction evidence and missing bridge |
| --- | --- | --- | --- |
| Formal type and scope | Parameter introduces an ordinary flexible endpoint at its original type scope, before invocation challenges. Written constants, slot identities and annotation permissions remain intrinsic. No formal type may be chosen after seeing an argument. | `YulangClosure.OriginalSource.Formal`, `Formal.entry` (`OriginalSourceSyntax.lean:31–39`); `.existsE <F.site, description, 0>` outside the invocation in `OriginalSource.sourceRules` (`OriginalSourceGeneration.lean:132–168`). Its admission remains `kernel.admitted`; an annotation ID is a `Nat`, not its interpretation. | Collector saves recipe position, role, owner, Lambda index, parameter and scope (`candidate_source.rs:1098–1118`). This gives provenance data. It does not establish the endpoint's original semantic type or admitted description. |
| Formal annotation and entry role | The *outer written annotation* determines Value versus retained Computation entry. Preserve its actual target and local realization evidence. Role cannot be recovered from a solved latent shape. | `Formal.outerComputation` selects `Formal.entry`; `sourceFormalRole` atom carries `F.annotation` and `some F.entry` in the actual formal context. The generic kernel must independently validate that atom. `OriginalFormalShared.entryPremises` repeats this exact shell (`:54`). | Rust role uses `parameter.annotation[..].ty.effects.is_some()` (`candidate_source.rs:1113`). `FormalEntry` copies that Lambda's annotation (`:1323–1327`), while `FormalAnnotation` is a separate action (`:1339`). R171 origin is conditional and needs the prepared-state repair below. No theorem connects this annotation representation to `Formal.outerComputation` or validates the atom's meaning. |
| Complete type interface and captures | Preserve original captures, source entry, body consumer, complete invocation return, source effects, protections, typed paths, and the whole original joint tuple. The body result and invocation result are distinct ports. | Lambda atoms `captureWholeEnvironment`, `closureFormation`; formal context binds the actual formal and entry; body goal is `.computation B.finalRoot L.bodyConsumer`. `OriginalFormalShared.lambdaTree` and `checkedBody` (`:27–73`) calculate the shell from the raw parameter. | A retained registration or scalar effect row supplies only part of this tuple. No inspected definition identifies all these interfaces with the concrete parent's source scope/solution. |
| Computation entry and effect flow | Value entry requires receipt, designated argument Force and actual Return/rebind; retained Computation entry omits that Force and retains the supplied carrier. Independently admitted challenges are fixed without assuming body safety or callee acceptance. | `receiptFormation` plus `entryForceReturnRebind` or `retainedEntry`; `.forallE <L.site, invocation, 0>` then receipt existential. Value uses `.executionE <F.site, returnRebind, 0>`; Computation goes directly to Shared. `OriginalFormalShared.enteredBody`, `value_entry_shared`, `computation_entry_shared` (`:49,148,169`). | Preparation allocates the computation formal's fresh effect at its parameter level and writes `native_root`/`entry_effect` (`candidate_source.rs:2303–2325`). Formal-name use links its effect to the same entry via `candidate_formal_effect_equal` (`:2476–2479`; equality emits two directed constraints, `candidate_effect.rs:1979–1987`). No source interpretation of these emitted constraints has been derived. |
| Pattern and body checking | Check the original pattern under the actual formal binding, then the original body under its pattern bindings. Require `completeBodyConsumer`, `actualReturnOrPendingSuffix`, and finite computation checking at the original ports under one body EventProof witness. | `OriginalSource.sourceRules` Lambda branch and `OriginalFormalShared.checkedBody`. `OriginalSourceClosure.checked_body_consumer` (`:223`) extracts the same pattern/body/check and derives the semantic computation action *from a supplied judgment* and decoding inputs. | `Action::FormalEntry` does not contain the pattern/body derivation or complete computation check. `OriginalSourceClosure.generated_value_body_consumer` / `generated_computation_body_consumer` (`:396,452`) still assume satisfaction of the whole Lambda Build with their supplied interpretation/readout/registry inputs. They cannot generate that satisfaction from the FormalEntry action. |
| Retained entry permission | The actual contravariant annotation grants handling of its resolved concrete atoms at its owned source position, including mixed input effects. Preserve type arguments, scope, owner and original occurrence. This permission is not effect emptiness or an input upper bound. | The selected hygiene policy supplies the meaning. Generic Lambda `retainedEntry` and `sourceFormalRole` are local atoms interpreted by `Kernel.atom`; `OriginalSourceEvents.EntryRegistration` (`:81`) preserves role, receipt, route, telescope, context and entry. Its construction is not a semantic permission proof. | `candidate_formal_entry_annotation` checks the same registered Lambda/recipe/scope, requires prepared `entry_effect`, optionally equates a row variable with it and retains concrete permission fields (`candidate_effect.rs:1990–2066`). `bind_formal_entry_permission_use` / `internal_formal_entry_permission` (`:557,607`) authenticate incidences but require independently supplied native route/owner inputs. Neither gives the original local handling law or parent solution interpretation. |

The annotation on the Lambda *expression* is separate from the annotation on
its formal. `sourceRules`'s `annotated` wrapper (`OriginalSourceGeneration.lean:36`)
requires `finalAnnotationFormation` and a boundary from synthesis to written
target. `OriginalFormalShared.annotation_child` can extract the Lambda child
from a judgment with that wrapper; it does not construct or waive the wrapper's
formation/checking evidence, and does not erase the formal annotation.

The binder order is one description, one view, every independently admitted
invocation, then a receipt for that invocation. Value entry also quantifies over
its admitted actual Return/rebind domain when replay is open. Shared evidence
is installed at its original anchor after receipt (and after Return for Value);
the body EventProof remains under that same event. `Satisfies.sharedE` uses
`environment.anchorValue`, rather than choosing a new witness for each body.
`OriginalSourceEvents.lambdaScope`, `lambdaEntry` and `source_lambda_entry`
(`:126–148`) retain these coordinates. `Joint` (`:262`) is data containing
retained objects and witness fields; it asserts no membership/admission law.

## What the existing source theorem actually consumes

The file `OriginalSourceGeneration.lean` declares namespace
`YulangClosure.OriginalSource`, not `YulangClosure.OriginalSourceGeneration`.
The exact source declaration at lines 1026–1031 is:

```lean
theorem generated_constraints_imply_source_judgment {Value : Type}
    (kernel : Kernel Value) (environment : Environment Value)
    (context : Context) {category : Category} (source : Source category)
    (solved : Satisfies kernel environment (Build context source)) :
    SourceJudgment kernel environment context source :=
  (source_reconstruction kernel environment context source).mp solved
```

Thus the fully qualified name is
`YulangClosure.OriginalSource.generated_constraints_imply_source_judgment`.
This is a transcription of the frozen source, not fresh `#print` output.

`Build = compile (sourceRules context source)` (`:870`). `Satisfies` (`:842`)
interprets every compiled local premise and retains the existential/universal,
execution, Shared, publication and alias structure. `Local` (`:732`) requires
`kernel.atom`, finite `Checking`, or `Boundary`. `Kernel` (`:670`) leaves atom
meaning, original admission, primitive checking, structural/function incidence,
boundary tags and actual conversions as parameters. The checking interpreter
`OriginalSourceChecking.kernel` (`:842`) supplies finite registered checking
constructions but preserves original atom/admission/tag/conversion meanings.
It also requires its `Inputs`, registry, declarations and reading.

Consequently the reconstruction is useful conditional mathematics: it consumes
one satisfying environment for all the independent local rules. It does not
prove that any supplied kernel is the concrete original language, that a Rust
successful trace satisfies that Build, or that an arbitrary annotation ID has
its approved meaning. None of these is established by `Kernel` being a structure,
by proposition definitions, by theorem naming, or by assumed local laws.

## R171 defects retained

1. `FormalEntryOriginR171.newFormal` sets `entry = none` (`:111–114`). Its
   scan-to-action composition requires literal equality of the R169 formals
   with that scan snapshot. The successful nonempty R169 application requires
   the selected entry to be `some port`. The intended newly registered
   successful application is therefore uninhabited under that equality.
   The actual Rust preparation updates the existing registration, so the
   required repair is a projection relation from scanned to prepared formals
   preserving owner/Lambda/parameter/recipe/scope/role/index and retaining the
   successful native-root/entry allocation. The source rule's `.computation`
   tag is not the Rust effect port and cannot repair this equality.
2. `FormalEntryOriginR171.Scan` appends only the Lambda's parameter recipe
   (`:123–134`). Rust appends each record-field recipe immediately afterward
   and rejects a duplicate field binding (`candidate_source.rs:1119–1123`).
   Allocation `Construction.skip` accounts for identity gaps, not recipe writes.
   The actual recipe snapshot and the saved formal recipe indices require
   explicit interleaved append events and successful duplicate handling.
   Generic source record-pattern coverage supplies no vector-index theorem.

These are model-application obstructions, not an established reachable Rust
bug. Record patterns, optional/default fields, annotated and unannotated
formals, computation and Value entry, recursion, captures, method selection,
source annotation boundaries and all admitted effect cases stay in the parent
domain. No new rejection or annotation requirement follows.

## Parent application and first remaining owner

At the concrete FormalEntry composition, the first remaining premise is the
collector/preparation relation in the preceding section, including the
record-field recipe events. Owner: Luna to lease the finite construction repair
and its actual source correspondence; no current R172 worker has that write
lease. The repair must preserve exact origin fields through preparation instead
of strengthening successful-trace hypotheses or deleting the entry requirement.

At the parent theorem's application of the source reconstruction theorem, the
first unavailable input is an independently justified interpretation that turns
the *same* `p.generates s x d` and `p.solves d a` into
`Satisfies K E (Build C S)` for the corresponding supported source/scope, under
the concrete original `K`. It includes every Lambda premise above and all other
constructors. `d` is not definitionally Build, `a` is not definitionally E, and
`p.solves` is not definitionally Satisfies in the frozen inputs. Identifying them
by stipulation would skip the inference soundness argument. Owner: Luna's
source/proof bridge assignment, following the construction repair and source
lane's frozen mapping.

If that interpretation were proved, the existing theorem could supply its
`OriginalSource.SourceJudgment`. A further source interpretation must supply
one `e` with **both** `p.sourceJudgment s x e` and `p.sameScoped s x e a`, retaining
the same formal description, captured/Shared data, original scoped strategy,
effect-row permissions and solution. The theorem does not mention `sameScoped`
and does not build this parent witness. Owner: Luna's source judgment/solution
interpretation. No separately existentially closed per-use or per-challenge
witnesses can replace it. All these obligations remain open.

## Evidence and limits

The exact 16 frozen dependency hashes were checked with `sha256sum` and matched
R172; the manifest is in the paired proof handoff. Reads used `cat`, bounded
`sed -n` and `rg -n` / `rg --files`; successful read/hash commands returned exit 0.
Some large combined tool displays were truncated; relevant sections were then
read with bounded commands. No command failure or mathematical counterexample
was produced. The source-level obstruction is preserved above and in the R171
handoff rather than replaced by an invented success receipt.

Pinned configuration read: `leanprover/lean4:v4.35.0`, package `YulangClosure`,
no external packages, `-j1 -M1024`. Actual Lean/Lake versions, checker exits,
printed theorem types and transitive axiom results: **NOT RUN in R172**, as the
packet explicitly prohibits invocation. No new theorem is delivered, so no
axiom audit is claimed. R171's historic checks remain evidence only at their
frozen handoff/hash and do not become a new R172 check.

Writes: this note and the single paired proof handoff only. Scratch/generated,
cache, build, Cargo, tests, Git, dependencies, descendants and runtime-path
inspection: none. Resource use: lightweight bounded reads/hashes and two
Markdown writes; process RSS and whole assignment wall time were not measured.
Work stops within the 900-second packet bound. Frozen submission awaits fresh
independent review and primary integration; no self-certification or production
authority is claimed. **STOP: writes stopped after final hash receipt.**
