# R177 proof handoff — exact candidate Call seam

ID: candidate-acceptance-construction-r177-proof; revision: 1; FROZEN.
Author/session: `/root/candidate_acceptance_r177_proof` (`lean_prover`).
Claim class: source/rule correspondence investigation; **fixed outcome INCOMPLETE**.
No new theorem, original semantic counterexample, parent closure, or production
authority is claimed. Writes/read activity stopped after this handoff was frozen.

## Fixed inputs and execution

Baseline: `yulang3`, `ec88e8ff10aee4a2f29f19b6d04ac6800249e7bf`.
Final contract revision 3 SHA-256:
`e3279f46a5076e833d3407b0a64214888fe443bd95badbb1c83a37c444c6af31`.
All 30 direct-input hashes were recomputed with Python `hashlib.sha256` and
matched before post-revision content reads. `pinned_stdlib.bin` was hashed only;
its contents were not decoded or inspected. Previous rev1/23 and rev2/29
verification also passed. Primary-requested revision pauses were acknowledged.

Read-only shell/Python searches, source reads and hash verification exited 0.
No Lean, Lake, checker, Cargo, tests, default build, runtime, dependency operation,
new environment/cache or scratch file was run/created. No theorem exists, so the
contract's single focused Lean check/import-build allowance was not consumed.
No new printed theorem type or axiom audit exists; neither kernel acceptance nor
axiom freedom is asserted. The installed toolchain was not invoked by this lane.
No build resource/peak-memory receipt is asserted.

Sole file changed: this handoff. The leased
`notes/theory/lean/YulangClosure/CandidateAcceptanceR177.lean` was not created.
No compiler, status, import-root, manifest, question, or other worker file changed.

## Original claim and authority

The unchanged parent is
`YulangClosure.SourceProblem.InferenceSoundness`, `Contracts.lean:127–130`:

```text
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

The source domain and `x` remain the original ones, and **the same `e` and `a`**
must discharge both conclusions. This work does not define `solves` or replace
the witness with separate witnesses for each Call.

Governing inference policy is the Authoritative 2026-10-11 top-level principles
§§1–1.1 and existing hygiene integration §1. The Authoritative
2026-10-08 source-Generalize selection adopts construction §§3–5, with source
equivalence/theorems under their stated L1–L5. In that construction §3.1, Call
retains the original callee computation, inert **whole** argument, actual
returned callee, receiver/receipt, actual entry, designated consumer and
invocation return. Section 3.2 requires independently valid finite checking;
complete Function checking keeps the same callable and proves checked-domain
and observation inclusion on the whole joint tuple.

`docs/yulang-source-type-safety-ja.tex`, opening correction and §1, explicitly
separates finite declarative source proofs from inference success. Its App
coverage table (line 281) evaluates the callee once and passes the whole delayed
argument to complete Call. Its candidate lifetime/permission developments are
not adopted as new semantic authority here. The integration guide's opening
research status and the whole-proof guide §1 retain the full inference goal.

## Reconstructed operational trace, including identity and native operands

This is a source-derived trace specification, **not a proved Lean operational
relation**. Its operation nodes refer to the pinned Rust owners, rather than
free predicates asserting original source success.

Let the retained result be the exact tuple `(h, c, H, I)` returned by
`prepare_with_world(source,name,scoped)` (`playground/lib.rs:490–605`). A trace
retains the original source text, normalized name (`-` becomes `stdin.yu`),
module identity, parsed artifact, final `Arc<HirModule>` `h`, provider modules
`H`, source indexes `I`, role indexes, and the same candidate carrier `c`.

1. Preparation follows the input cap, syntax-environment/parse/diagnostics,
   pinned world, imports and lowering branches. Structural-projection fallback
   is available only with no explicit imports and an error-free local lowering;
   other import errors return `Err`. The final lowering result remains `h`.
2. `scoped=true` chooses `H=[h.clone()]` and
   `solve_scoped_experiment(h.clone())`; `scoped=false` constructs the pinned
   candidate world and invokes `solve_modules_with_role_sources(H.clone(), I,
   role_indexes)`. These modes select respectively `(scoped=true,
   operation_v1=false, role_sources=None)` and `(false,false,Some(...))` in
   `shadow_apply.rs:1596–1604,1643–1645,1749–1759`. They are not interchangeable.
3. The final non-inspection route retains preflight, collection and session
   success, then `execute`, FieldTail dispatch and `finish_candidate`
   (`shadow_apply.rs:1763–1840,1916–1930`). Candidate finalization rejects an
   unresolved **active** FieldTail selection, then calls `finish_observations`
   (`lib.rs:10746–10759`). The active test has the exact owner/occurrence,
   dispatch-context and receiver-representative requirements in
   `candidate_scheme.rs:1003ff`; dormant captured templates are not all treated
   as unresolved. This condition is not complete original Call discharge.
4. Preparation returns only after `candidate_conflicts(c)` is empty. It does
   not itself call `observes_hir`. `infer_types` subsequently calls
   `candidate_public_types(h,c)`, which separately requires `observes_hir(h)`
   and empty conflicts (`playground/lib.rs:102–130`). `observes_hir` is pointer
   identity against a HIR retained in this candidate (`shadow_apply.rs:2006ff`).
5. Each requested binding export keeps its exact definition root `r` from `h`.
   `export(c,r)` requires no errors, root ownership, a scheme-position lookup,
   candidate graph state, and a graph at that position. It returns a borrowed
   pair from **that same state** plus `r.clone()`
   (`shadow_apply.rs:2029–2053`). This cannot be replaced by an arbitrary graph
   having an equal printed scheme. Rendering/output-cap success is an extra
   consumer operation, not a source typing proof.

For one source Apply occurrence `k`, retain its owner `o`, exact callee and
argument source indices `f,u`, recipe, checking occurrence `(k,0)` and cause.
`candidate_source.rs:1869–1924` retains these in `ApplySourceInput` and attaches
the recipe's `source_input`; it does not select them by endpoint shape.
The actual Apply branch (`shadow_apply.rs:4302–4388`) constructs:

```text
Vf+ = positive endpoint of that source callee
Vu+ = positive endpoint of that whole source argument's value component
Eu+ = positive effect term of that argument's effect component
R−  = negative result component of this Apply
J−  = fresh negative invocation-effect term at this application-effect level
D−  = NegativeFunction(Vu+, Eu+, J−, R−)
NativeInterface = (Vf+, Vu+, Ef+, Eu+, R−, D−, J−, invocation_row, Eapp−)
admitted value pair = (Vf+, D−), with checking occurrence/cause for k
```

The same branch records the native interface before value-constraint admission.
The effect branch (`shadow_apply.rs:4424–4444`) admits `Ef ≤ Eapp` at slot 1
and `J ≤ Eapp` at slot 2. There is no separate direct `Eu ≤ Eapp` edge in this
branch. **This is not a counterexample:** Eu enters the Function's argument
effect port, and the callee's entry/body behavior may propagate its contribution.
No eager-argument or empty-effect interpretation is silently substituted.

## Exact original Call target and first missing bridge

Use the corresponding resolved source occurrence
`Source.app ⟨site,none⟩ callee argument` in the original context `Γ`. Establishing
this correspondence itself must preserve `o,k,f,u`, module identity and the
same candidate/session; equal spelling alone is insufficient.

`YulangClosure.OriginalSource.sourceRules` (`OriginalSourceGeneration.lean:
111–123`) introduces one admitted `ViewLogic` value at `⟨site,.viewLogic,0⟩`.
In the resulting single environment `ρ'`, its App node requires all of:

```text
descriptorFormation, wholeArgumentCompatibility, completeCallCertificate,
sourceCallIncidence, callableImage
(and roleAndInitialCallOrigin for singletonFormalCall)

Checking original ρ'
  ⟨.value, site, Γ, ⟨callee.site,.returnedValue⟩, ⟨site,.descriptor⟩⟩
Checking original ρ'
  ⟨.computation, site, Γ, ⟨site,.callableImage⟩, ⟨site,.synthesis⟩⟩

both child source judgments in the same ρ'
```

This inventory is already proved by
`YulangClosure.OriginalSourceChecking.generated_application_ports`
(`OriginalSourceChecking.lean:940ff`).
`generated_application_checking` at 957ff obtains the admitted value and first
Checking proof **from an already satisfied original Build**; using it with
candidate acceptance as if that premise were supplied would be circular.

The earliest unconstructed sequent for the selected value check is therefore:

```text
exact preparation/mode/session/finalization/public-export trace for (h,c,H,I,r)
and exact source Apply o,k,f,u with native tuple above
  ⊢ ∃ v, original.admitted ρ ⟨site,.viewLogic,0⟩ v ∧
       Checking original (ρ.extend ⟨site,.viewLogic,0⟩ v)
         ⟨.value,site,Γ,⟨callee.site,.returnedValue⟩,⟨site,.descriptor⟩⟩
```

The native `(Vf+,D−)` comparison must be connected to the original endpoints
and same decorated callable. Its actual discharge needs an original finite
checking derivation, including checked-domain/observation obligations where
Function checking applies. The existing native tuple and empty conflicts do
not yet construct that derivation or the admitted `v`. The corresponding
computation goal additionally requires the original complete callable-image
interface and synthesis interface; two scalar effect edges alone do not give
the universal same-observation implication. The exact mode reading is visible
in `OriginalSourceChecking.ModeMeaning:1072–1095`: computation ranges over every
raw observation at the two complete interfaces.

`candidate_call.rs:397–438` independently retains pending OriginalGenCall0,
ArgumentReifyAndWholeCarrier, and ReceiverDispatchAndCompleteResultFutureInterfaces
suppliers for every source Call. Those pending labels corroborate the seam;
they are **not** a proof that the source program is ill typed. No original
accepted-source counterexample was found, and failure of the stricter
`source_call` observer would not by itself refute source typing.

## Parent application, scope, and next work

The trace fixes a concrete owner for the selected Call obligation and preserves
its native operands. It does not discharge the sequent above. Consequently it
cannot be applied to the parent as a proof. Complete `Build` discharge and the
one shared `sameScoped` witness remain OPEN, as do unrepresented source clauses
and generalization/use correspondence. No source constructor was removed.

The next constructive task belongs at the candidate comparison/source Call
boundary: construct the original admitted description and finite same-callable
Checking derivation from the actual candidate operations on the retained tuple,
or find a genuine accepted-source violation with those exact operands. A new
opaque `acceptance_sound` premise, arbitrary false-kernel countermodel, generic
guard theorem, or permissive definition of `SourceProblem.solves` would leave
that task unchanged and is not offered as progress.

STOPPED: both leased outputs are frozen; this worker will perform no more
reads, writes, builds or cache operations unless explicitly resumed by primary.
