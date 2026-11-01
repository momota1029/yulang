# R177 source handoff — candidate acceptance construction

Status: FROZEN revision 1; partial source correspondence, unreviewed.
R177's fixed outcome is INCOMPLETE. No original Call typing/effect implication
or source soundness counterexample is established. The original
`YulangClosure.SourceProblem.InferenceSoundness` and its single shared
`sameScoped` witness remain OPEN.

Owner/session: `/root/candidate_acceptance_r177_source`, registered researcher.
Baseline: `yulang3`, `ec88e8ff10aee4a2f29f19b6d04ac6800249e7bf`.
Sole output lease: this file. Contract revision 3 SHA-256:
`e3279f46a5076e833d3407b0a64214888fe443bd95badbb1c83a37c444c6af31`.
All 30 direct-input hashes matched before revision-3 content reads. Revision 1
and revision 2 were separately verified (23 and 29 inputs) and paused before
the primary issued the next revision. No pinned source dependency changed.

## Objective, method, and governing meaning

Trace the selected consumer's actual preparation, solver mode, identity and
publication guards, then compare its retained Apply operands to the existing
original source App rule. This is a static source audit, not a Rust execution
or Rust program correctness result. The governing inference principles
§§1, 3–5 require correct natural constraint inference and prohibit publishing
inconsistent results; they do not make exporter success source legality.
The native source-Generalize definition §§2–4 retains independent source rules,
joint clause satisfaction and actual final interfaces. Its local-law and
production-recognition obligations remain explicit.

## Exact operational trace

The following describes successful branches with their actual return values;
it does not assert an executed successful input or supply a new `solves`.

1. `tools/inference-playground/src/lib.rs:102–130`: `infer_types(source,name)`
   calls `prepare(source,name,false)`. `candidate_public_types` checks
   `candidate.observes_hir(hir)` and empty conflicts, then exports every actual
   binding's `definition_root()`. Rendering/output caps may still fail.
   `observes_hir` (`shadow_apply.rs:2006–2008`) uses pointer equality against
   the candidate's frozen HIR Arcs, not module-name or source-text equality.
2. Playground `lib.rs:481–605`: `prepare` retains the exact `(hir,candidate)`
   from `prepare_with_world`. The latter normalizes `-`, checks the byte cap,
   parses under its selected syntax environment and rejects syntax diagnostics.
   It constructs `ModuleIdentity::source_root(FileId::new(FileKey::new(
   "inference-playground",name)))`, resolves the source world/imports, and
   lowers one `Arc<HirModule>`. The `StructuralProjection` import fallback
   requires no explicit imports and successful local lowering with no HIR
   errors; it does not forgive an arbitrary import failure.
3. For `scoped=false`, the final solve is
   `CandidateInference::solve_modules_with_role_sources(modules.clone(),
   &indexes,&role_indexes)`. For `scoped=true`, it is
   `solve_scoped_experiment(hir.clone())`, with a one-HIR module vector.
   After final solve success, nonempty candidate conflicts cause `Err`.
   Only then is the actual `(hir,candidate,modules,indexes)` returned.
   **Preparation itself has no `observes_hir` guard.**
4. Playground `lib.rs:1140–1182`: ordinary `modules` comes from provider
   projection and `append_unique_projection(hir.clone())`; dedup uses module,
   projection signature and projected member-root correspondence
   (`lib.rs:610–657`). Preliminary inspection and missing-member solve attempts
   may extend this world. Their candidate values are discarded. The returned
   candidate is from the later final solve in step 3. Thus a theorem must
   retain the final module vector and candidate rather than substituting a
   preliminary candidate or inferring HIR identity from names.
5. `shadow_apply.rs:1596–1604,1643–1645,1749–1840,1916–1930`:
   ordinary final solve selects `(hirs,false,false,Some(role_sources),None)`;
   scoped final solve selects `(vec![hir],true,false,None,None)`.
   The shared implementation checks a nonempty world, imported ownership,
   source preflight/HIR errors, collects with candidate value/effect graphs
   enabled, retains role members when supplied, and rejects internal SCC uses
   for the scoped experiment. It creates the candidate session and, with no
   readback parameter, calls `execute`, `execute_candidate_field_tails(None)`
   and `finish_candidate`, propagating errors before constructing `Self`.
6. Solver `lib.rs:10746–10756`: candidate finish rejects unresolved **active**
   FieldTail selection and freezes observations. It asserts no closed types
   and no legacy closed schemes. `candidate_scheme.rs:1003–1063` distinguishes
   active unresolved uses from dormant templates: nonempty live source
   obligations, missing route mappings/context, unmatched selected/captured
   uses, live local-use frames and unmatched expression-operator uses can
   block. Selected/captured matches retain source owner, occurrence, dispatch
   context, canonical receiver and, for captured dormant templates, all four
   mapped rows plus guard/source/role metadata. This gate is not a universal
   original Call-certificate check.
7. `shadow_apply.rs:2029–2053`: `export(root)` requires empty frozen errors,
   `owns_definition_root(root)`, a root-scheme position, candidate graph state,
   and `Some(graph)` at that position. It returns a borrowed
   `CandidateGraphExport {state,graph,source_root:root.clone()}`. Frozen
   ownership lookup (`lib.rs:7843–7860`) checks actual HIR root ownership.
   This is a graph from the same candidate state and root, not a closed public
   scheme or semantic assignment.

The source-world helper is also pinned: `pinned_stdlib.rs:3,128–169` includes
the bundle, parses path/blob/text records, and caches resolution. The bundle
was hashed only and remains opaque. Its concrete modules were neither decoded
nor executed in this lane. Parser, HIR-lowering, and imported source semantics
are not independently proved by naming these successful helper returns.

## One original Apply and its native operands

For one source-owned `LocalSourceForm::Apply {callee,argument,..}`, collection
(`candidate_source.rs:1866–1924`) retains the exact source owner, expression
index, callee/argument indices, source level, recipe index, value/effect
positions, checking occurrence and cause. Its recipe points back to this
retained source-input index. This does not choose another occurrence by shape.

Native recipe admission (`shadow_apply.rs:4302–4402`) constructs

```text
demand = NegativeFunction(argumentValue+, argumentEvalEffect+,
                          invocationEffect−, applicationResultValue−)
value constraint: calleeValue+ <: demand
```

It retains that exact native tuple before constraint admission, checking that
the source occurrence matches the recipe and no native tuple was installed
previously. Apply's effect branch (`shadow_apply.rs:4424–4444`) admits

```text
calleeEvalEffect+ <: applicationEffect−
invocationEffect+ <: applicationEffect−
```

The argument effect is already the positive argument-effect port of the native
demand. Absence of a separate direct argument-effect-to-application-effect edge
in this branch is not a demonstrated error: the callee's behavior may carry
that effect. No argument execution, strictness or inert-carrier semantics is
inferred from the shape alone.

`candidate_call.rs:480–575` independently authenticates a requested source-call
observation against the source Apply indices, occurrence/cause, HIR ownership,
lexical scopes, the negative Function's exact four ports, and native
kind/polarity. Observation success is extra structural evidence; final export
success does not itself invoke this observer or establish its semantic inputs.

The original source App generator
(`OriginalSourceGeneration.lean:111–123`) requires
`descriptorFormation`, `wholeArgumentCompatibility`, `completeCallCertificate`,
`sourceCallIncidence`, and `callableImage`, plus `roleAndInitialCallOrigin`
where its formal-call predicate holds. It also requires value checking from
**callee.returnedValue** to **application.descriptor** and computation checking
from **application.callableImage** to **application.synthesis**, together with
both child derivations. `OriginalSourceChecking.lean:939–974` proves this exact
port inventory and extracts the value checking only from an already satisfied
original `Build`.

The native value constraint has the appropriate *subject shape* (the callee's
returned endpoint rather than the application's result). This correspondence
does not decode its demand into the original independently formed descriptor.

## First missing semantic premise and failed proof route

The first unavailable bridge is a source-directed interpretation of this same
retained native tuple, in the same source context and logical/event scopes,
as the original independently formed descriptor and whole argument interface.
It must construct the original App atoms and checking premises from actual
candidate construction/propagation invariants. In particular the whole inert
argument carrier, same-callable domain/observations and complete immediate/
future result/effect interfaces cannot be inferred from four native ports or
an empty error list.

The implementation exposes that gap rather than storing a certificate:
`candidate_call.rs:397–438` always lists original Gen-Call-0,
argument Reify/whole carrier, and receiver-dispatch/complete-result-future
suppliers as pending. Formal callees add original registration/introduction/
exposure suppliers; direct module callees add source typing/admission and
receiving-export correspondence suppliers. These pending labels corroborate
the absence of a supplied bridge; they do not prove the source judgment false.

The attempted implication stops at:

```text
final prepare + same-HIR/conflict guards + root export
  -> retained native graph/Apply construction evidence
  -/-> [not established] original App checking/complete Call judgment
```

No source program with successful final acceptance and a failed original
judgment was established. A false arbitrary Kernel, missing observation,
pending-supplier label or unused port would not supply such a counterexample.
Consequently this partial trace does not meet R177's requested checked branch
implication or concrete semantic failed implication.

## Checks, coverage, resources, and handoff

Commands were bounded `rg`/`sed`/`cat` source reads, SHA-256 verification using
Python, and the single leased Markdown write. All revision input checks passed
(23/29/30 pins respectively); the opaque bundle was only hashed. No Rust/Lean
execution, build, tests, Cargo, cache, scratch, environment or compiler edit
occurred. No random/enumerative search, seeds, oracle comparison or mutations
were used. The independent oracle is the existing original App rule and its
checking inventory; this lane supplies no new semantic oracle and shares no
assumed transition checker with the solver. CPU/RAM peaks were not measured;
only short source/hash processes ran, within the 900-second assignment window.

Coverage is the named experimental consumer's two selected solve modes, exact
final carrier/identity and publication guards, native Apply generation, and
the first original App premise boundary. Propagation preservation, complete
Call, all source clauses, generalization/FreshUse source meaning, full effect
hygiene correspondence and construction of the same global `sameScoped`
witness remain unverified here. No production authority follows.

Recommended next action: assign one construction-preservation proof at the
Apply producer that interprets its actual whole argument and demand in the
original source rule, reusing existing source/checking laws; do not add another
guard-only acceptance relation.

STOPPED: this handoff revision is frozen; no further writes or builds are
running. Independent review is pending and cannot be supplied by this author.

Commit packet:

- Exact leased path: `tasks/agent-loop/inbox/candidate-acceptance-construction-r177-source.md`.
- Baseline: `ec88e8ff10aee4a2f29f19b6d04ac6800249e7bf`.
- Changed source dependency hashes: none; contract expanded sequentially to
  revision 3 as recorded above.
- Claim/review status: partial static source correspondence, unreviewed;
  R177 fixed outcome incomplete and original parent OPEN.
- Checks already run: all direct-input hashes at each admitted revision;
  source inspection only, no executable verification.
- Proposed commit message: `Record R177 candidate acceptance source boundary`.
- Shared deltas deferred to primary: STOPPED lane observation, review intake,
  incomplete fixed outcome, exact missing Apply semantic bridge and unchanged
  parent/sameScoped status. No shared records or Git state were mutated.
