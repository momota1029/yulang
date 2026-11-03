# R343 — actual computed-callee continuation consumer; original EI remains open

Handoff `R343-CONTINUATION-ELIMINATION`, revision 1. Producer
`/root/r343_continuation`; baseline supplied by primary `944dff732`.
Exact Lean artifact: `notes/theory/lean/YulangClosure/OriginalContinuationEliminationR343.lean`,
SHA-256 `de4cd62f0e5b8a489bee08e36aabd47c8e2de5fb7a9c7fdd9694d4e1d3ed99a0`.
No coauthors, children, Git, compiler edits, root-import edits or shared records.
Source bytes frozen and source writes STOPPED before independent review.

## Outcome and application

**Constructed and kernel-checked candidate HigherOrder source consumer. Zero
R339/R306/R159 semantic premises eliminated. No source-qualified refutation.**
The improvement over R342 is the actual R314 selected caller `(make 1) value`,
rather than stopping at make's returned lambda. The declaration-derived tick
consumer, original block discard, make result consumer, pending outer caller,
identity entry, designated Force and identity result consumer remain ordered.
The Request is reached by eight constructed internal steps and actual publication.
After every finite protocol-respecting interaction, handle 0 still denotes the
same full operation/payload/continuation/context. Every original independently
typed response, with its entire view list, resumes that handle and reaches the
actual caller's integer argument via eight further internal steps. No reached
prefix, completed child, successful termination, arbitrary ResponseSchema or
finished EI clause is supplied as an input.

Namespace prefix below: `YulangClosure.OriginalContinuationEliminationR343`.

- `selected_source_projection`: computes projection of the original exported
  selected source with names `[value, make]`; its lexical substitution is exactly
  `selectedProgram`. Substitution supplies R342's constructively typed make value.
- `selected_prefix`, `selected_capture_typed`: derive the actual saved packet,
  including the pending outer application. `identity_consumed` applies the
  returned lambda to that independent caller; `selected_response_delivery`
  composes the real callee response and this caller consumer.
- `Development.authentic_source_publication`: joins both original decoded trees,
  their computed projections/substitution, full original source-Key tick
  resolution, actual interaction prefix/publication and derived StateTyped.
- `Development.every_development`: for all receipt decorations, integer arguments,
  action lists and actual finite traces from publication, proves current
  StateTyped, progress and unchanged handle lookup. Zero/pending/internal and
  repeated-response developments are not restricted to returning traces.
- `Development.response_after_every_development`: consumes the preceding invariant
  at every such current state and every TypedCall-typed original response; proves
  the exact protocol, concrete delivery trace, final StateTyped and same lookup.

All 17 theorem types and complete axiom outputs are preserved in
`/tmp/yulang-r343-continuation/audit.log`; exact name list is `theorems.json`.
The result is conditional only on the existing operational Trace protocol and
external response ValueTyped in its final consumer. Actual source typing, prefix
and capture are constructed. Receipt decorations are arbitrary syntax data;
no receipt semantics or protection/hygiene result is inferred from them.

## Original governing claim and precise remaining premise

Governing IF source: `notes/design/2026-10-08-call-source-interface-definition.md`
§§2–4 and `notes/theory/2026-10-08-call-source-interface-construction.md`
§§3.1–3.3, 6–7. EI source:
`notes/design/2026-10-24-computed-call-result-constructor.md` §§2, 3.1, 3.4, 5(1).
These require the genuine original full C_f/d_f contract before Request elimination;
IF placement retains that independently typed contract and grants no license.
Original operational manuscript: `docs/yulang-operational-type-safety-ja.tex`,
opening correction and request-cutting/resume lemmas around lines 1000–1088.
Current correction: source manuscript opening and
`notes/theory/2026-10-24-corrected-core-value-continuation.md` §§4–5. Their
candidate value-typing preservation is distinct from original complete EI typing.

Original source d_f owner is `OriginalSource.SourceJudgment` in
`OriginalSourceGeneration.lean:803`, with constructors at line 744. It is finite
`Judgment kernel environment (sourceRules context source)`. The real primitive
eliminator is `OriginalSourceScopedInterpretationR335.primitive_source_iff`:
its result is exactly `kernel.atom environment entry.data`. `Kernel.atom` and
primitive-check/admission semantics remain independent; this derivation has no
raw Request/continuation constructor yielding original C_f membership.
`sourceRules` does retain the `actualReturnOrPendingSuffix` and
`primitiveDeclarationInstance` atom obligations; their full interpretation is not
constructed by adding their source tags. This is a bounded inspection finding,
not a theorem that no richer original interpretation could exist.

The unchanged parent is
`OriginalSourceEIConstructionR339.every_typed_callee_response`. Its first missing
field remains, at the SAME original state/request/declarations/schema/head:

```lean
∀ answer : ResponseAt inputs schema head,
  Meaning inputs (.trace (answer.raw.atInterface
    (state.interfaces ⟨request.original.calleeSite, .synthesis⟩)))
```

Even after that field, the source-Key/use-authenticated resumed `.calleePrefix`
PrimitiveInput and all independently registered BoundReturn ReturnInputs remain.
The latter retain same-return checking, actual provider and whole argument/reify
obligations. No candidate CompTyped-to-Meaning cast or exact-conclusion callback
was introduced. There is consequently no legal full R339 application from this
artifact. R306's authentic licensed child/catalogue and R159's original logical
admission, all local checks and both source children remain unchanged. Primary
owns the original Kernel/Inputs primitive-contract interpretation packet and
source/native correspondence; those are the next distinguishing inputs.

Represented: the authentic selected callee/caller, actual tick physical
resolution, higher-order returned lambda, Bind/Delay/Force, all original formal
typed tick responses with ordered views, publication and arbitrary finite
protocol-respecting resumption histories. Omitted from this candidate calculus:
original Event/current-world compatibility, shared original witness telescope,
W/Z arms, original guards/licenses, handler selection, live protection metadata
and native execution simulation. The original whole-language domain and shared
witness quantifiers have not been replaced by this fixture theorem.

## Execution, audits and failures

Installed native toolchain resolved with `elan which lake`:
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
Actual versions: Lake 5.0.0-src+eb6cafb, Lean 4.35.0,
commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
All generated outputs are isolated under `/tmp/yulang-r343-continuation/project`;
no shared `.lake` output was written. Verification slot was coordinated and
released to primary between stages and after the final audit.

1. Initial isolated `lake build +YulangClosure.OriginalSourceContinuationR342`
   exited 1: project `-M1024` caused kernel excessive memory in R315 at
   lines 72/79, followed by cascading errors. Preserved `import-build.log`.
2. `python3 /tmp/yulang-r343-continuation/build_cone.py`: freshly compiled all
   91 local imports sequentially using native `lean -j1 -M2048`; aggregate
   146.2 seconds including initial new-target failure. Each import exited 0.
   The first new-target errors were reserved token `prefix`, an induction on
   a nonvariable index and underconstrained Event list notation. `cone-build.log`
   and `cone-receipts.json` preserve them.
3. First direct repair exited 1: transitivity induction hypotheses still
   required the second trace argument. `repair1.log` preserves both goals.
   Supplying that argument gave direct target exit 0, 0.844 seconds;
   `repair2.log` is empty. Final target/audit shell exited 0;
   `final-target.log` is empty and final audit imports the added authentication
   theorem from the compiled module.
4. Manual native `lean -j1 -M2048 ProofAuditR343.lean` exited 0 in 1.040 seconds.
   Used the skill checker's unmodified `audit_source` and `validate_audit`
   components, including theorem-kind and allowed-axiom checks, for all 17
   declarations. Full helper/default target success is NOT claimed: its
   configured `-M1024` build failed above. No config or checker was changed.

Complete axiom grouping (not merely a source grep):

- `[propext, Classical.choice, Quot.sound]`: `selected_source_projection`,
  `Development.authentic_source_publication`.
- `[propext]`: `selected_capture_typed`, `Development.every_development`,
  `Development.response_after_every_development`.
- `[]`: the remaining 12 delivered theorems, individually listed in `axioms.json`.

The dependency-cone hole/bypass source scan found only an English comment using
“admit” in OriginalCheckingAdmission. No proof hole or project axiom was delivered.
All 91 copied import sources were rehashed against the repository at freeze:
none changed. Source authority hashes are in `source-evidence.json`, SHA-256
`1ac17e03f60bc1adf6f1d63a67ab3cc1dcc4d89a1658e4d29de5d6152a247d60`.
Final import manifest `final-imports.json`, SHA-256
`2f2d4fc82bc0536ec62ab0daa3e3d6802757d07c68ab3fcc0beb9e89139ea08e`.
Complete audit log SHA-256
`b75ee57d5660ce66bb47435053111838980ba5bd5455fa98feafc0865c1847e0`.
`artifact-hashes.json` lists other evidence hashes. The earlier `dependencies.json`
retains the initial failed-target source hash; use `final-imports.json` plus the
frozen artifact hash for final review, not that earlier target revision.

Grant: 3000 seconds. Total author wall time/RSS were not instrumented; explicit
checker stages and versions above are measured. Fresh-cone/final stages used one Lean process at a time, `-j1`, local memory
bound 2048 MiB, per-process 120-second and cone aggregate 600-second bounds.
Initial Lake scheduler concurrency was not instrumented. Isolated scratch was
approximately 266 MiB. All owned execution
has ceased, checker released, no descendants. This handoff and the exact Lean
artifact are the only repository writes. All writes STOPPED. Kernel acceptance
is reported separately from independent review, source/native correspondence
and production authority, which are not supplied by this worker.
