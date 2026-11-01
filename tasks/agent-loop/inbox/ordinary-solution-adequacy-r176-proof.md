# R176 proof handoff — ordinary result and original source discharge

Assignment: `/root/ordinary_solution_adequacy_r176_proof`, registered
`lean_prover`; handoff revision 1. Sole author; no descendants. Requested and
observed effective model/effort metadata were not independently inspected.
Baseline supplied by Luna: `yulang3`, `6a7e31c39`; no Git command run.

**Result: BLOCKED_ACCEPTANCE_TO_ORIGINAL_DISCHARGE.** The authenticated
ordinary API produces diagnostic observations. No original-source acceptance
judgment was identified from which the required semantic discharge can be
constructed. No new theorem or Lean module is delivered; no counterexample
to Yulang type/effect inference soundness is established. This is the new R176
operational finding, not a repeat of R175's registration absence audit.

## Frozen authority and read sequencing

Final contract: `tasks/agent-loop/sprints/ordinary-solution-adequacy-r176.md`,
revision 3, SHA-256
`7b10f0542ada0283f215cfbeba147c55898fea5d27463c490db2875b05308fec`.
Its unchanged 25 direct input pins were all recomputed and matched before
new revision-3 content reads. Revision-1 and revision-2 ACKs likewise preceded
their respective dependency-content reads:

- revision 1: `689fa628a427fd3522cb819ac9032dba793adeca04a90804c4c97bbf93d2ce8a`;
  all 14 input hashes matched;
- revision 2: `9d1bb77fbd9e1473a0f60ef6d548e0cdbb76ac4a79befb56bc487e6c52f13f25`;
  all 23 input hashes matched;
- revision 3: the hash above; all 25 input hashes matched.

Before the first ACK checkpoint, only path discovery, the hash-checked
revision-1 contract, root `AGENTS.md`, `AGENTS.pre-sprint.md`,
`rules/goal-driven-sprints.md`, the Lean proof skill and its `sources.md` and
`execution.md` references were read. Luna was informed of that exact order.
On each unpinned source-definition boundary, content inspection stopped and
Luna supplied the sequential contract revision. The Source-Generalize
definition's correct path is under `notes/design`, not `notes/theory`.

Source evidence was read only after Luna froze and ACKed its stopped revision:
`tasks/agent-loop/inbox/ordinary-solution-adequacy-r176-source.md`, handoff
revision 2, SHA-256
`1389c4d0c7d928c43b4405247a5aa46cfe6cd203a6589b372c8f077cf21a4618`.
That exact hash matched immediately before its content read. Its static source
observations are attributed to its author; this lane did not independently
execute or certify the Rust path.

## Original claim, corrections and Lean correspondence

The original parent remains
`YulangClosure.SourceProblem.InferenceSoundness`,
`notes/theory/lean/YulangClosure/Contracts.lean:127` (definition body
transcribed from the pinned source, not freshly printed by Lean):

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

All source forms, scopes, constraints, solutions and quantifiers remain. The
same `e` must supply the source derivation and `sameScoped` for that same `a`.
No definition of any parent field was changed or instantiated.

Original source authority and exact section map:

- `notes/design/2026-10-08-source-generalize-definition.md` §2 selects the
  independent declarative/local source rules and symbolic rule construction;
  §3 retains genuine L1–L5; §4 separates source checking evidence from
  production recognition. Hash:
  `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`.
- `notes/theory/2026-10-08-source-generalize-definition-and-proof.md`
  §§3.1–3.3 preserve complete Call, source entry, effects, final annotation
  roots, recursive member/world and original Shared/event telescopes. §4
  constructs every active local clause. §5.2 evaluates one global assignment
  and strategy. §6 SRC reconstructs the independent source derivation and
  explicitly does not concern Q. Hash:
  `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`.
- `docs/yulang-source-type-safety-ja.tex`, opening corrections,
  `sec:source` and `sec:all-source`, supplies the 13-expression,
  11-pattern, 3-statement inventory. Its header and correction notice say
  unreviewed research; candidate owner/permission policies were not adopted
  as semantic authority here. Hash:
  `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`.
- `docs/yulang-whole-proof-closure-ja.md` §§1,4 retains whole-source inference
  soundness and distinguishes it from conditional composition. Hash:
  `17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5`.
- Original A/B scope: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
  §§1,3,5, hash
  `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`.
  The current correction is
  `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–4, hash
  `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`:
  qualification uses a fixed birth-level induced graph; source scopes and
  shared strategies do not follow from numeric levels.
- Authoritative inference principles §§1,1.1,4 and authority/integration,
  hash `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`,
  preserve ordinary generation/accumulation/propagation and forbid incorrect
  acceptance or inconsistent publication. They do not supply a success law.

Exact formal definitions inspected:

| Fully qualified surface | Pinned owner / locator | Meaning relevant here |
| --- | --- | --- |
| `YulangClosure.OriginalSource.Source` | `OriginalSourceSyntax.lean:79` | Full 13/11/3 raw grammar and ordered containers; optional records, method selection and handlers retained. |
| `YulangClosure.OriginalSource.sourceRules` | `OriginalSourceGeneration.lean:84` | Source-directed local rules, checks, boundaries and original logical/event binders. |
| `YulangClosure.OriginalSource.Kernel` | `OriginalSourceGeneration.lean:670` | Independent local semantics, genuine admission/conversion/checking clauses. |
| `YulangClosure.OriginalSource.Checking` | `OriginalSourceGeneration.lean:690` | Finite checks; complete Function domain/observation children, without arbitrary inclusion oracle. |
| `YulangClosure.OriginalSource.Judgment` | `OriginalSourceGeneration.lean:744` | Independent rule derivation, including fixed/open execution and Shared/publication scopes. |
| `YulangClosure.OriginalSource.SourceJudgment` | `OriginalSourceGeneration.lean:803` | `Judgment kernel environment (sourceRules context source)`. |
| `YulangClosure.OriginalSource.Satisfies` | `OriginalSourceGeneration.lean:842` | Complete original formula interpretation, including universal branches and one `anchorValue` at Shared. |
| `YulangClosure.OriginalSource.Build` | `OriginalSourceGeneration.lean:870` | `compile (sourceRules context source)`. |
| `YulangClosure.OriginalSource.source_reconstruction` | `OriginalSourceGeneration.lean:1019` | Full-category satisfaction/source-judgment equivalence, conditional on the selected original kernel/environment. |
| `YulangClosure.OriginalSource.generated_constraints_imply_source_judgment` | `OriginalSourceGeneration.lean:1026` | Consumes satisfaction; does not establish operational success-to-satisfaction. |
| `YulangClosure.OriginalSourceInterpretation.PhiW` | `OriginalSourceInterpretation.lean:403` | Original world guards, all installed cells, aliases, captures and shared-field equations. |

Relevant Lean input hashes: `Contracts.lean`
`2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`;
`OriginalSourceSyntax.lean`
`3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`;
`OriginalSourceGeneration.lean`
`126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`;
`OriginalSourceChecking.lean`
`a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6`;
`OriginalSourceInterpretation.lean`
`feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`.
Other exact dependency hashes remain in the authenticated revision-3 contract.

## Applying the frozen ordinary trace to the parent

The source lane authenticates this ordinary control path in
`crates/yu-solver/src/lib.rs`, hash
`429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be`:
`SolvedModule::solve` (`20387`) → `InferenceSession::try_new`
(`10087`, `candidate_graph = None`) → `run` (`10732`) → ordinary admission/SCC
processing → `finish` (`20037`) → `Ok(SolvedModule { errors: data.errors, … })`.
`errors()` (`20448`) separately exposes relation diagnostics. Availability
success, empty worklist and retained diagnostics are distinct observations.
No inspected ordinary public predicate requires complete body collection,
empty diagnostics or original clause discharge. The experimental playground
uses a different `CandidateInference` path; its conflict guard cannot fill the
ordinary API's semantic premise.

Consequently `Ok(SolvedModule)` cannot be used as the hypothesis
`p.solves d a`. This handoff neither asserts that every such result is
accepted Yulang source nor demonstrates a reachable accepted unsound source.
The ordinary collection boundary is also concrete: Apply/Group and nested
Lambda bodies have error body status, and ordinary emission has no Apply
branch (source receipt's `1102–1170`, `1272–1370`). That is a full-source
coverage obligation; it is not permission to restrict the parent or proof
that a public source acceptance decision accepts those cases.

The useful existing implication applies as follows. For any original category
and source `s`, fixed original kernel `K`, environment `env` and context `Γ`,
an actually established

```lean
YulangClosure.OriginalSource.Satisfies K env
  (YulangClosure.OriginalSource.Build Γ s)
```

would yield `YulangClosure.OriginalSource.SourceJudgment K env Γ s` by
`YulangClosure.OriginalSource.generated_constraints_imply_source_judgment`.
Its premise has not been produced by the ordinary trace. Neither a default
`LocalLaws` parameter nor a proposition definition produces it.

The **first remaining premise** is the original semantic success/acceptance
bridge: identify the actual criterion denoting successful Yulang type/effect
inference and prove that every result meeting it discharges the complete
generated original clauses at one original kernel, environment and strategy.
It cannot be defined from `Ok` or from an unproved empty-error sufficiency law.
Owner: Luna assigns the acceptance/source correspondence owner; this leaf has
no authority to select a new acceptance meaning.

After that premise is identified, its genuine proof has at least these seams:

1. Complete original-source collection, including the recorded Apply/Group
   boundary, mapped to the actual `Build` clauses without removing source
   forms or interpreting permissions as actual inflow/subtraction residual.
2. Semantic admission/propagation/SCC/finalization invariants proving those
   same type/effect clauses are discharged; worklist exhaustion and diagnostic
   preservation alone do not imply their meanings.
3. Same-solution source readback and the single shared `sameScoped` witness:
   the reconstructed source derivation must be the `e` for the same returned
   `a`, preserving rigid imports, Shared anchors, every use and future.

Those are open premises with source/solver correspondence ownership to be
assigned by Luna, not assumed fields of a theorem. The parent remains OPEN.
There is no proof of a Rust program guarantee and no production promotion.

## Checks, resources, changed paths and stop

Actual commands: read-only `pwd`, `rg --files`, bounded `rg -n`, `cat`,
`head`, `sed -n` and `sha256sum`, plus one UTC clock lookup. All shell
invocations returned exit 0. Hash commands and reads were short; reported
individual shell wall times were at most 0.1 s. CPU, peak RSS and aggregate
agent time were not instrumented; no invented resource receipt is supplied.

No theorem was constructible from the current authenticated acceptance
evidence under the approved laws. Thus no Lean/Lake invocation or helper check
was run, no fresh Lean version was observed, and there are **no fresh printed
theorem types or axiom results**. Lean 4.35.0 was supplied in the packet, not
independently executed here. This is a semantic input obstruction, not a
checker failure or an unchecked proof claim. The reserved one focused check
and required import build (180 s total, 1 CPU/1 GiB) were unused. Existing
`.lake` was not read or written; no cache/generated output or environment was
created. No tests, Cargo, runtime, Git, root-import changes or scratch outputs.

Sole changed path:
`tasks/agent-loop/inbox/ordinary-solution-adequacy-r176-proof.md`.
`notes/theory/lean/YulangClosure/OrdinarySolutionAdequacyR176.lean` was not
created. No represented case was removed; no new theorem represents a subset.

Independent review: pending; no self-certification. Primary owns integration,
review appointments and shared records. **STOPPED / WRITES STOPPED** on this
handoff submission. No background process, descendant or generated output
remains. Further work requires a new primary packet with the exact acceptance
criterion and original correspondence inputs; do not substitute an assumed
model or a stronger source-typing hypothesis.
