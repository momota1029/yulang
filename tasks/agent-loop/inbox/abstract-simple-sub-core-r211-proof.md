# R211 proof handoff, revision 1

Disposition: **STOPPED_INCOMPLETE — missing cached dependency**. Producer:
`/root/abstract_simple_sub_core_r211`, assigned registered `lean_prover`.
Effective runtime model/effort metadata: UNKNOWN. No independent review or
self-certification. Contract SHA-256:
`f3850d4d655c6f694043d7b3ceec6cd5628d5a1308bd45ad63653c04d16c5bef`.
Supplied baseline: `yulang3` / `607e2ce81`; no Git command was run by this leaf.

## Result and exact execution stop

Stage A did not freeze a concrete model. No Lean module, declaration, proof,
scratch file, cache, target, environment, or generated output was written.
The only changed path is this handoff. The leased
`notes/theory/lean/YulangClosure/AbstractSimpleSubCore.lean` remains absent.

The existing project lacks these required compiled imports:

```text
notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubConstraintSyntax.olean
notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubLatticeInference.olean
notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubLatticeGrowingInference.olean
```

The read-only `ls -l` of those three exact paths returned exit 2, with
`cannot access '…': No such file or directory` for each. The parent directories
`.lake`, `.lake/build`, `.lake/build/lib`, and `.lake/build/lib/lean` exist
(`ls -ld`, exit 0). This is an absent dependency artifact, not a Lean proof
diagnostic or a mathematical counterexample. The contract explicitly says to
stop on a missing cached dependency and prohibits a new cache/target/environment.
The producer therefore did not invoke a build or the checker to regenerate it.
Primary was notified through the existing team channel before this freeze.

Actual toolchain receipts, cwd `notes/theory/lean`:

```text
$ elan which lake
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake
[exit 0]
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --version
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
[exit 0]
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake env lean --version
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
[exit 0]
```

`check_lean.py` invocations: **0/2**. Delivered theorem declarations: **none**.
Printed theorem types and `#print axioms` results: **NOT_RUN; no theorem was
delivered**. No kernel-acceptance, axiom-free, model/runtime, source/native,
independent-review, or production receipt is claimed.

## Governing claim and correspondence inspected

Read root `AGENTS.md`, `AGENTS.pre-sprint.md`, `rules/goal-driven-sprints.md`,
the R211 contract, compact current state/README, the Lean skill and its
`references/sources.md` and `references/execution.md`. Read the actual project
pin, lakefile, manifest, relevant README sections, and the listed declarations.

Original manuscript: Parreaux, *The Simple Essence of Algebraic Subtyping*,
local `/home/momota1029/rust/simple-sub-reference-paper.pdf`, §§3.5.1–3.5.2,
Figures 6–9, §5 introduction/footnote 15, §§5.2–5.3 and Figures 11–12. Read
with `pdftotext -layout … -` and bounded output windows. The actual reference
`Typer.scala:48–207,238–257` supplies level-based bound propagation, polar
extrusion memoization, freshening and polarized coalescing. Its two-port
Functions and absence of occurrence-qualified intrusion do not instantiate
the full R211 core. The paper explicitly limits its proof sketch to the
non-let-polymorphic algorithm; its footnote does not prove the extension.

Original Yulang parent: `2026-10-13-intrusion-source-preservation-proof.md`
§§1,3–5, with `2026-10-24-birth-level-scc-intrusion.md` §§2–6 replacing the
old cross-level qualification. Quantification remains every supported original
source program, lawful history, actual occurrence and its polar pairs, with
the original scope, one shared witness/strategy, publication and lawful uses,
complete Call and effect hygiene. Local diagonal lifts do not supply that
shared source-scoped strategy.

Authoritative operation sources inspected: top-level principles §§1–5 and
§1.1; parent-copy decision and its association clarification; birth-level
correction §§2–6; source Generalize selection §§2–3. The pinned accumulation
note is a finite complete-inclusion research theorem. The pinned Value-reference
note explicitly leaves its reference-to-Yulang Value-graph identification open;
it is not authority to infer source incidence from solver bounds.

Primary clarification received during Stage A: `CoreProblem` may own concrete
finite Value-reference adjacency, immutable birth levels, and publication/use
input data. Consumed relations must be computed from those fields; subsequent
source soundness must construct the input. Accordingly, the absence of source
Value incidence in bare `SimpleSub.Constraint` is **not** reported as a semantic
impossibility or a definitive R211 authority gap. No arbitrary relation,
successful history, `LawfulStore`, or final certificate was substituted.

Exact existing definitions inspected (source inspection, not fresh printing):

* `YulangClosure.SimpleSub.Term`: Value/Effect kinds; var/atom/bottom/top;
  union/intersection; Function argument, argumentEffect, resultEffect, result;
  record labels/optional bits, tuple order, variant tags/payloads.
* `YulangClosure.SimpleSub.Constraint` has `kind`, `lower`, `upper`;
  `Store.Satisfied ρ store` means every member satisfies the independent `Sub`
  relation under the same substitution.
* `YulangClosure.LevelPath`, `ExtrusionOccurrence`, `Qualifies`: both paths
  stay within one immutable birth level; actual occurrence endpoints and polar
  parent/copy pairs remain distinct from type-graph coordinates.
* `YulangClosure.SimpleSub.LatticeInference.Completion.completeTerm` and
  `completeStore` compute structural completion relative to supplied references;
  `Lawful`/`LawfulStore` contain exact shape/presence requirements.
* `YulangClosure.SimpleSub.LatticeGrowingInference.GrowingHistory` is indexed
  by supplied graph/ref/birth and contains supplied `ConstraintStep` and graph
  extensions. `completed_decided_growing_store_sound` still takes `LawfulStore`
  and that history. It is not `CoreProblem.initial` plus an endogenous solver.
* `YulangClosure.SimpleSub.ScopedPublication.Metadata`, `captureGuard`,
  `useGuard`, `BoundLevelsClosed`, `NonGenericClosed`, `MetadataTransport`:
  these retain current/captured/non-generic distinctions; their proposition
  definitions are not concrete all-run invariants.

No cases were removed from R211. **No concrete R211 cases are represented by
a delivered module**, including extrusion, intrusion and publication/use.

## Parent application and next owner

The actual namespace in `Contracts.lean` is `YulangClosure.SourceProblem`
(the contract's `Contracts.SourceProblem` names the containing module).
Its original soundness definition is, with the source-file parameter names:

```lean
def InferenceSoundness : Prop :=
  ∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
    ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

There is no new lemma to apply. R211 whole-run soundness remains unconstructed
and unproved. First execution premise/owner: **primary/verification owner must
provide the already-built pinned dependency artifacts or revise the fixed
no-cache/resource contract before another construction/check packet**. No
installation, manifest, lockfile or global-default change is requested here.

After that, the next construction remains the unchanged Stage A definitions
and actual solver readout, deriving the decoder/history/invariants from
`initial`/`step`; neither a supplied graph interpretation nor a preservation
certificate can close this task. Source `generates`/`solves` adequacy and
same-scoped source readout remain independent primary-owned premises even if
that abstract theorem is later proved. Principality/order, original-source
termination/accessibility, and source-scoped coverage stay open.
Accounting: **0/4 roots; 0/5 packages**. No root delta, counterexample,
production promotion, or claim that conditional mathematics closes the parent.

## Authenticated inputs

All 15 contract pins matched at intake; none was edited by this leaf.

```text
2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e Contracts.lean
a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6 SimpleSubConstraintSyntax.lean
33709d3978e8071708c10bba23d85b1b025c11dfd988220501acb7c6e3220293 SimpleSubConstraintSoundness.lean
c534c060dfde84f2817fbaa53222f430b59d9b6377cfacedabeca7b9b4b8ffa3 SimpleSubLatticeInference.lean
1270e3407ddeef881020610b094709ebba07b62a97e54712bcc4b139ef8e78d0 SimpleSubLatticeGrowingInference.lean
865b9eb4a64962182a22a9e507b98b1e7ab92ac143e4cbfea0b8570e39bb58ce SimpleSubGrowingInference.lean
d7231d0a3695dba7f3102e5fe235d4d26e34cad78870dbdbae9b7633c42787aa SimpleSubRegularCompletion.lean
6b6e5e6f1c45140d935e1aa29fba4c1303ae89cd91fd6e1cde0d37387148db8d SimpleSubRegularDecision.lean
a9c184512bf6e23d15cc8a3a2ed230652fb168f707155e779be18c562d8e57c9 SimpleSubLatticeDecision.lean
d64e9bffca5d513985237a9ff78dcf3d9e43baae1594edbc93dff4b5410d428f SimpleSubScopedPublication.lean
3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246 SimpleSubGeneralizationSoundness.lean
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81 top-level inference principles
6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b parent-copy SCC decision
f4d3bd7e89ae26ecba0baeaaa351e82037ff0cf268c815e64b638dbbabfb2493 complete bound accumulation
8dd8eb55ac9d9df75980182cb5483f9394674a94f77c9d70d12f89b5be0d24e6 Value-reference SCC
```

Additional consulted source/environment SHA-256:

```text
ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae birth-level SCC decision
531a9efae0ab7e03bfbd2f41cd7da86078e2fc8e67675d2c5c941972409f4e89 Value/type association clarification
3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271 original source-preservation claim
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38 source Generalize selection
5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698 reference paper PDF
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9 reference Typer.scala
ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c lean-toolchain
212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4 lakefile.toml
058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3 lake-manifest.json
```

## Resource and cessation receipt

One leaf, no children, no tests/Rust/build/checker/inference execution, no
Git mutations, no external communication. Read/hash/text commands and the
two native version commands ran. No total CPU/RSS or active reasoning timer
was instrumented; exact aggregate consumption is UNKNOWN. No 120-second
verification allocation was consumed. A read-only wall-clock observation was
`2026-11-01T18:42:15Z`; this is not an active-time measurement.

All writes cease after this revision's handoff write. There is no running
subprocess, generated-output writer, scratch lease or pending child. Primary
owns intake, dependency provisioning/contract revision, independent review,
shared records and integration. This producer will not resume writes without
a new primary packet.
