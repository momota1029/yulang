# R179 proof handoff — first App descriptor construction gap

Status: FROZEN revision 1, **BLOCKED**, unreviewed. No theorem constructed,
no Lean module written, and no Lean/Lake command run. This reports a missing
source-owned construction in the frozen inputs; it is not a counterexample
to Yulang inference soundness.

- Sprint/contract: `original-app-admission-r179`, SHA-256
  `30bd50b1886d9b390ab290051b9d2926552b7dc45aa5a17ff47c35cde25e42aa`.
- Assignment/author: `/root/original_app_admission_r179_proof`, current-session
  bounded constructive proof leaf. No descendants or contributing coauthors.
  Requested registered role: `lean_prover`; actual model/effort: UNKNOWN.
- Baseline supplied by contract: `yulang3`,
  `9ee28f082c157fda11d7c5c948decd3798472bbb`. No Git command was run.
- Sole output written: this handoff. Leased
  `notes/theory/lean/YulangClosure/OriginalAppAdmissionR179.lean` remains absent.
  Existing `.lake` ownership was reserved to this lane; no build/check touched it.

## Input acknowledgement

Before reading any direct-input contents, a Python verifier separately
enumerated all 17 path rows in the contract's Frozen direct inputs section,
required the exact path-row grammar and a complete 64-hex hash on each following
row, and compared SHA-256 of each file's bytes. It rejected omissions through
the explicit count assertion. Result: 17 rows, zero malformed rows, zero
mismatches; verifier exit 0. The contract hash also matched. ACK was sent to
primary before constructor investigation. Direct dependency revisions are
exactly those 17 immutable contract rows; no semantic dependency was added.

Operating sources read: root `AGENTS.md`, `AGENTS.pre-sprint.md`,
`rules/goal-driven-sprints.md`, `rules/design-authority.md`, current state and
handoff protocol, the assigned contract, `yulang-lean-proofs/SKILL.md` and its
`references/sources.md` and `references/execution.md`. Project pin/config and
README were read without invoking a toolchain.

## Original claim and exact source scope

The unchanged parent is `YulangClosure.SourceProblem.InferenceSoundness`.
The pinned R178 proof receipt locates its original definition at
`YulangClosure/Contracts.lean:127–130` and records:

```text
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

`Contracts.lean` is not one of R179's frozen direct inputs, so this lane did
not expand the dependency lease to reread it or construct a parent theorem.
The fixed task keeps that parent and its one same-solution witness unchanged.
Its objective is inference success implying the original type/effect judgment;
Rust runtime correctness is outside this packet.

The original source manuscript actually read is
`2026-10-08-source-generalize-definition-and-proof.md`, §§1–3.1, 3.3 and 6,
contract SHA `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`.
Its scope is conditional on independently supplied L1–L5, rather than a
concrete interpretation of every local predicate. §3.1 Call retains the actual
callee computation, inert whole argument, returned callee, receiver/receipt,
entry, designated consumer and invocation return. §3.3 retains ViewLogic's
complete prior telescope and original description-region position. §6 preserves
the same operands and witnesses. The governing 2026-10-11 Authoritative
inference principles and current clarification were read at their pinned hash
`7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.
Research manuscript status does not authorize a new semantic law.

The exact actual Lean App equation is
`YulangClosure.OriginalSource.sourceRules`,
`OriginalSourceGeneration.lean:111–123`. It retains arbitrary callee and
whole inert argument, both annotation alternatives, the conditional
singleton-formal origin clause, and:

```text
existsE b (.rule .app site Γ
  [descriptorFormation, wholeArgumentCompatibility, completeCallCertificate,
   sourceCallIncidence, callableImage, conditional roleAndInitialCallOrigin,
   Checking value callee.returnedValue app.descriptor,
   Checking computation app.callableImage app.synthesis]
  (sourceRules Γ callee, sourceRules Γ argument))
b = ⟨site, .viewLogic, 0⟩
```

This packet proves none of those constructors and omits none from the target.

## First missing field, equation and owner

Construction stops at field 1, `descriptors`:

```text
OriginalSourceEnvironment.Logical.descriptors :
  Logical s View → List (OriginalSource.Endpoint × s.Descriptor)
```

`Logical` is declared at `OriginalSourceEnvironment.lean:249–254`.
`OriginalSourceInterpretation.Sorts.Descriptor` (`:37`) is an opaque type;
`SourceAssignment.descriptor` (`:830–835`) is a raw endpoint readout.
Neither supplies a descriptor-formation constructor for an actual App.
`Decoded.logical` (`OriginalSourceEnvironment.lean:346–352`) only folds an
already supplied write list through `put`; it does not justify the writes.

The App equation emits the actual original atom

```text
atom .descriptorFormation site Γ [callee.site, argument.site]
```

but `OriginalSource.Kernel.atom` (`OriginalSourceGeneration.lean:670–671`) is
an independent `Environment Value → Atom → Prop`. No frozen definition
constructs the App descriptor writes from the same inferred solution, complete
prior telescope and the genuine callee/whole-argument child derivations, or
identifies those writes with that atom's original interpretation. This is the
first missing owner equation, before the interface/view/assignment/witness
fields can be authenticated. Merely selecting the existing descriptor at
`⟨site,.descriptor⟩`, retaining all maps, or choosing an empty write list would
not establish that formation law.

The needed supplier belongs to the **original App descriptor/profile
formation and local admission owner**. Its required evidence is an independently
specified source-owned App construction/equation preserving those exact
children, original scope and the same solution `a`, together with its original
formation/admission law. No concrete declaration implementing that supplier
was located in the frozen inputs. This is scoped absence evidence, not an
assertion that no such construction can exist elsewhere.

`OriginalFormalAdmission.declarationFor` (`:40–45`) encodes an already selected
formal contract. `Introduction.selection` and `FormalAssignment`
(`OriginalParameterWorld.lean:57–68`) are Lambda/Parameter-indexed and use the
actual prior typed telescope. They do not produce an App contract.
`OriginalFormalAdmission.ViewPacket` (`:57–65`) accepts its viewMeaning/eta/
witness as fields and writes no descriptors/interfaces;
`localAdmissions` (`:122–132`) recognizes the formal binders and delegates
other binders to `base.logical`. Reusing it at the App would change the owner
and would not discharge the original App obligation.

## Exact remaining goal and parent application

For the original incoming decoded state, `b = ⟨site,.viewLogic,0⟩`, and the
not-yet-constructed source-owned `data`, the next admission goal remains:

```text
admissions.logical state b .viewLogic data
```

Its exact declaration is
`OriginalSourceEnvironment.LocalAdmissions.logical`
(`OriginalSourceEnvironment.lean:599–600`). `DataAdmitted` (`:611`) requires
it independently of kind equality. `admitted_scoped_iff` (`:648–653`) supplies
only the mechanical reduction after authentic environment decoding and parent
path construction; it does not prove the predicate.

The parent application is the existing
`SourceAppAdmissionR159.app_admission_iff` (`:124–154`): to reconstruct the
original App judgment, one must provide annotation locals and one occurrence,
data and decoded state, this actual admission, and all App locals and both
source children under the **same** extension. R179 supplies no new conjunct.
`OriginalAppConstructionR160.formation_consumer_iff` (`:24–41`) and
`logical_admission_consumer_iff` (`:45–55`) leave the exact original atom and
admission as inputs; neither is an App constructor. No new consumer lemma was
written. No synthetic kernel, equality-defined admission, stronger assumption,
restricted source fragment or fresh witness was introduced.

Interfaces, source-owned viewMeaning, `a`'s extended eta and its joint witness
remain unconstructed. Even after their authentic construction and admission,
the finite value/computation Checking, complete Call, whole Build satisfaction,
concrete SourceProblem and parent's shared same-solution `sameScoped` witness
remain OPEN. No production gate follows.

## Actual execution, resource use and cessation

Actual commands were short read-only `cat`, `rg -n`, `sed -n`, `nl -ba` and
the Python SHA-256/parser verifier, plus one `apply_patch` writing this handoff.
Source/hash shell commands exited 0; some batched display output was truncated,
so exact relevant definitions were subsequently reread with bounded ranges.
No source content from outside the frozen semantic input set was used.

Project files report `leanprover/lean4:v4.35.0`, library `YulangClosure`,
`moreLeanArgs = ["-j1", "-M1024"]`, and an empty external package list.
These are read configuration values, **not measured tool versions**.
No theorem was constructed, so the contract required **zero Lean/Lake/version/
build/check commands**. Delivered theorem types and `#print axioms` results:
none. Kernel acceptance, independent review and source/native proof closure:
NOT_RUN/OPEN as applicable. No failed Lean diagnostic is concealed.

The assignment bound was 1200 seconds; the 180-second Lean check budget is
unused. Aggregate active wall time and CPU/RAM peaks were not instrumented;
only short source/hash commands ran. No runtime, tests, Cargo, compiler edits,
Git mutations, new cache/environment/scratch, root import or shared record
edits occurred. There is no scratch path or generated output to transfer.

Mutual TODO `R179-APP-FORMATION-OWNER`: primary must identify/admit the genuine
original App formation/admission constructor and same-solution equation before
another construction packet. Inputs must include that exact source owner and
its actual child/solution/telescope dependencies; a result that takes descriptor
writes or admission freely is a falsifier for closure of this TODO.

STOPPED: reads and writes are finished; no process, build/check or descendant
remains active. Both leased paths are ready for primary intake; the Lean path
was never created. Independent review and adjudication remain with primary.
