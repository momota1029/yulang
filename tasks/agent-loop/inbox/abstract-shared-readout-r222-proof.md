# R222 equation-construction handoff — revision 1

- Sprint: `abstract-shared-readout-r222`, contract SHA-256
  `d493b155e00c67e472aa88aaed62068bb412dcd071b4e87acb51743b2454e73d`.
- Assignment/handoff ID: `R222-EQUATIONS`; revision **1**.
- Worker: `/root/r222_equations`, current-session primary dispatch; no children.
- Requested registered role/model/effort: `prover`, Sol/high. Observed
  model/effort: **UNKNOWN/UNKNOWN**; no in-place model-switch claim.
- Outcome: **candidate equations plus source-qualified construction obstruction**;
  no completed compiler, checked Lean theorem, review or production authority.
- Exact owned paths: this inbox and
  `notes/theory/2026-11-02-abstract-shared-readout-r222.md` only.
- Author of both: `/root/r222_equations`; no contributing descendants.
- Artifact SHA-256:
  `8435d2610df65be3e547eaedeff8796228dec78628143b1ffe95d982b58e143a`.
- Freeze time: `2026-11-01 21:37:08 UTC` (artifact hash observation).

The original parents remain `SourceProblem.InferenceSoundness`,
`SourceScopedCoverage`, `PrincipalCoverage`, and `InferenceTermination` in
`Contracts.lean:128–154`, with original quantifiers, source domain, scopes,
shared witnesses and instance ordering. **Parent delta 0; 0/4 roots and 0/5
packages.** No supplied Store.Satisfied, LawfulStore, source judgment, graph/ref
solution, successful history or target conclusion was used as an input premise.

## Exact stop result

An actual `CoreProblem` with one level-0 Value row, births `[0]`, no Value
references, and sole demand `⟨⟨value,var 0,var 0⟩,0,0⟩` passes the existing
`inputValid`. Its `initial.insertPendingUpper` succeeds and produces the
existing `CoreState` data `upperBounds=[var 0]`, `lowerBounds=[]`,
representatives `[0]`, pending `[]`, and retained clause `var 0 <: var 0`.
This is an actual R212 partial operation; no full accepted run is claimed.

Paper Fig.12's negative singleton meet is syntactically `μn.n`. The explicit
Top-seeded finite fold, also used in R212, presents this as `μn.(Top∩n)`.
The artifact makes the distinction explicit: these are syntax/equation
presentations, not a checked recursive-semantic equivalence, and neither is
claimed equivalent to Top. The raw paper form has no constructor root; the
explicit fold gives Value nodes `[intersection 1 0, structural Top]`, root 0.
That graph is Valid, but not Guarded. `FiniteLattice` of node 0 would require
a strictly smaller derivation of exactly itself through the right meet child.
The same discriminator works for an Effect row.

The first missing premise is a derived guard-producing normalization with
literal Fig.12 correspondence, or an actual transition invariant preventing
this output. R212's existing insertion provides no such invariant. Rejecting
the cycle merely because `checkGuarded` rejects it would exclude an actual
operation output without the required algorithmic derivation. Choosing Top
does satisfy this reflexive store but does not establish that correspondence.
This is not a proof that the store is inconsistent or that all possible
semantics-preserving encodings are impossible.

Fig.12's positive seed is frozen under the original context C. R212's extra
positive key is **not adopted**. The artifact includes the recursive Function
discriminator producing different nested binder syntax and does not promote
the candidate simultaneous-row sharing transformation to a proved equivalence.

The finite contextual syntax construction, direct lexical-binder graph
encoding, required graph/ref/store theorem shape and its missing premises are
recorded in the artifact. Upper-only, two-row bound cycles, mixed polarity,
recursive Function, all four ports, duplicate representatives and both kinds
are represented as discriminators. A combined Value/Effect cyclic fixture
keeps both kinds. A single SCC containing both kinds is impossible in the
current grammar because Effect terms have no Value child. Finite structural
row-spine interpretation and representative-bound merging remain open seams.

## Sources, hashes and reuse

All eight frozen R222 mathematical dependency pins matched their contract.
Additional directly read interface/authority hashes are recorded below.

```text
023635d283f9a00e906ec965a6eaa5595eab21f2b93f353a1d5ea0ede0bffb6c AbstractSimpleSubCore.lean
b162fbde8a83096f5bd2e5e9efe076ce07e7cfa8306e27ab551e46f1d359e1f2 abstract-simple-sub-core-r212-artifacts.json
1270e3407ddeef881020610b094709ebba07b62a97e54712bcc4b139ef8e78d0 SimpleSubLatticeGrowingInference.lean
c534c060dfde84f2817fbaa53222f430b59d9b6377cfacedabeca7b9b4b8ffa3 SimpleSubLatticeInference.lean
755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29 SimpleSubRegularSolutions.lean
a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6 SimpleSubConstraintSyntax.lean
1d4f46b9e9d2375d31284957c4157906df9fd00477fc976d43204262dedcb805 2026-11-02-original-literal-readout-r221.md
f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8 2026-11-02-literal-l1-adoption.md
55533eee35ed7058abd125ac0e01d8f29b8c0534800018d254c1bd9f9c0bb79b SimpleSubLatticeCertificates.lean
2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e Contracts.lean
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81 2026-10-11-yulang-inference-top-level-principles.md
c69d0c24f540024985205401c1405d8d34cbd08439a82e4a7cddb2b7e5682185 20261102-abstract-simple-sub-core-r212-review-outcome.md
5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698 /home/momota1029/rust/simple-sub-reference-paper.pdf
```

Paper read: Fig.10/§§5.1.1–5.1.2, printed pp.124:24–25; Figs.11–12 and
§5.3.1, printed p.124:26. The paper explicitly permits unguarded recursive
syntax, while restricting when recursive subtype hypotheses may be used.
Reused R212 actual row/insertion definitions, upper-only and four-port
discriminators and fresh review's unresolved Fig.12 seam. Rejected arbitrary
ordinary free-name uniformity and an assumed simultaneous-sharing equivalence.
R221 original-source obstruction remains intact; this packet supplies no new
source judgment or Rust/native correspondence.

## Checks, resources and next owner

Read-only source inspection, `pdftotext -layout` to stdout and SHA-256 checks
only. The pinned configuration was read: Lean 4.35.0, project `-j1 -M1024`,
no external packages. **No Lean/Lake checker execution assigned or performed;
delivered checked theorem set: empty; axiom-dependency reports: none.** Proposed
theorem types are labeled unimplemented in the artifact.

Budget ≤900 seconds; completed within the envelope. No heavy process, cache,
test, Rust, Cargo, Git, network, new environment or scratch output. All new paths
are exactly the two leased Markdown files; no other write occurred.

Next step belongs to Luna at this decisive obstruction boundary. A newly
assigned focused Lean packet could prove the emitted self-bound fixture and
`¬ selfUpperGraph.Guarded`; that would formalize the obstruction and would
still leave parent delta 0. A successful complete readout needs the missing
normalization/correspondence theorem before promotion.

Mutual TODO **R222-GUARD**, owner Luna to assign: prove a guard-producing
normalization of the literal equations on actual emitted bound-only cycles.
Falsifier: this one-row input must neither be excluded without derivation nor
reported as Guarded under the failing direct graph. No semantic change is
requested or performed. Mutual TODO **R222-ROW-MERGE**, future equality-transition
owner: retain every physical row bound under duplicate representatives;
falsifier q=[0,0] with a unique retained bound in row 1.

**WRITES_STOPPED** at revision-1 freeze. No active process or descendant;
no descendant lease to reconcile. Both paths are frozen for Luna intake and
fresh review. Assignment ended at its exact stop condition; parent remains open.
