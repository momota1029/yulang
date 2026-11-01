# R184 v4 stop — original App bridge — 2026-11-02

Status: **parent OPEN; no theorem, counterexample, or source-correspondence
closure**. The proof assignment stopped before writes or Lean execution when an
exact structural definition it needed fell outside the frozen inputs. All 24
contract inputs matched at assignment start.

## Existing mathematical results actually applied

`SimpleSubLatticeInference.lean` and its pinned imports provide:

- `YulangClosure.SimpleSub.Lattice.accepts_sound`: graph validity, guardedness,
  and demanded `RegularSub` comparisons.
- `checkStore_sound`: structural `StoreSatisfied`, from checked decoding and
  certificate acceptance.
- Publication transport: structural clause preservation under its exact
  guards.

These results do not establish original source admission, App's complete Call
premises, contextual effects, or the same original scoped witness. The source
module itself leaves original Call/effect correspondence separate.

## First unsupplied parent premise

`OriginalSourceGeneration.lean:112–123`, whose `Kernel` is defined at
`:670–685` and `Satisfies` at `:842–848`, requires the App clause to supply:

```lean
∃ candidate,
  original.admitted environment ⟨site, .viewLogic, 0⟩ candidate ∧ ...
```

The full clause retains the atoms `descriptorFormation`,
`wholeArgumentCompatibility`, `completeCallCertificate`,
`sourceCallIncidence`, and `callableImage`, plus the conditional sibling atom
`roleAndInitialCallOrigin` when `singletonFormalCall context callee argument`
holds, and both original checking goals.
`OriginalSourceEnvironment.lean:1100–1106`'s `functionKernel` preserves
`original.atom`; `:599–610` leaves logical admission at
`LocalAdmissions.logical`. No map from generated Simple-sub graph/store
constraints to these source atoms/admission and their common scope witness was
found in the inspected pinned modules. This is the first parent edge left open,
not a source-qualified counterexample and not a global absence claim.

## Exact boundary and execution receipt

The proof attempted to inspect `Regular.expandNodes`, referenced by
`SimpleSubLatticeCertificates.lean:149–152`. Its import route is the unpinned
`notes/theory/lean/YulangClosure/SimpleSubRegularConstraintSoundness.lean`;
that file and its ultimate declaration owner were **not read**. Stop was
requested at that boundary.

No Lean/checker/build/test ran. No output, scratch, or generated file was
written; both leased output paths remain absent. No counterexample was
constructed. The worker confirmed no active commands or descendants and writes
stopped within its 1800-second grant; exact elapsed time was not instrumented.

The independent review of the parent dependency map passed. A fresh review of
this stop record found only locator and inventory omissions, corrected here;
it verified the substantive blocker conclusion. Neither review closes a
theorem. Principality, termination and Rust/native correspondence remain
separate open gates.
