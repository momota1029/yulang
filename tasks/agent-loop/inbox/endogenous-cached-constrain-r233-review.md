# R233 fresh independent review

Disposition: **PASS for the frozen, narrow relation obstruction; MODEL-INCOMPLETE for endogenous constraining; parent delta zero.** No BLOCKING, major, or minor defect found in the submitted theorem statements or their stated scope. The missing model equation is a blocking prerequisite to continuing the proposed operation theorem, not a false theorem in this submission.

Reviewer: `/root/r233_width_obstruction_review`, fresh nonauthor. Baseline supplied by primary: `d47635c57d3c34099da999dc41f2475ce202be5a`. Initial review used actual declarations, governing authority, PDF Fig.9 and reference source before reading the author's explanation. No builds, tests, checker, cache writes, descendants, or Git operations were performed. Only this explicitly leased review receipt was written.

## Frozen bytes

Direct SHA-256 checks matched all three assigned targets:

| Artifact | SHA-256 |
| --- | --- |
| Contract `tasks/agent-loop/sprints/endogenous-cached-constrain-r233.md` | `30873001ab25326e8d02b501c245eefab828021ee1a856cb23666bd085484891` |
| `AbstractCachedConstrainR233.lean` | `3a0de10775554603d9c906bde1ec44c0d53d009044e354e69554e61c3ecff4f4` |
| Author handoff revision 2 | `b8b05a549300fa3837de22718c1d9da8ce504a3226c1f5ec3817b24b1f2d7cf1` |

Actual imported syntax: `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6`; Contracts: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`. Abstract core/R229/R230 admission hashes also matched. Source import: `cd2b84a84d16be8856766f0514a2f400cf224ac95b6e81e42d4a7a875036e113`; actual PDF: `5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698`; actual Typer.scala: `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9`.

## Mathematical validity and cause

`SimpleSubConstraintSyntax.lean:83–111` defines a deliberately partial structural relation. Its record rule requires equal head label and optional flag plus a comparison of entire tails. R233 identifies a limitation of using that relation with the specific closed-row embedding as the stronger constraining theorem's conclusion. It does not repair the model or hide a downstream symptom.

The new module's `recordDepth_mono` (`:44–101`) covers all 16 constructors. Reflexivity is identity; transitivity composes implications; bottom has empty interpretation and top universal interpretation. Union introduction/elimination and monotonicity use disjunction; intersection projection/introduction and monotonicity use conjunction. The record rule invokes its tail induction hypothesis after decrementing depth. Function, tuple and variant cases have false antecedents. All four Function premises and both kinds remain in the induction domain. This interpretation does not validate Function variance or source semantics, and the submission does not claim that it does.

The invariant is nonvacuous: `recordDepth widthLower 2` reduces to `0 = 0`; `recordDepth widthUpper 2` reduces to `1 = 0`. Consequently `width_not_sub` (`:119–123`) excludes *all* derivations, including lattice/transitivity detours. It is not merely failure to match a direct constructor. `width_field_reflexive` (`:115–116`) is a real positive instance. No existing relation, source rule or constraint definition is changed.

`Constraint.Satisfied` is explicitly `Sub` after substitution (`SimpleSubConstraintSyntax.lean:138–139`). Substitution traverses records and fixes atoms/recordNil (`:53–67`). The concrete pair contains no variables, so `width_rejected_by_every_valuation` (`R233:127–130`) follows definitionally for every valuation. This quantifier concerns the defined structural satisfaction relation; it says nothing about all source typings or all alternative semantic models.

## Paper/reference correspondence

I read the actual local PDF's printed p.124:21, Fig.9, and reference `Typer.scala:88–129`. Fig.9 iterates right fields, looks up matching left labels, then compares field types. For `(0:A,1:B)` versus `(0:A)` there is one successful child comparison. The pinned implementation's `:109–114` has the same width behavior; `:93` immediately accepts the shared canonical A object. This avoids its separate limitation for distinct equal-named primitive objects. Numeric Lean labels/atoms are an explicit finite embedding of distinct labels and canonical leaves, not a universal reference-object equivalence theorem.

Paper caches every comparison; reference caches only variable-endpoint comparisons and returns early on identity. Both accept this example, but their cache states differ. Neither paper execution nor reference execution is formalized by the new module; only its missing closed-row `Sub` conclusion is formally refuted. No source-qualified counterexample to Yulang, inference soundness, a complete solver, or every existing model follows.

## Existing lattice route checked

Inspected hashes:

| Module | SHA-256 |
| --- | --- |
| SimpleSubLatticeInference | `c534c060dfde84f2817fbaa53222f430b59d9b6377cfacedabeca7b9b4b8ffa3` |
| SimpleSubLatticeCertificates | `55533eee35ed7058abd125ac0e01d8f29b8c0534800018d254c1bd9f9c0bb79b` |
| SimpleSubRegularSolutions | `755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29` |
| SimpleSubRegularConstraintSoundness | `1d2266867115fc27afe39dbb80a3ca0e8f75247a2e16b739145137e83999de33` |

The existing route supplies real conditional results, including `Lattice.accepts_sound` (`SimpleSubLatticeCertificates.lean:476–484`) and decoded `checkStore_sound` (`SimpleSubLatticeInference.lean:322–330`). Their premises include actual graph decoding and acceptance; their conclusion is graph-indexed RegularSub/StoreSatisfied, not an endogenous transition.

Their direct record equation also requires matching full rows: `Regular.recordPairs` (`SimpleSubRegularSolutions.lean:142–148`) zips equal labels/optional flags and returns none on unequal lengths; `expandNodes:168` uses it. `NodeRel` (`SimpleSubRegularConstraintSoundness.lean:87–89`) and `recordPairs_holds:45–57` confirm the same ZipRel obligation. Lattice structural expansion (`SimpleSubLatticeCertificates.lean:149–158`) reuses that equation. Therefore these inspected declarations do not supply the missing Fig.9 record-width equation for the unchanged direct decoding. This is not a theorem excluding every possible graph, alternative embedding, or other repository model. R184's stop receipt correctly keeps original App admission and complete Call/contextual effects open; accepts_sound is not automatic source reconstruction.

## Required equation, owner, and falsifier

Before continuing, Luna must assign the mathematical-model/embedding owner to freeze and justify the independently defined record consistency/subtyping equation consumed by generation, constraining and coalescing/readout. At minimum, for required distinct fields it must express: each right label exists on the left and its left field type relates to the right field type; extra left fields are permitted. Specify how this equation maps to the existing Term representation or a justified alternative. Optional rows, effects and all original source constructors remain separate obligations; this example authorizes none of their missing meanings.

An overstrong claim that “Sub cannot express any width demand” already has a concrete falsifier: encode the right requirement with open tail `recordCons 0 false (atom 0) top`. The existing `Sub.recordCons` proves the comparison from the unchanged widthLower, using reflexivity on atom0 and `Sub.top` on the extra left tail. This does not refute `width_not_sub`, whose right tail is recordNil, and does not establish that this open-tail encoding is the approved source mapping. A source-corresponding approved mapping/bridge of this sort, or an existing independently justified width relation with the needed composition equations, would falsify a global missing-meaning claim. The submission's explicit frozen-pair qualification avoids that overclaim.

## Verification, parent application, stop evidence

I did not rerun verification. The primary directly confirmed during this review its actual pinned `check_lean.py` invocation for the frozen module and all four named theorems, explicit project/Lake paths, timeout 180, Lake 5.0.0 / Lean 4.35.0, build and complete type/axiom audit exit 0. Every theorem's reported `#print axioms` result was “does not depend on any axioms.” The retained receipt is the frozen author handoff `:244–271`; these are attributed primary execution receipts, not this reviewer's execution or independent replay. Reported cache growth is +144,032 bytes. The module's embedded audit commands alone would not establish these facts.

The unchanged root definitions remain `Contracts.lean:128–154`. R233 supplies no original generated-constraint solution, source judgment, or sameScoped witness, and no actual transition accessibility. R229's no-opposite-replay theorem and R230's separately assumed satisfying original valuation do not supply those missing facts. All four roots and all five packages remain open; types/effects, full source domain, shared witnesses and native correspondence remain intact. No production promotion is supported.

The author handoff `:275–293` reports no children, cache/scratch creation or active background work and freezes both leased files. The primary directly confirmed the author stop at `2026-11-02T00:38:32Z`. This is authenticated author/primary stop evidence, not independent process monitoring. This reviewer has no descendants or active commands and stops writing this sole review path upon submission.
