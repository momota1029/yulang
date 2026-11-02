# Sprint R234 — paper record width branch

Status: ADMITTED. Baseline: `5deacdac4`. Objective: close the selected paper's mandatory-record comparison equation and its finite upper-field lookup branch, as one leaf of the abstract Simple-sub model. Original four roots, quantifiers, and Yulang source domain stay fixed.

## Authority and fixed scope

The pinned Parreaux Simple-sub import (`notes/theory/2026-10-11-parreaux-simple-sub-proof-import.md`, §3.2.2, Fig. 9; pinned `Typer.scala:88–129`) defines record comparison by traversing each upper/right field, finding the same label in the lower/left record, and constraining the matched field types in the same direction. This packet formalizes only the finite mandatory-record fragment and the exact lookup/decomposition branch. It does not infer Yulang optional-field semantics, duplicate-label well-formedness, runtime record behavior, recursive graph completeness, or a whole solver.

Existing `SimpleSubConstraintSyntax.Sub.recordCons` and `SimpleSubRegularSolutions.recordPairs` compare complete ordered rows. R233 proves only that a particular closed-tail encoding fails; its open-tail/top caveat remains. R234 may define a separate paper-level record relation/representation, but may not silently change `Sub` or claim that an encoding is source-authorized.

## Required result

Freeze definitions for finite labeled fields, the paper's required-field relation, and the actual lookup branch that emits child comparison obligations. Prove a checked theorem that successful branch execution is equivalent to the frozen relation (or state and prove the exact one-way soundness direction if algorithm output conventions make equivalence inapplicable). Include the two-field-to-one-field width case, missing upper label rejection, label permutation, and recursive child-obligation preservation. Keep all fields required and child comparisons directed lower-to-upper.

Apply this result to R233's ground width pair at the paper-relation level. Do not claim that current closed-tail `Sub` accepts it. Do not claim Yulang source embedding, parent-root reduction, principality, termination, or Rust correspondence unless a separate reviewed equation actually supplies those steps.

## Lanes and verification

One registered `lean_prover` owns only `notes/theory/lean/YulangClosure/PaperRecordWidthR234.lean` and `tasks/agent-loop/inbox/paper-record-width-r234-proof.md`. It must freeze writes before Luna invokes the pinned project checker. Luna owns cache use and Git. One fresh nonauthor `spec_auditor` reviews source authority, scope, and exact theorem application; one fresh `lean_prover`-qualified theorem audit is not substituted for primary kernel/type/axiom checking.

Use only `notes/theory/lean/.lake/build`, pinned Lean 4.35.0 / Lake 5.0.0. No new worktree, environment, target, or cache path. Additional apparent `.lake` growth cap: 64 MiB. No Rust edits, Cargo, default build, tests, or expected-output changes. Preserve all UNKNOWN/quarantined leases. Stage exact R234 paths only.

## End gate

Record full declaration types and axiom audits, exact source pin, falsifiers, checker result, cache growth, independent review, and exact limitations. Parent-premise delta is zero unless this leaf is actually composed into an unchanged original root. If a premise remains source-unjustified, report it without renaming it as a proved embedding.
