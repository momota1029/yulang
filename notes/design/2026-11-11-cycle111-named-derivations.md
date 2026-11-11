# Cycle 111: independent named structural derivations

Status: Draft implementation design, 2026-11-11.

## Objective and scope

Close the source-name boundary for the finite static structural associated fragment. The initial target is not another finite-index restatement: define a judgment on `Atom Nat`, whose seed, structural decomposition, type transitivity and associated-declaration rules mention original names. Prove that allocation preserves and reflects this judgment, then give the existing ordinary solver an exact contract using those named derivations and named valuations. Follow with an unchecked source syntax checker if time permits.

No new language semantics: existing ordinary grammar, scoped single-placeholder templates, scalar associated decoder and declaration resolution are retained. No dynamic invocation identity, new child lifetime policy, parser adequacy, K2, four-way role selection or principal typing claim.

## Data and independent judgment

For arbitrary `env`, `roles`, structural `src`, define `Derives env roles src a` on `Atom Nat` by seed membership, the existing structural split relation, syntactic transitivity on type atoms, and `Step env roles q head result` with both receiver bounds. Associated conclusions are both output bounds. Neither allocation nor a solver result appears in the judgment.

The bridge is bidirectional: source derivations rename to the finite carrier; every finite derivation reads back to a source derivation. Required source-only roundtrip is proved for names appearing in input atoms and occurrence endpoints; absent names must never acquire accidental evidence from the total allocator's dummy slot.

Target: for every present source name and scalar head, computed finite Known iff both named bounds are independently derivable. For every named valuation, final ordinary models iff input atoms and all independently activated source equations hold. This advances source_boundary_adequate and the static fragment of saturation; the five general B4 bridges remain open.

## Validation and publication

Read existing Y2 audit ROLE-MORE-001/002/003/005 before implementation. Y2's where differences are not adopted. Focused builds only, scoped axiom audit, negative/positive boundary tests. Publish each coherent subgoal with imports and Audit registration, using GitHub API and expected-head non-force ref updates. No full project build or full Audit.

## Second subgoal: raw structural source boundary

After the named judgment closes, replace `Program` supplied with scope proofs by raw occurrence records containing endpoint names, associated name and ordinary `Roles.Goal`. A recursive checker must accept exactly raw programs whose templates use only placeholder zero. Erasure of a checked program must be inverse to checking, preserving order, multiplicity, roles and names. Define the raw associated step and raw derivation without checked templates. The public entry checks scopes, computes allocation and ordinary grammar, runs finite closure and the ordinary solver, and returns its computed source/state package. Target success iff scope, ordinary grammar and existence of a raw named model. This does not parse surface text or interpret out-of-fragment templates as language errors.
