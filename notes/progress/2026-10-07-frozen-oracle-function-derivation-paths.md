# Frozen Oracle Function derivation and typed-path trace

Date: 2026-10-07
Status: bounded historical characterization; compiler-referee review passed
Frozen Oracle: `/tmp/yulang2-oracle-rebuild`, `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Yulang3 baseline used for trace: `deb5635ecc895a49b7f13d750374338003fd01e1`
Authority: historical implementation evidence only; no semantic or production authority
Method: read-only source trace; no Oracle execution

## Question and result

The open `ORIGINAL_ASSOC` gate still lacks an independently interpreted
source producer for the original owner/view-kernel contribution of ordinary
`f x`. The bounded historical trace found a source-origin and structural
derivation chain, followed by a separate projection-based typed-path
collector. It found no pre-query producer for the original
`(beta,p0,j_call;s,c)` association, complete contribution, or shared `xi`.

This is a preservation/attribution mechanism downstream of ordinary source
lowering, not the missing source producer. Oracle constraint labels, projection
results, and consumer behavior do not define current language meaning.

## Historical chain

Paths are relative to the pinned Oracle checkout.

1. `crates/infer/src/lowering/expr/tail.rs:630–689` allocates an
   `ApplicationArgument` origin before submitting the callee's negative
   Function demand (`tail.rs:535–586`). Expected-occurrence provenance is
   registered afterward with an empty path. The origin preserves a route to
   the source application across eager constraint submission, but contributes
   no original static slot or complete source judgment.
2. `crates/infer/src/constraints/machine/propagate.rs:211–269` emits child
   constraints for Function argument, argument effect, return effect, and
   return ports, with structural derivation labels. For the argument-effect
   passthrough case (`:235–245`), the emitted edge can connect the upper
   argument-effect endpoint to a stack-stripped upper return-effect endpoint
   (`:401–410`). Therefore a derivation label alone is not an unchanged typed
   path.
3. `crates/infer/src/constraints/machine/entry.rs:1427–1507` retains
   `(parent, rule)` provenance on admitted canonical child records. Duplicate
   constraints can accumulate derivations; trivial canonicalization emits no
   child record. `crates/infer/src/constraints/explain.rs:1302–1331,1739–1757`
   later traverses structural parents and root origins. Portable conversion
   retains Function labels and the `ApplicationArgument` source category
   (`:1975–1985,2065–2083`). This is conditional explanation reachability,
   not an exhaustive or unique source-path inventory.
4. `crates/infer/src/generalize/provenance.rs:204–280,308–338` constructs
   `GeneralizedTypePathStep` values by walking projected bound shapes in
   `WitnessCollector`. It does not concatenate the explanation labels into a
   complete typed path. `crates/infer/src/analysis/session/occurrence_provenance.rs:228–322`
   and `constraints/mod.rs:2786–2793` later export generalized witnesses as
   definition-owned occurrence keys with converted paths and proof roots.
   This path is downstream of projection and coverage limits.

Conditional on an admitted application root, retained nontrivial child
records, intact provenance links, and sufficient explanation budget, a
selected structural-parent chain can reach its application origin and retain
its derivation labels. Canonical fan-in, replay parents, and multiple origins
prevent upgrading this to a unique position inventory. The projected
collector separately supplies selected typed paths, not a complete original
source contribution.

## Boundary and next step

The historical chain supplies no original `beta`/`Slots(beta)`, formal
owner/receiver correspondence, original `xi=(nu,K,D)`, complete Call
contribution, or exhaustive source licensing/admission. Endpoint identity,
source spans, structural labels, successful comparison, and projected path
equality cannot be assigned those meanings by analogy. This result does not
close `ORIGINAL_ASSOC` or any dependent gate.

The search was bounded to the cited application, Function propagation,
constraint-entry/explanation, generalization, and occurrence-export routes.
It is not a repository-wide absence proof. Oracle use is limited to historical
mechanism discovery and later attribution audits; current source rules remain
governed by the approved Yulang3 designs and explicit user decisions.

No Oracle execution, builds, tests, code edits, or Git mutations were part of
the source trace. Resource counts were not instrumented. An independent
compiler-referee review passed and confirmed the pinned Oracle HEAD and the
seven cited source files were unmodified in the historical checkout. This
review validates the cited bounded trace, not repository-wide absence or
current source adequacy.
