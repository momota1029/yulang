# Shadow marker for the CALL_TYPE CI-ArgFrame obligation

Date: 2026-10-07

Baseline: `83002c582e3c7977b28fb4734ea989ab115f8349`

Claim class: default-off unresolved-premise plumbing; no semantic or production authority

## Scope

The approved shadow lane permits retaining settled structure and naming
unresolved semantic premises while the proof work continues. The canonical
CALL_TYPE node remains CONDITIONAL-CLOSED. Its CI-ArgFrame leaf requires, for
every retained CalRet witness, one compatible extension that preserves that
witness and jointly establishes argument typing at the actual returned `C1`
and `ArgCompatible` with the actual returned provider `U`, under the same
original scope/incidence/`xi`.

`crates/yu-hir/src/shadow.rs` now records this requirement once for each
retained `Apply` as
`Premise::JointArgumentTypingAndActualReturnedProviderCarrierCompatibility`.
The HIR structural phase has no actual provider, returned world, evidence, or
`xi`; the marker creates none. It supplies no constraint conversion, Q-based
discharge, application typing judgment, or semantic acceptance. The solver
state remains `ApplicationTypingRuleUnresolved`, with no semantic facts.

The marker is in the general per-Apply inventory, not the direct-Name-only
source-use list. Thus grouped, computed and indirect callees retain the same
unresolved requirement. Existing Core and solver lifecycle code forwards HIR
premises generically and was not changed.

A subsequent bounded constructive audit of the fixed Name/Name cut made the
pending semantic head more concrete. From `Gamma(x)=Value(Ax)`, typed-core §6
produces `Result(Value(Ax))=Comp(empty,Ax)` and the inert
`Return(lookupρ_X x)` skeleton. After granting independent initial typing and
an actual callee Return, the required conclusion remains, for **every**
retained CalRet extension `w_f`, one compatible `w1 >= w_f` that preserves its
evidence and jointly establishes argument `Typed_X` at actual `C1` plus
`ArgCompatible_X` with `CarrierContract(U)`. The missing source head introduces
that `result(name x)` at the actual returned-provider carrier port. It needs
both independently justified Name/Return descriptor typing and soundness of
the original whole-carrier argument check. Neither generated constraints,
Name lookup/C1=C0, nor provider view alone supplies the two judgments. This is
a bounded premise localization. A fresh compiler-referee delta review found no
findings on the derivation, quantifier order, or status boundary. It is not a
new semantic rule or a CALL_TYPE closure.

## Review and verification

Independent compiler-referee review passed the conjunction, scope and
non-discharge boundary with no findings. Independent regression review passed
all explicit inventories and aggregate counts with no findings. It verified
that direct-use premises remain unchanged, per-Apply counts increase by one,
the 4,000-Apply structural case scales from 20,000 to 24,000 pending rows, and
production Core/solver files are unchanged.

Focused checks passed:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-hir --features shadow --lib shadow_ -- --test-threads=1
  51 passed
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-hir --features shadow --lib shadow::tests:: -- --test-threads=1
  26 passed (4 overlap the preceding filter)
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-core --features shadow --test shadow_annotation_header_membership --test shadow_binder_use_groups --test shadow_derivation --test shadow_directional_incidence_join --test shadow_feature --test shadow_legacy_application_provenance --test shadow_raw_structural_inventory -- --test-threads=1
  31 passed
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-f5 --test shadow_captured_source_retention --test shadow_f5_differential --test shadow_legacy_local_application_provenance -- --test-threads=1
  9 passed
git diff --check
  passed
rustfmt --edition 2024 --check on changed Rust files other than the file with an existing unrelated formatting difference
  passed
```

No broad workspace/default-feature suite or performance measurement was run.
Only one Cargo process ran at a time. This is not an old-infer semantic
differential; it checks that structural requirement identity and unresolved
status survive existing shadow lifecycle paths.

`cargo fmt --check` was also attempted and failed on existing formatting drift
across unrelated committed files. The changed solver differential file has one
formatter suggestion at unchanged line 531, outside this diff; its new line
and every other changed Rust file pass targeted rustfmt. No formatting rewrite
was applied.

## DAG and adjacent attacks

The canonical DAG remains 90 nodes / 196 edges: 7 CLOSED, 20
CONDITIONAL-CLOSED, 43 OPEN-PROOF, 19 OPEN-SEMANTIC and 1 IMPLEMENTATION-ONLY.
No node, edge, or status changed. HIR_WIRING now records this pending marker as
one existing shadow-plumbing slice; it does not claim CALL_TYPE evidence.

Concurrent bounded attacks did not close their target gates:

- **ORIGINAL_ASSOC P2 remains OPEN-SEMANTIC.** FVIEW §2 and typed-core §§2,
  6, 9 treat original paths, `Flow`, owner/view contracts, typed `p0` and
  shared `(nu,K,D)` as supplied inputs or open source-generation work. The
  complete Call equations give a typed-call skeleton, not an introduction of
  original `slot ∈ Slots(beta)`, contribution membership and joint owner/view
  incidence. The smallest missing producer must jointly return those fields
  and `OriginalAssocType_X` at the same original scope and `xi`, preserving
  the full licensed witness domain. No IDs, endpoint equality or Q result
  supplies it.
- **REC_DESC remains OPEN-PROOF.** FH reflection needs exhaustive failure
  inversion of `S ∧ ¬DescMem` to an admitted history refuting every extension;
  one failed extension does not invert `forall h. exists e`. The more useful
  simultaneous route would jointly introduce both cyclic Return descriptors
  and their own-root/world validity from independent external bases, actual
  K, complete ordinary clauses, nonrecursive guards and CompleteMem facts.
  No existing rule supplies that acceptance without circularly assuming a
  world whose elimination already entails the target members. The route
  comparison changes no status.
- **INIT_WORLD remains OPEN-SEMANTIC.** The last-rule audit separates a
  source-owned root, supplied by its source constructor, from an independent
  semantic import whose source/import contract must supply an open
  descriptor/provider clause at its importing incidence. The minimum W0 rule
  must take the external base excluding the imported root, formal punctured
  callable and argument holes, source/import incidence and same-original
  `(C0,xi)`, plus independently specified joint provider/reference/state/
  role/profile/activation/owner compatibility; it must extend the root
  environment jointly while leaving holes open and preserving old incidences.
  No source transition, receipt, activation, store update, checked membership,
  or extended-environment validity can be a premise. Existing context,
  source-contract and inert-introduction clauses do not supply this rule.
  This is bounded missing-premise localization, not a proof of nonderivability.
- **ALL_VIEW remains OPEN-PROOF; PRINCIPAL stays CONDITIONAL-CLOSED.** No
  actual designated-export Direct certificate combines nonidentity `VIncl`,
  resolver conformance, widened allowance, paired Option 2 extras and the
  same original source/query witness. The displayed restricted Function rule
  needs matching non-coverage interface; the independent decorated result
  inclusion and actual-export consumption remain open.

No admitted-source counterexample or pair of authority-consistent meanings
with different observables was obtained. Production cutover remains gated by
the existing source, semantic, principality and conformance obligations.

## Next attack

Construct the ordinary simultaneous recursive Return/root-installation
introduction rule from independently grounded inputs, while separately
attacking the original K-Owner introduction that produces P2's typed
`p0`/shared-root incidence. A proof of CALL_TYPE's actual CI-ArgFrame inputs
must replace the new marker, not treat it as evidence.
