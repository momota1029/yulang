# R4 read-only extraction audit

Sprint: `EFFECT-PERMISSION-NATIVE-DECODE/20261029-r4`  
Owner: Luna, read-only source lane (100-second limit).  
Inputs: R4 manifest SHA-256
`b36ac6d4f1463a3e085c7aa11dea7b0c9fa39037213bfc2c4f7293811bf1af84`.

## Source-to-observation crosswalk

Pinned R3 source hashes remain unchanged: `candidate_effect.rs`
`1f64d4fec8f2abceb11a48a51f5b615aa2cf605c9586ba742f15f9024a6a2717`,
`candidate_source.rs`
`96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`,
`lib.rs` `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`,
`LocalSource` `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1`,
and `candidate_scheme.rs`
`31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`.
The owner-export implementation is `shadow_apply.rs` rather than
`candidate_scheme.rs`; it is transitively pinned by the R3 evidence's exact
R3-input-manifest hash and that manifest's `shadow_apply.rs` entry
(`c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`).
The live path also matches the root-owned frozen current-state lease. R4's
manifest pins that chain through the immutable R3 evidence; no source change or
Cargo invocation is used here.

- `candidate_source.rs:1043–1115,1339` constructs this formal registration.
  The fixture's ordinary `f(pair: ...)` parameter is not a nested local
  binding parameter, so the `parameter_scopes` lookup falls back to
  `AnnotationScope::for_source(owner)`. `candidate_effect.rs:43–45` maps the
  exact `SourceRootId::Definition(owner)` to `AnnotationScope::Definition(owner)`.
  This resolves the scope coordinate from pinned code, independently of the
  raw redacted debug strings.
- `candidate_effect.rs:1617–1744` visits Function children before their own
  effect ports. Tuple children are ordered. The frozen tree is root Tuple;
  its first Function has atomic `Int` argument and `Unit` result; the second
  Tuple has an atomic `Int` then a Function with atomic `Int` argument and
  `Unit` result. Atomic leaves and tuple assembly do not allocate effects.
  The root `[audit]` row is retained by source traversal but is not a Function
  port call. The four actual calls, matching raw `constructor_visits`, are:
  first Function argument omitted; first Function result concrete/negative;
  nested Function argument omitted; nested Function result concrete/negative.
- At `lib.rs:10487–10517`, `fresh_effect_at_level` returns the pre-push
  `effect_bounds.len()` ordinal. `candidate_effect.rs:1694–1744` calls it once
  for each omitted port and once for each accepted negative concrete row; the
  latter immediately records that returned ordinal in the Origin event. No
  positive concrete signature pair, symbolic memo lookup, variable or hole is
  present in this frozen tree. Thus the first omitted call allocates `n`, the
  first observed origin is `n+1 = 22`, the second omitted call allocates 23,
  and the second origin is 24. This forward recurrence yields `n = 21` at the
  beginning of the Lean model's decoded slice. It accounts for all four ordered
  ports and the unvisited root row; it makes no claim that 21 is the initial
  effect counter of the whole solver invocation.
- The raw block maps parameter 0, occurrence ordinal 4, owner encoding 0,
  enclosing annotation position 0, root row position 1, first result row
  position 2 and nested result row position 3. Concrete effect IDs are 0 for
  root `audit`, 1 for `io`, and 2 for `state`; variables lists are empty.
  Origins allocate rows 22 and 24 on the two result paths, with concrete sets
  `[1]` and `[2]`. Capture 4/root 0 materializes the negative rows at nodes 17
  and 14. The two exact-owner export entries retain positions 2/3, their paths
  and concrete IDs, and nodes 17/14. These fields are recorded in R3 evidence
  revision 5 and the exact raw stderr extract; this note does not reproduce or
  alter that frozen receipt.

## Boundary

This source inspection supports the bounded source tree, scope, four-port order
and decoder-slice allocation recurrence. It does not prove the Lean
`ValueCode`/State abstraction, tag irrelevance, the `expectedAll` equation,
transitive axioms, or the decoder theorem application. It does not equate an
abstract state with an unobserved native state. Those remain R4 proof and
review obligations. Parent and production gates remain **OPEN**.

No source, Lean file, test or build was changed or executed in this lane.
