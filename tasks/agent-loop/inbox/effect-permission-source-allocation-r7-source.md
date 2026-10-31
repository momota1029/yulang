# EFFECT-PERMISSION-SOURCE-ALLOCATION/20261029-r7 — source boundary check

Owner: Luna, read-only. This reuses the completed R6 extraction and confirms
its exact source owners remain pinned; it is not a second source proof.

- `crates/yu-solver/src/candidate_effect.rs` SHA-256
  `1f64d4fec8f2abceb11a48a51f5b615aa2cf605c9586ba742f15f9024a6a2717`.
  At `candidate_formal_value_pair`, Tuple rejects empty elements and any
  element with an effect row, then recurses in index order. Function visits the
  argument at reversed polarity, result at current polarity, then the argument
  and result effect ports. For the selected successful cases, omitted ports
  allocate once; negative nonempty concrete rows with no variables allocate
  once and append a local permission entry. The selected cut is the return from
  `candidate_formal_value_pair`; enclosing annotation link admission and later
  propagation are excluded.
- `crates/yu-solver/src/lib.rs` SHA-256
  `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`.
  `fresh_effect_at_level` reads `effect_bounds.len()` before pushes, checks
  `u32` conversion, reserves four aligned vectors and pushes one item to each.
  A failure after allocation can leave earlier state changes; successful-path
  transcription does not assert rollback.
- Reused R6 source extraction:
  `tasks/agent-loop/inbox/effect-permission-source-allocation-r6-source.md`,
  SHA-256 `f2a0b85bd67027f62c0e7ecd77793e88ecf0cd47e0e7f9c5cea05850f859efa9`.
  Its read-only helper survey includes reservation and resource callbacks.

This boundary check finds no new source discrepancy in R7's fixed outcome. It
does not instantiate any `HelperFrames`, prove Rust `Vec` execution or resource
success, establish the full permission prefix, or produce the exact R5
`SourcePair` witness. No source was changed, and no Cargo/test/compiler command
ran.
