# R67 independent review — revision 1

Sprint `EFFECT-PERMISSION-QUALIFIED-REIFICATION/20261031-R67`.
Reviewer: `/root/r67_review` (`compiler_referee`), fresh and read-only.

## Verdict

**FAIL for integration pending one major finding.** The finite Lean algebra is acceptable within its stated conditional scope.

## Major finding — resource failure becomes a semantic mismatch

At `crates/yu-solver/src/candidate_receiver.rs:892`, `.ok()?` discards
`CurrentEmissionGap::SearchLimit` from the allocations/conversions at lines
755–758, 761–762 and 781–782. `InventoryPackage::capture` subsequently converts
that `None` into `BoundMismatch` at line 3533. A valid package whose
reification allocation fails therefore reports a source/evidence mismatch.
This violates the sprint requirement to return failures through the existing
private gap/error channel.

Minimum closure: preserve the reification `Result` through the capture call
chain. Returning `SearchLimit` must remain distinguishable from failed root
validation. A focused source trace suffices under the current prohibition on
tests/builds.

## Other reviewed properties

- `HirOccurrenceId` equality includes artifact pointer identity. Occurrence
  ownership is checked before enumeration; package/table identity is checked
  before reading owner-local coordinates.
- Complete facts and provenance retain order and indices. Distinct provenance
  edges sharing one `FactId` survive; duplicate occurrence/slot keys and
  dangling fact references reject.
- Lean's first-appearance `eraseDups` matches Rust's enumeration. Complete
  competitor-list equality prevents discarded competitors from producing a
  successful read.
- The final retained stdin contains the exact frozen R67 module body and
  verbatim R65 `readSelectedAt_iff`. Its digest matches the receipt; retained
  exit is 0, with 19 theorem types and complete axiom reports using only
  `propext` and `Quot.sound`. This authenticates retained evidence, without
  independently rerunning Lean or establishing unsliced project integration.

## Authenticated hashes

| Artifact | SHA-256 |
|---|---|
| Rust receiver | `2ad3418d9bca0c8c5c4d3c27c3fa06ee28ad653e1f5e5a8adef2f202c21fd35a` |
| R67 Lean module | `4b40cc5f1e832eaac226235d7c9c8a974bd3c6b895fa2d9fab7051d3271ee4e1` |
| Rust handoff | `4c52c08ac16047f82a31656491c1c8b5cf2b2b295bc06d7020cb5f906dfea327` |
| Proof handoff | `ee4bc812c85e76de7ee1aa673e89471e3c6eb5ce57d1787ca94e590059d4850f` |

Contract, baseline receiver, pinned direct dependencies and every retained
dependency hash also match.

## Open limits

`SemanticFact` supplies only identity and two `Term`s; no reviewed owner
interpretation constructs each row's four raw/canonical endpoints. Lean starts
with an R65 inventory carrying those fields. Actual Rust/package correspondence,
pointer/store/arena authenticity, native resource equivalence, complete
Context extraction, actual native Runs and original A/B remain open. This is a
partial checkpoint, not completion of the fixed Rust-to-Lean outcome.

Review was read-only throughout: no writes, builds, tests, Lake, formatter, Git
mutations, author contact or descendants. Reviewer STOPPED.
