# R139 frozen artifact review — changes requested

Reviewer: `/root/r139_review`, fresh independent static review.
Baseline: `4c1d58a646a1101c080659ebfed6ae7862d8aded`.
Contract v1 SHA-256: `717acc2e9c3bd70f19a0b74854802952ab0eea6ccf62fab104c5075997ee4afb`.

Reviewed frozen bytes:

- Rust source handoff: 20,752 bytes, SHA-256 `deec8b482fbc9d1c092caaaf2a7ebbeba821c51f22c529058edd2a5ee4d7941f`.
- Lean module: 11,350 bytes, SHA-256 `5bf4e97160a6114c5ae320883fcfbd71045f0b2500c15de35df0def5366cb90b`.
- Proof handoff: 16,903 bytes, SHA-256 `2b1aaed7a6e510a16e265109a280e0068025e36f5f4cc3a5de4d1b2d15e562d2`.

## Verdict

**CHANGES_REQUESTED for source-evidence wording/provenance. Lean remains
CONSTRUCTED_BUT_UNCHECKED.** No kernel acceptance, axiom-audit success,
source/native inventory equality, parent closure, or production authority is
established.

## Findings to address in source handoff revision 2

1. The statement that `SourceNodeKey` distinguishes same-offset nodes is false.
   At pinned `full_parse.rs:409–432`, two distinct zero-width siblings share
   parse pointer, green pointer and start, and the test asserts their keys equal.
   Complete Rust `Eq` remains suitable for the table, but injectivity does not
   follow. This fixture uses a modified parse and is not a supported-source
   counterexample to the parent theorem. Preserve the accepted-source uniqueness
   question as OPEN.
2. Not all allocations become `EncodeError::Exhausted`: some output `Vec::push`
   paths lack `try_reserve`, and cloning symbol `Box<str>` allocates
   infallibly. Add fallible reservations/avoid duplicate allocation, or narrow
   the failure claim to explicit reservations and document allocator-abort
   limits. No partial authenticated snapshot return was found for the modeled
   explicit `Err` paths.
3. R139 contract and source handoff cite stale R138 outcome SHA
   `080b15b3…`; the committed R138 outcome now hashes to
   `2cfe94f5dd822c4df4619fa194186c2537393c1c3ed8340e244f56b6e93ac480`, which
   matches the R139 proof handoff.

## Supported parts and proof status

The reviewer verified all proposed Rust tags have `Clone`, `Eq`, and `Hash`
support, including manual hashes consistent with equality; `HashMap` collisions
do not merge unequal keys. `build_snapshot` uses one mutable table for source
and retained-native encoding; output loops preserve repeated-key order and
multiplicity. Explicit reservation/code-width errors propagate before snapshot
return. The private completion marker is only a convention, not an independent
authentication law. `lookup` is unused in the construction path.

Static inspection of all 19 Lean theorem bodies found no evident mathematical
counterexample, `sorry`, project axiom, unsafe evaluation or kernel bypass.
The standard-library index lemmas used have compatible pinned signatures.
However, the one permitted check and both version queries exited `-6` before
elaboration with `failed to create thread: Resource temporarily unavailable`
under one-CPU affinity and 1 GiB address-space cap. No type prints or axiom
outputs exist; they remain UNVERIFIED. Do not retry under R139's exhausted
one-check allowance.

Additional limits: Lean has seven abstract tags while Rust has eight including
`FormalPosition`; concrete instantiation remains open. Generic theorems require
`DecidableEq K`. `encode` is total on unregistered keys, using `idxOf`'s length
sentinel. Failure lemmas prove error-result nonpublication but do not validate
arbitrary successful snapshots. No theorem connects successful
`constructFrom` to `extend`/`encode`, Rust execution or R136/native inventory.
Source traversal order still needs a filter/order bridge to R136's native
permission traversal. Source/native equality, `SourceProblem.InferenceSoundness`,
effect hygiene H, A/B, consumers and production remain OPEN.

No builds, tests, Lean/checker commands, Git mutation/status/diff, delegation,
scratch or file writes were performed by the reviewer. Review fit within 240
seconds; CPU/RSS unmeasured. Reviewer STOPPED with no outstanding leases.
