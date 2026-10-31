# R95 bounded outcome — exact-input execution failed

Sprint: `EFFECT-PERMISSION-LOGICAL-OCCURRENCES/20261101-R95`.
Contract SHA-256: `787d97362f3ca2d7a6a8e742009408513b0ca73a729228ec430db334727e7a1f`.
Manifest SHA-256: `0cc19b0cc76cd5b9a456d62bb3a7d48d656698afefd22c1bc3eccfbd4ed4142c`.
Corrected stdin: 106,897 bytes, SHA-256
`8bd62910afba8530f2140bd5b150db0d5fb5281c4651b87a88f78c51dc53d0d7`.

## Execution and independent review

The independent exact-input review passed: all 15 pinned inputs matched and all
ten distinct theorem names had exactly one adjacent `#check` / `#print axioms`
pair. Its frozen receipt is
`tasks/agent-loop/inbox/effect-permission-logical-occurrences-r95-input-review.md`,
SHA-256 `9b694c2c29ab4c3b88cfd456862ce101f5249d72cfa5cbee83d477ae1aa890a0`.

Primary execution was authorized in pushed commit `64200c8997e55938670c9dccaac1351f0e4e558e`; the pushed state receipt is
`abc8309c9bc01f6e1382d934b5116374c3f3ad95`. The exact pinned Lean 4.35.0
binary ran once with `--stdin -j1 -M1024`. It exited **1** after 12.576 seconds,
using 928,752 KiB peak child RSS. No timeout, stderr output, or retry occurred.
Complete stdout, exact command, timestamps, input digest and executable hash
are preserved in
`tasks/agent-loop/inbox/effect-permission-logical-occurrences-r95-verification.md`,
SHA-256 `6a2aca0dfac25074b7b05e0a70a6fa2eedbd877ed92644df0349be6b64d76e45`.

The fresh result reviewer returned **FAIL / BLOCKING**. Its receipt is
`tasks/agent-loop/inbox/effect-permission-logical-occurrences-r95-result-review.md`,
SHA-256 `f0676825d9bea19204ed4900f160a661aef5db8484aee421d7d14349bea95cb6`.
Review ran 81 seconds of the 120-second allocation. The reviewer confirmed two
clean local declarations and eight declarations that depend on `sorryAx`:

- `inventory_iff_lookup`: `propext, Quot.sound` — clean local declaration.
- `encode_lookup`: `propext, sorryAx` — induction hypothesis fails to unify in
  13 tree/forest branches; downstream membership and uniqueness inherit it.
- `observe_eq_follow`: `propext` — clean local declaration.
- `source_membership_iff`, `full_route_unique`, `app_inventory`,
  `lambda_body_inventory`: each transitively includes `sorryAx`.
- `source_provenance`: direct witness transport/elaboration failure and
  contaminated dependencies.
- `app_exact`: unresolved dotted `AtomKind` identifiers and failed `rfl` in
  both annotation cases.
- `lambda_body_exact`: unsolved goals for both formal entry modes and both
  annotation alternatives.

The reviewer confirmed all ten printed types retain their intended stated
quantifiers, but printed types after failed elaboration are not proof evidence.
No source-semantic counterexample follows from these errors. The candidate is
**not kernel-accepted**; its complete provenance result remains unchecked.

## Closeout and next gate

R95 closes as `CLOSED_BOUNDED_ELABORATION_FAILED`. The authorized call was used;
no repair or second call is permitted in this packet. The R93 candidate remains
frozen at its original hash. A repair needs a new bounded packet, preserving the
stated App/Lambda equations, all source constructors, both entry modes, both
annotation branches and the original parent quantifiers, followed by fresh
review and a newly authorized check.

R94's malformed digest remains a historical blocker, closed with zero calls.
Original A/B, semantic admission/readout, source/native correspondence, full
effect hygiene, principality, termination and production remain OPEN. No Rust
or compiler behavior change is authorized by R95.
