# FULL-PAPER-TYPE-SUBSTITUTION-20261025/r8 — frozen integration failure

Outcome: `FAILED_CHECK_PRIMARY_BOUNDARY` for the R8 integrated module. One
standalone value-typing transport candidate is checked in the R8 scratch file;
the full requested record/paper-typing substitution slice is NOT complete.
Baseline: `492f48e12cbccec3b4f5d5e10b9c6a334c6bcd51` on
`research/simple-sub-intrusion`. Contract SHA-256
`65834569d8bdf44215a2de7201e70de3e9542063d0b7c3c18d45245144627b14`.
R7 remains frozen `FAILED_CHECK` in
`tasks/agent-loop/inbox/paper-typing-subst-r7.md`.

## Checked standalone artifact

`notes/theory/lean/.lake/R8TransportProbe.lean` SHA-256
`71e31e9a94f55b735adddde3e10c3e14dd147f407ad4f2682e3ff29cae8e21ca` was
compiled successfully with Lean 4.35.0 via `lake env lean`. It contains a
standalone `PaperValueTyped.subst_explicit` theorem proved by applying
`PaperValueTyped.rec` with all five motives explicitly set to the σ-transformed
target relations. Its handlers use the eliminator's IHs. This covers all value
constructors, including record values, and recursively carries the Values,
RecordPayloads and Computation motives. It also checks
`mapPaperValue_record_eq` by lifting the concrete `List.attach_map_val` instance
through `Value.record`.

Complete printed axiom audits from that successful invocation:

- `mapPaperValue_record_eq`: `[propext, Quot.sound]`
- `PaperValueTyped.subst_explicit`: `[propext, Quot.sound]`

No `sorryAx`, `_f`, or project axiom appeared in these two scratch declarations.
This is a checked value-judgment slice, not a successful focused module build,
not five separately exported transport theorems, and not the original full
paper substitution theorem.

## Failed integration attempt

The R8 primary integration attempt copied the explicit value theorem into
`PaperExecutionTypingSubstitution.lean` and tried to add a standalone
computation theorem. The focused Lake build failed. `PaperExecutionSyntax`
built; the typing module did not:

1. Defining `PaperValueTyped.subst` caused unqualified `subst` references in
   its own motive arguments and lookup proofs to resolve to the new theorem
   instead of the type substitution function. The resulting diagnostics report
   `Ty` where a typing derivation was expected and a proof where `Ty → Ty` was
   expected. The scratch theorem avoids the collision with the name
   `PaperValueTyped.subst_explicit`.
2. The direct `induction` tactic does not support `PaperComputationTyped`, which
   belongs to the mutual inductive family. Computation transport also needs an
   explicit recursor proof, with motive names that do not shadow the type
   substitution function.

The exact failed integration source was preserved as
`notes/theory/lean/.lake/R8FailedModule.lean`, SHA-256
`739172d53849c5a99a078d37ba11938b60db2b26a5f341cbe8a0ac58da1ffb71`.
The leased main typing file was returned byte-for-byte to its R8 input hash
`647146f77ba98b997c16cc08cc735ec2e1eaaf72e0b56e262b54e25604c3529d`; no
failed declaration was retained as a deliverable. The syntax input remains
read-only at hash `8ad8bc4b1549eadaa73c743438b333c62b44be7bdff0346f690b7da9e6353a97`.

## Accounting and continuation

R8 consumed 8/8 serial Lean/Lake invocations, approximately 14.6 checker
seconds, under its 120 checker-second and 900 active-second limits. Two early
probe failures (unavailable `aesop`; omitted sibling motives) were preserved in
that count and are not results. The last focused module build failed as above.
No test, Rust/native build, compiler change, independent review, or source/native
record bridge is claimed. All eight historical/foreign UNKNOWN reservations
remain quarantined; no reviewer slot is established.

At the boundary, use the standalone checked recursor proof as the base for the
next integration step: give the exported theorem a non-conflicting name for the
type substitution function, and prove computation transport through the same
explicit five-motive eliminator rather than ordinary mutual `induction`. Preserve
the original arbitrary σ claim, the record rule distinctions, and every
omitted-paper/source/native obligation.
