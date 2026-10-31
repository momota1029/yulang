# R87 amendment 02 — diagnostic-directed proof repair

Date: 2026-10-31
Authority: Luna, within the fixed R87 outcome and existing two-call cap.

## Preserved outcome and boundary

R87 remains `NATIVE-DRAIN-READER-CORRESPONDENCE/20261031-R87`. The original reader definitions, source predicates, theorem statements, quantifiers, branch acceptance/rejection behavior, R57/R84 claims, exact inputs, and production boundary remain unchanged. Slot 1 is a failed call and remains preserved; this amendment authorizes at most one diagnostic-directed proof-body repair and slot 2 only. No budget reset, third call, Rust/source change, new dependency, or semantic change is authorized.

## Slot 1 independent audit

The fresh reviewer independently reconstructed the exact 150,997-byte stdin (`e277bb3673cde7f44ee4bc4aa9e1145de2c6e15187a72d34091a1878e0862358`), verified the frozen candidate/handoff, authorization and executable, and rehashed stdout/stderr in raw receipt `tasks/agent-loop/history/native-drain-reader-correspondence-20261031-r87-raw-result.json` (`31c8a9d4d86468975d3680e60d83fd4ff508c50949ff25830923f17a5c38f8aa`). Exit 1, no timeout; 10.305 seconds; peak RSS 954,112 KiB. Stdout: 159,444 bytes, SHA-256 `45fb8854635d6861106643df46724a04e2105cda217dc72d719bed6bcf75bd33`; stderr empty.

All 35 R87, 13 R84 and 11 R85 type/axiom pairs were present exactly once. Four unsolved goals contaminate five declarations: `publicationData_iff` (candidate line 155; error 2502), `uncut_sound_complete` (inherits the contaminated result), `cuts_sound_complete` (line 305; error 2651), `internal_sound_complete` (line 378; error 2722), and `saved_sound_complete` (line 424; error 2768). The other 30 R87 reports are clean: six with no axioms, 23 with `propext`, and `checkedCandidates_ok_iff` with `propext, Quot.sound`. R84/R85 reports remain clean. The four residuals are proof normalization failures: three retain generic `Bind.bind` where the pinned library needs `Option.bind_eq_bind` normalization; the positive cut branch retains `if True` because the restricted simplification omitted conditional reduction. The independent reviewer found no statement/source mismatch or counterexample and judged a proof-body-only repair plausible. Verdict: BLOCK slot-1 theorem acceptance; repair plausibly admissible for the final slot.

## Exact repair lease and gate

The proof owner may edit only:
- `notes/theory/lean/YulangClosure/NativeDrainReaderCorrespondenceR87.lean`
- `tasks/agent-loop/inbox/effect-permission-native-drain-reader-r87-proof.md`

Repair only the diagnosed normalization steps. Preserve all definitions and theorem statements byte-for-byte. Do not alter relation/source semantics, strengthen premises, weaken conclusions, add dependencies, or import failed R86 declarations. Record changed proof locations and hashes in the handoff. Stop and return to Luna if the diagnostics require any change outside proof bodies.

After the repair freezes, a fresh independent reviewer must inspect the exact diff and reconstruct the full slot-2 stdin before execution. Primary will separately commit and push the exact slot-2 authorization. Slot 2 remains subject to the original executable, `-j1 -M1024 --stdin`, `LEAN_NUM_THREADS=1`, 120-second call cap, exact in-memory transport, and no build/cache/scratch/worktree/environment creation. Complete type and axiom audit is required after execution. Any unsolved goal, `sorryAx`, hash drift or source mismatch closes R87 as failed with 2/2 calls consumed.
