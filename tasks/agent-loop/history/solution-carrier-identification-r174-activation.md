# R174 activation receipt

Sprint `SOLUTION-CARRIER-IDENTIFICATION/20261102-R174`; branch `yulang3`,
baseline `bb9b5826a`. The unchanged goal is Yulang type/effect inference
soundness against the original typing rules; runtime is out of scope.

The R173 proof/source outputs were independently reviewed PASS for the bounded
`BLOCKED_ORIGINAL_INTERPRETATION` result and pushed in `bb9b5826a`. The first
missing input is a same-solution, pre-invocation construction of the original
`FormalAssignment`: a Value descriptor from `native_root`, or a Computation
complete interface from `native_root` plus `entry_effect`. The R173 selector
returned `BLOCKED_INPUT` for another Lambda proof until the actual solution
carrier and its original descriptor/interface interpretation are known. It
recommended `SOLUTION-TO-ORIGINAL-REGISTRATION` as the next outcome.

R174 therefore admits one read-only source lane to locate the actual Rust
solve result, retained constraint/solution state, exported inferred values and
their original-source interpretation. No proof lane is launched until the
carrier is identified; this avoids assigning another theorem with an assumed
bridge. Contract dependency hashes are pinned in the sprint file. No unknown
lease or quarantined path is released; the existing 16-slot user-authorized
capacity record remains unchanged.

## Roster and acknowledgement

At R174 start the live roster was synchronized: Luna and the R174 source
researcher were active; the R173 proof/source/reviewer and selector had
completed. No other RUNNING/WAITING child was coordinating this state. Existing
UNKNOWN assignments and their quarantined leases remain unchanged. No new
capacity override or path release occurred.

`/root/solution_carrier_identification_r174_source` acknowledged the exact
contract SHA before any writes. Requested role: `researcher`; requested and
observed model/effort: UNKNOWN in runtime metadata. Its only write lease is the
single R174 source handoff; all Rust sources are read-only. Budget: 600 seconds;
no descendants or execution/build/test/Lean/Git/cache/scratch/runtime work.

## Contract revision 2

The source researcher requested the governing instruction paths before reading
them. Luna read and hash-pinned them in contract revision 2 as inherited
governance-only inputs, separate from the frozen representation and Lean
semantic dependencies. No source dependency, lease, execution permission, or
semantic claim changed. Updated contract SHA-256: `0348e550270015243dec340da3ac8e5e55aaa599e5102599d2367519362224b7`.

## Contract revision 3

The source lane located two additional candidate-result representation owners
outside the prior frozen set. Luna pinned their exact hashes before authorizing
further reads: `crates/yu-solver/src/candidate_scheme.rs` and
`crates/yu-solver/src/shadow_f5.rs`. Both are read-only inputs; this expands no
write lease or execution authority. Updated contract SHA-256: `d58b4a30e78bb409c5b4df0c29396f4f7d4458cbbd5090afa789b91be2848d39`.
