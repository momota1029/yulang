# R187 primary source readback — candidate evidence only

Owner: Luna primary. This is a provisional continuation of
`R187-OLDER-LOCAL-SAME-USE-1`, not a proof, counterexample certification, or
source/native closure. R187's original parent, A/B, source/native, and
production gates remain OPEN.

## Exact source and run

The readback used this HIR source construction:

```yu
act signal:
    our ping: () -> int
my finish (x:[signal] int) = x
my outer (t:[signal] int) = {
    my bridge (x:[signal] int) = outer x;
    my relay (u:[signal] int) = bridge u;
    catch t { signal::ping(), _ -> relay t, v -> finish t }
}
```

`parse_file` reported no structural recovery, HIR local-source lowering
succeeded, and `CandidateInference::solve` returned a candidate. This was a
read-only query through the existing candidate observation API, driven by the
temporary ignored probe `target/r187-probe/` (Cargo manifest SHA-256
`c3cb54d773fd60780138a15588adb47036dcbe3b6a5d00a55ffd4a3b895e7621`, driver
SHA-256 `cb3856ab0a99633bab365768cf6de63d2b3f08ce68521aee45d6ddd188e4f630`).
The observed `crates/yu-solver/src/shadow_apply.rs` worktree bytes had SHA-256
`7c52bbd421de84d57efa7aba13a391b26eb4098a77199895482f720017be2fca`; that
file is dirty and was excluded from R187's pinned baseline. Therefore these
are current-worktree candidate observations, not evidence about the pinned
baseline implementation.

Command:

```text
cargo run --offline --manifest-path target/r187-probe/Cargo.toml
```

The probe found four retained Apply calls: `outer x` at source level 2,
`bridge u` at level 2, `relay t` at level 1, and `finish t` at level 1. The
`bridge u` and `relay t` callees resolve to local bindings. The terminal
`finish t` call remains present as the finite Catch value-arm branch.

## Source relation to the two Replay inputs

The bridge Lambda's slot-2 source origin is relation 45, with a direct completed
source drain for `PositiveFunction(Term 291) <= ValueRow(7)`. The later local
`bridge u` Apply has complete occurrence facts/origins; its direct slot-0
origin is relation 58:

```text
ValueRow(13) <= NegativeFunction(Term 306)
```

The retained Replay has child relation 59, lower parent 55, and upper parent
58. Both ordered inputs are present in the retained dependency:

```text
lower_input = ValueRow(13) positive <= PositiveFunction(Term 296)
upper_input = ValueRow(13) negative <= NegativeFunction(Term 306)
```

The same Replay dependency was returned for FunctionPort ordinals 96 and 98.
This authenticates the bridge local call's source slot-0 relation as the Replay
upper parent in this candidate run.

The relay Lambda's slot-2 source origin is relation 74, with a direct completed
source drain for `PositiveFunction(Term 314) <= ValueRow(8)`. The actual later
`relay t` Apply has complete occurrence facts/origins; its direct slot-0
origin is relation 95:

```text
ValueRow(18) <= NegativeFunction(Term 338)
```

The retained Replay has child relation 96, lower parent 92, and upper parent
95. Its ordered inputs are:

```text
lower_input = ValueRow(18) positive <= PositiveFunction(Term 324)
upper_input = ValueRow(18) negative <= NegativeFunction(Term 338)
```

The same Replay dependency was returned for FunctionPort ordinals 154 and 156.
Thus the source-origin-to-Replay-upper-parent join and both retained Replay
inputs are present for the later relay call in this run. The observer does not
expose a separate Replay completion receipt; the successful candidate solve
does not certify the theorem's native correspondence.

## Local Capture and FreshUse readback

The complete bounded observation was not truncated. It returned 12 Capture/map
rows for local callee occurrence 14 (`bridge` use, route 0, context use 1) and
24 rows for occurrence 19 (`relay` use, route 1, context use 2).

For the later relay use, Capture graph root 0 has live root 8, boundary 1, 18
nodes, 9 rows, 8 captured bounds and 8 snapshots. `source_frontier`,
`owned_regions`, `negative_functions`, and `context_views` are empty. The
captured bounds are:

```text
ValueRow(8) positive <= PositiveFunction(Term 314)       relation 74
ValueRow(12) positive <= ValueRow(9)                      relation 60
EffectRow(31) positive <= EffectRow(28)                   relation 72
EffectRow(31) positive <= BottomPositive                  relation 73
EffectRow(23) negative <= EffectRow(12)                   relation 56
EffectRow(12) negative <= EffectRow(23)                   relation 57
EffectRow(12) negative <= EffectRow(29)                   relation 62
EffectRow(29) negative <= EffectRow(9)                    relation 53
```

The Capture snapshots retain the same eight source bounds and admission /
emission heads. Their coverage bitsets are 56 except relation 53's 120; those
bits are unresolved coverage gaps, not completeness proofs. The retained
FreshUse map records report empty scope, scoped-relation, effect-operand, and
bundle maps; context remapping is identity and evidence remapping contains
snapshots 11 through 18. The terms map has 18 entries, including Term 314 and
Term 324. Explicit formal annotations explain the absence of scoped demands in
this source construction; `scoped_replay_demand_transports()` returned no rows
for calls 1 and 2.

The bridge-use Capture graph has root 0, live root 7, boundary 1, 9 nodes, 5
rows, 2 bounds and 2 snapshots. Its two bounds are
`ValueRow(7) positive <= PositiveFunction(Term 291)` (relation 45) and
`EffectRow(22) negative <= EffectRow(9)` (relation 19).

## What this does and does not establish

This readback replaces the manually predicted relay Capture table with actual
candidate-run bounds and joins both relay Replay inputs to the source Apply's
slot-0 relation. It does not identify every numeric row with the mathematical
names `V_u`, `n_u`, `c_u`, `q_u`, and `r_u`, establish that no additional
authentic suffix reaches the return, or evaluate the proposed finite model
against every retained relation. The coverage gaps remain unresolved.

The higher-level `source_provider_observation` refuses these local calls:
its source consumer query requires a module-callee target and its route census
walks module routes. Separate `source_occurrence_observation` and
`ordinary_provider_observation` calls permit the joins above, but do not provide
one completeness-authenticated local source-to-Capture-to-Replay census. A
future exact source-path revision would need that local join and a Replay
completion receipt if those fields are required for closure. No compiler code
was added by this readback.
