# R233 outcome — endogenous cached constrain

Status: **REVIEWED MODEL-INCOMPLETE**. Baseline: `d47635c57d3c34099da999dc41f2475ce202be5a`. Contract SHA-256: `30873001ab25326e8d02b501c245eefab828021ee1a856cb23666bd085484891`.

## Outcome and parent application

The pinned paper relation accepts record width: `{0:A,1:B} <: {0:A}`. The frozen closed-tail pair in `AbstractCachedConstrainR233.lean` is rejected by every valuation in the existing `SimpleSubConstraintSyntax.Sub`. `recordDepth_mono` proves the structural invariant across all 16 Sub constructors, including transitivity, lattice constructors, and all four Function ports. `width_field_reflexive`, `width_not_sub`, and `width_rejected_by_every_valuation` establish the exact separation.

This result is deliberately narrow. An open right tail encoded with `.top` can express the same demand under existing `Sub`; R233 does not prove global inexpressibility, refute every possible embedding, or establish a Yulang typing counterexample. It shows that the selected closed-tail record denotation does not match the paper's width relation. Existing R229/R230 insertion/publication slices do not supply complete `constrain` or apply to a parent root.

Independent reviewer `/root/r233_width_obstruction_review` returned PASS for this exact frozen relation obstruction and MODEL-INCOMPLETE disposition. Review SHA-256: `5699f7fb0d4e4deb5abeabddacaf56d1526a1eabbf2aea8ba6a470742e499d0e`. No blocking, major, or minor defect was found within that claim. The reviewer explicitly identified the open-tail/top encoding as a limit on global claims.

**Original parent-premise delta: 0. Roots: 0/4. Packages: 0/5.** The four original roots, quantifiers, and source domain are unchanged. The missing bridge is the authority-derived record representation and the connection between its denotation and the actual upper-field lookup/comparison transition. The next model step must establish this equation from selected source authority before any new Lean bridge is activated. No Rust code slice was safe.

## Lean and resource evidence

Pinned checker command used Lean 4.35.0 and Lake 5.0.0 against the existing project/cache, checking the four declarations above with complete printed-type and axiom audits. Exit 0; each declaration's `#print axioms` reported no axioms. Exact module SHA-256: `3a0de10775554603d9c906bde1ec44c0d53d009044e354e69554e61c3ecff4f4`.

The existing `.lake` apparent size grew from `133,964,417` to `134,108,449` bytes (+`144,032` bytes). No new worktree, environment, target directory, or cache path was created; no cache cleanup, Cargo, default build, Rust edit, or tests were run. Proof source and review writes stopped; selector consultation returned and no descendants remain active.

`python3 tools/agent_sprint.py check`: PASS (static consistency only). This checkpoint records an incomplete research outcome and does not promote it to parent closure or production readiness.
