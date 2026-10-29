# R19 conditional Lean checkpoint receipt

Status: primary integration receipt; exact staging scope below. This is a
research-only formal-model checkpoint under the unchanged inference/executor
soundness goal. It does not authorize Rust/compiler changes or promote any
source, parent, or production gate.

## Claim and review boundary

The frozen R19 module models presence changes for the session and term-arena
journals separately. Its accepted theorem computes journal absence from the
restricted `CompletedCall` alphabet and applies the result to a projection of
an arbitrary R18 `TupleInput`. The reviewer accepted this as a conditional
presence-projection artifact with no correctness findings. The artifact does
not authenticate every actual SCC graph-plan member/provider action before the
selected call, nor identify an observed native `TupleInput` with the computed
projection. Actual native selected-call exclusion therefore remains OPEN. No
five-event bound, parent closure, or production conformance is claimed.

Review receipt: `/root/effect_permission_candidate_call_journal_r19_review`,
read-only verdict ACCEPT conditional; zero blocking, major, or minor findings.
Its required continuation is to authenticate the complete actual graph-plan
prefix, preserve both journal projections and the same arena, then establish
the native-input correspondence.

## Audit and source identity

The proof worker artifact and handoff are frozen at SHA-256
`7796394c7cc312f2a403d82fe938c31b7d3c2dc4092ad1c53ef6729496f4f83a` and
`bd09cd149957ac91f0c56905de0e7457e337e6f5cdb826816dc6b8972152c6b2`.
The primary ran the pinned Lean 4.35.0 audit over eight R19 roots and four
inherited R18 roots in a fresh project copy: exit 0, 19.40 seconds, maximum RSS
975,488 KiB. All twelve printed types and complete axiom reports were inspected.
The raw stdout SHA-256 is
`dcd66aad0832a4a582a00f2d9442e7235b2948d2108af7a5deede55b1bd46858`; stderr
was empty; the resource receipt SHA-256 is
`0b8aee233cf5f49daae67dcbae394f111ff458bf9ed548d0b0471defc385f351`. The
worker and primary audits consume the R19 contract's two-audit allowance.

The frozen 200-entry R19 input manifest authenticates 200/200 workspace inputs.
It records the workspace versions of `candidate_effect.rs` and
`candidate_scheme.rs`, whose hashes differ from HEAD:

| Source | Frozen workspace SHA-256 | HEAD SHA-256 |
| --- | --- | --- |
| `crates/yu-solver/src/candidate_effect.rs` | `1f64d4fec8f2abceb11a48a51f5b615aa2cf605c9586ba742f15f9024a6a2717` | `7c8e4fe5270fd45cecece80dfbbdff81aa8f294546687938bf89212325fc146b` |
| `crates/yu-solver/src/candidate_scheme.rs` | `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707` | `35c58dca3748595e273cd53bfba07da2be3fd340ec63c56f6a18adea5e514fb1` |

Those Rust changes are provisional trace instrumentation from earlier
incomplete work and are intentionally excluded. This checkpoint reproduces
the formal import graph only; it does not publish or authenticate that Rust
workspace snapshot. Keep the source/native correspondence gate OPEN.

## Warning disposition

The successful import-closure build log
`/tmp/yulang-effect-permission-candidate-call-journal-20261030-r19/construction-build-3.log`
has SHA-256 `83eb2462e0fe9e973326b623579186b5a90f5ff598e07196d2b78df47002a17b`
and reports 17 existing Lean warnings in the import cone. They are at
`FormalPermissionSourceOrigin.lean:172`, `FormalPermissionSourceInstance.lean:64,187,210`,
`FormalPermissionHelperFrames.lean:266`, `FormalPermissionConnectedCuts.lean:35,232`,
`FormalPermissionTermCallControl.lean:162,225,233`,
`FormalPermissionArenaEvents.lean:101,103,143`, and
`FormalPermissionEventBuffer.lean:38,51,67`. They comprise unused `simp`
arguments, deprecated `if_pos`/`if_true`, a proposition-valued `def`, a
constructor-like local name, and `simp` steps that already close the goal.
The R19 proof files and their imports remain frozen. Admit a separate bounded
warning-maintenance packet with versioned proof revisions and the necessary
audits before further proof development; do not suppress the linters or fold
that maintenance into this checkpoint.

## Exact paths for this checkpoint

The following frozen Lean files form the complete local import closure for
`FormalPermissionCandidateCallJournal`. Their bytes were reauthenticated before
staging. No Rust, configuration, policy, coordination, pending-question, cache,
or unrelated worktree path is in scope.

| Path | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/FormalPermissionArenaEvents.lean` | `02ef97716d882073ccb2e53c53bbf8046c80e82a517253898db5d1c02cd1b8b3` |
| `notes/theory/lean/YulangClosure/FormalPermissionAuthenticatedNativeDecode.lean` | `ea97baf7c98becef27df9e0c416d8d5fb00e9e1b5b63f37021b01598231936dc` |
| `notes/theory/lean/YulangClosure/FormalPermissionAuthenticatedSiteExport.lean` | `d6fc3e11f26350f6cf03d7afc248500778e3bf4a8ee816582630aa5f5feeeb84` |
| `notes/theory/lean/YulangClosure/FormalPermissionCandidateCallJournal.lean` | `7796394c7cc312f2a403d82fe938c31b7d3c2dc4092ad1c53ef6729496f4f83a` |
| `notes/theory/lean/YulangClosure/FormalPermissionConnectedCuts.lean` | `6427eed5f0c3b84f80a3a37c31797fc782960c725fb77f6bef46cebcc993b023` |
| `notes/theory/lean/YulangClosure/FormalPermissionEventBuffer.lean` | `1886b763ebd493721cd6cb7d03f32ff3c43555587a53ccf4e0ee3c351c450b57` |
| `notes/theory/lean/YulangClosure/FormalPermissionExportWitness.lean` | `7c01a80c8d8e868d9349a3d02ec2d465ca976edfb515e04b57161b5c9744a67f` |
| `notes/theory/lean/YulangClosure/FormalPermissionExportWitnessNative.lean` | `a5ccf179ef6e5396adb46c18ced108052cba4022119efd0daa0d026b4c368de1` |
| `notes/theory/lean/YulangClosure/FormalPermissionHelperFrames.lean` | `92531e0849a08a03a37bbb35315f01b831d31bdffb108712c5b0a4a7eaaa75dd` |
| `notes/theory/lean/YulangClosure/FormalPermissionSiteTraversal.lean` | `ac079ecc4c480adb4222723815b3f476469ed13b933c3994d090db0fae909207` |
| `notes/theory/lean/YulangClosure/FormalPermissionSourceAllocation.lean` | `795e63e850f73d75f18f721224d3e0723c187a57c7437ffe3ef08a4dbd80648a` |
| `notes/theory/lean/YulangClosure/FormalPermissionSourceInstance.lean` | `828eef57d8caaa538c8feb91ad023dc45eb41e421b4eb430532e383ee1c75e91` |
| `notes/theory/lean/YulangClosure/FormalPermissionStructuralBufferBound.lean` | `f9bfd9ea556128b27e850b5ca66934d46fd86d73a77bdfdbb3846142ad37abd7` |
| `notes/theory/lean/YulangClosure/FormalPermissionTermCallControl.lean` | `73bface0963c65eb76933ff8116594b161e78f1733b66e6be25cc174d1eb2dd7` |

This receipt is the only non-Lean path in scope; its digest is recorded in
`current.json` after freeze.

R12–R18 imports are retained as conditional models with their source/native,
parent, and production limits intact. The R19 source-authentication result is
the conditional model above, not a native exclusion.

## Git disposition

Before this checkpoint, branch `yulang3` and `origin/yulang3` both pointed to
`d33805eb589ac89925bacab57e362df093456fe0`. Stage only the fourteen Lean
paths above and this receipt; inspect the exact index and outbound range before
commit and push. Synchronize `current.json` and the durable R19 outcome after
the commit with the actual hash and remote result. Stop if any frozen hash,
branch tip, or upstream relationship changes.
