# Sprint R314 — source-authenticated Display prerequisite discharge

Status: ACTIVE, solo primary; R149 remains OPEN.
Contract revision 4. Branch / base: `research/simple-sub-intrusion` / committed and pushed R313/R314 checkpoint `e91fdb417`.
Authority: user's persistent unchanged-Yulang2-samples goal; R149; unified design §§4.1–4.5, stage 4 and 10; proof companion §§3.1–3.2 and 7.1–7.4; R313 bounded readback.
Dispatch: serial primary work because the user prohibits subagents and no dispatcher callable is available. No independent proof or review receipt is claimed.

## Parent outcome

Continue the exact 142-byte `Types` sample. R313 reads its receiver as ordered `(Int, Str)` from the same saturated solver session that remains deferred, and matches the exact pinned local tuple `Display` target `('a, 'b)` with both exact `Display` prerequisite identities. The whole method inventory remains incomplete, and three local target shapes are unsupported.

Determine whether the two tuple prerequisites can be discharged source-directedly from the same receiver evidence: substitute `'a = int` and `'b = str`; identify the exact pinned `Display` implementations for those types and their own prerequisite sets; preserve every implementation/source identity and fail closed on ambiguity, unsupported syntax, or missing routes. Do not trial-type candidate bodies. Improve source-role candidate enumeration only when an exact route can be authenticated without treating spelling as identity.

Success evidence is a same-session readback linking each tuple `where` subject to the exact concrete element, then to a unique authenticated `Display` implementation with discharged prerequisites, or an exact obstruction that proves why the current source/solver route cannot establish it. Keep ordinary inference deferred unless global candidate completeness and later-constraint stability are both established. This sprint does not authorize changing Yulang2 lookup semantics or claiming method selection, runtime execution, R149 closure, source/native soundness, A/B, principality, termination, review, or production.

Revision 4 retains that outcome and adds the exact selected-member source projection/readback path. The pinned Types session currently has no captured member graphs because the provider projection contains only imported binding roots; selected member-only HIR exists, but candidate admission still returns `Unsupported`. Keep this obstruction explicit while isolating the member-only HIR consumer.

## Fixed inputs and falsifiers

- Types source: unchanged 142-byte template, SHA-256 `8cbfb97a8df8e5dc4916313769c39a84626ae124f91f8a9672f1ad8b866f98e6`.
- Pinned standard library: original R149 bundle and blobs; especially `lib/std/core/fmt.yu`, `lib/std/text/path.yu`, and `lib/std/time.yu` where the source census finds `Display` implementations.
- R313's pinned receiver observation remains the frozen baseline. R314 adds a separate captured-member FreshUse layout readback and leaves the original deferred selection gate intact.
- Initial R313 dependency hashes (before the additive R314 readback extension): `candidate_source.rs` `7696160622e4cdbe70c07a41d2d53e1d4054c0de5b8e64709b7060a3831c07d9`; solver `lib.rs` `e783110e699b15aefa38801e5324a962c8a14c378023761528effd87f6606ed2`; `shadow_apply.rs` `e6637642b0a2d6e0007db952bcc0b37236f8ab5de73751370ac9e42c79449ded`; playground `lib.rs` `77ce92655fab129d8627350da33f319171bc6dafea8bbc182023d5562a808eba`.
- Current revision 4 dependency hashes: HIR `module.rs` `85ed21b065f6e608ee5ba3e5d0ae6f4a1915d699cb13493df02d9e4dc1dbe72e`, `shadow.rs` `ccecca0d8967eabb87cf388e0b2efe4c2bae4c5ff341050a41dd59991decf18d`; solver `candidate_scheme.rs` `d057af438b2245be9ceae3027d48773ff6edfa1164612e9299f031c14a95a1f3`, `candidate_source.rs` `1127ade5b0c36758b262e27a3a4e8e060b5dacbd05162f240c1b0b21801972a8`, `lib.rs` `f34795ab6fd486355e41b987b1ef92887255f1b4814a29d9236704415598ea52`, `shadow_apply.rs` `64885d9e38d2736fb605015d1a811fb4a72825e0dc1f9dac78dc80bde29ed4c8`; playground `lib.rs` `e91fc47672fd973d587ff18e97a3ba7b199c80a3bb2c0efa03ef1664252d1d5c`.
- Preserve ordered bounds, relation/source identity and the exact `where` order. A missing or unsupported candidate is not evidence of uniqueness. No selection based on declaration order, spelling, a partial inventory, or a candidate body that happens to type.
- A legal later bound that changes the applicable implementation refutes any proposed early-stability rule.

## Exact write leases

Revision 2 adds `crates/yu-solver/src/candidate_scheme.rs` for the same-session
readback of captured Member FieldTail rows through their retained FreshUse maps.
This is needed because `GraphState::member_graphs`, graph-local obligation
ownership, and `prepare_candidate_fresh_use` are implemented there. The added
lease does not authorize changing candidate selection or method semantics.

Revision 3 adds `crates/yu-hir/src/module.rs` and `crates/yu-hir/src/shadow.rs`
to form only the exact implementation-member source carriers authenticated by
the pinned role index. The current binding-only provider projection yields no
member graphs, while projecting all of `fmt` fails on unrelated unsupported
bodies. This lease is limited to exact member-source projection and identity
validation; it does not change language lookup or authorize member selection.

- `crates/yu-hir/src/shadow.rs`
- `crates/yu-hir/src/module.rs`
- `crates/yu-solver/src/candidate_source.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `crates/yu-solver/src/lib.rs`
- `crates/yu-solver/src/candidate_scheme.rs`
- `tools/inference-playground/src/lib.rs`
- `tasks/agent-loop/current.json`
- this contract and `notes/theory/2026-10-22-r314-display-where-bound-discharge.md`

Other paths and all pinned source bytes are read-only. No simultaneous writers or subagents. Solo cap: 1800 seconds, no carryover; at most one Cargo process and focused checks only until the source route is understood.

## Stop conditions and verification

If global candidate completeness depends on unowned or unsupported source syntax, keep `DeferredSelectionUnavailable`, record exact source owners and continue on an independent proof/readback step. Do not widen semantic authority to get a green test. Before ending the sprint, update the compact state and note, run focused relevant tests, `python3 tools/agent_sprint.py check`, and `git diff --check`; integrate a coherent checkpoint if Git metadata is writable. Never force-push.
