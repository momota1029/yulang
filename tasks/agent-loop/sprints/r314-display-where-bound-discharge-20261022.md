# Sprint R314 — source-authenticated Display prerequisite discharge

Status: ACTIVE, solo primary; R149 remains OPEN.
Branch / base: `research/simple-sub-intrusion` / `60adf4b4d` plus the frozen, uncommitted R313 readback slice in this worktree.
Authority: user's persistent unchanged-Yulang2-samples goal; R149; unified design §§4.1–4.5, stage 4 and 10; proof companion §§3.1–3.2 and 7.1–7.4; R313 bounded readback.
Dispatch: serial primary work because the user prohibits subagents and no dispatcher callable is available. No independent proof or review receipt is claimed.

## Parent outcome

Continue the exact 142-byte `Types` sample. R313 reads its receiver as ordered `(Int, Str)` from the same saturated solver session that remains deferred, and matches the exact pinned local tuple `Display` target `('a, 'b)` with both exact `Display` prerequisite identities. The whole method inventory remains incomplete, and three local target shapes are unsupported.

Determine whether the two tuple prerequisites can be discharged source-directedly from the same receiver evidence: substitute `'a = int` and `'b = str`; identify the exact pinned `Display` implementations for those types and their own prerequisite sets; preserve every implementation/source identity and fail closed on ambiguity, unsupported syntax, or missing routes. Do not trial-type candidate bodies. Improve source-role candidate enumeration only when an exact route can be authenticated without treating spelling as identity.

Success evidence is a same-session readback linking each tuple `where` subject to the exact concrete element, then to a unique authenticated `Display` implementation with discharged prerequisites, or an exact obstruction that proves why the current source/solver route cannot establish it. Keep ordinary inference deferred unless global candidate completeness and later-constraint stability are both established. This sprint does not authorize changing Yulang2 lookup semantics or claiming method selection, runtime execution, R149 closure, source/native soundness, A/B, principality, termination, review, or production.

## Fixed inputs and falsifiers

- Types source: unchanged 142-byte template, SHA-256 `8cbfb97a8df8e5dc4916313769c39a84626ae124f91f8a9672f1ad8b866f98e6`.
- Pinned standard library: original R149 bundle and blobs; especially `lib/std/core/fmt.yu`, `lib/std/text/path.yu`, and `lib/std/time.yu` where the source census finds `Display` implementations.
- R313 readback code/test stays frozen while R314 consumers depend on it.
- Frozen R313 dependency hashes: `candidate_source.rs` `7696160622e4cdbe70c07a41d2d53e1d4054c0de5b8e64709b7060a3831c07d9`; solver `lib.rs` `e783110e699b15aefa38801e5324a962c8a14c378023761528effd87f6606ed2`; `shadow_apply.rs` `e6637642b0a2d6e0007db952bcc0b37236f8ab5de73751370ac9e42c79449ded`; playground `lib.rs` `77ce92655fab129d8627350da33f319171bc6dafea8bbc182023d5562a808eba`.
- Preserve ordered bounds, relation/source identity and the exact `where` order. A missing or unsupported candidate is not evidence of uniqueness. No selection based on declaration order, spelling, a partial inventory, or a candidate body that happens to type.
- A legal later bound that changes the applicable implementation refutes any proposed early-stability rule.

## Exact write leases

- `crates/yu-hir/src/shadow.rs`
- `crates/yu-solver/src/candidate_source.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `crates/yu-solver/src/lib.rs`
- `tools/inference-playground/src/lib.rs`
- `tasks/agent-loop/current.json`
- this contract and `notes/theory/2026-10-22-r314-display-where-bound-discharge.md`

Other paths and all pinned source bytes are read-only. No simultaneous writers or subagents. Solo cap: 1800 seconds, no carryover; at most one Cargo process and focused checks only until the source route is understood.

## Stop conditions and verification

If global candidate completeness depends on unowned or unsupported source syntax, keep `DeferredSelectionUnavailable`, record exact source owners and continue on an independent proof/readback step. Do not widen semantic authority to get a green test. Before ending the sprint, update the compact state and note, run focused relevant tests, `python3 tools/agent_sprint.py check`, and `git diff --check`; integrate a coherent checkpoint if Git metadata is writable. Never force-push.
