# Sprint R311 — pinned generic `say` LocalSource formation

Status: OPEN_CONTINUATION, solo Luna primary. The source-carrier outcome is met; parent R149 remains OPEN.
Branch / baseline: `research/simple-sub-intrusion` / `51f18e9b9`.
Authority: unchanged user goal; `notes/design/2026-10-20-r149-types-console.md`; unified design §§4.1–4.5, 9 stage 2 and stage 4, 10; proof companion §§2.14–2.16, 7.2–7.5; R310 full-test receipt.
Contract revision 3, primary-approved exact lease expansion after discovering that the retained `InfixOperator` constructor is consumed exhaustively by candidate collection and runtime lowering. Solo primary, no subagents per user instruction.

## Original outcome and measurable result

Keep the exact Yulang2 Types and Console samples, original pinned stdlib bytes and public/runtime outputs. The current ordinary `yu-playground --lib` suite has a reproducible failure in `pinned_public_export_route_retains_source_owned_edges_and_names`: the exact pinned `std::io::console::say` binding resolves, but `HirModule::local_source` returns `None` because the source carrier outcome is `UnsupportedForm`.

Required source is the exact pinned declaration `pub say(value: 'a): () =` with `where 'a: Display` and body `out::write: value.show + "\n"`. Success evidence: the ordinary provider lowering retains a Supported LocalSource for the authentic say binding; the carrier preserves the exact where-clause source, subject `'a`, role `Display`, body occurrence and original source keys; existing public-export assertions pass. Then rerun the full playground library tests and unchanged Types/Console boundary tests.

This sprint closes only the source-carrier formation obstruction. It does not claim method inference, Call typing, sample execution, source/native adequacy, A/B, principality, termination, independent review or production closure.

Outcome evidence: the ordinary pinned say carrier is Supported with its exact generic formal, result annotation, where-clause owners, operand occurrences, parse-owned operator-use key and imported HIR declaration receipt. `cargo test -p yu-playground --lib` passes 40/40 and `cargo test -p yu-hir --lib` passes 161/161. Candidate collection and runtime still refuse the InfixOperator constructor pending an authenticated operator-use-to-value-owner bridge.

## Proof and implementation route

Trace the ordinary `lower_module` counter path into `form_ordinary`, the exact binding plan/header, formal parameter source projection, where-clause parsing and RHS `OperatorChain` traversal. The decisive source node is the exact `InfixOperatorUse` between `value.show` and the newline string. Retain the parser-associated `HirOperator` and imported declaration receipt with the parse-owned operator node. Update candidate collection to recognize the new carrier constructor and keep it explicitly unsupported there until an authenticated source-value consumer exists; do not select a provider from spelling alone.

Falsifiers: the carrier points at a different declaration, body or where node; source key is reconstructed from spelling/range without parse ownership; unsupported/recovered input becomes Supported; test passes only after changing pinned bytes; or source formation claims the declaration is typed when it is only retained.

## Exact permissions and resources

Exact write leases: `crates/yu-hir/src/module.rs`, `crates/yu-hir/src/module/local_source.rs`, `crates/yu-solver/src/candidate_source.rs`, `tools/inference-playground/src/lib.rs`, `tools/inference-playground/src/runtime/program.rs`, this contract, `notes/theory/2026-10-22-r311-pinned-say-local-source.md`, and Luna-owned `tasks/agent-loop/current.json`. Pinned stdlib bundle and all other files are read-only. If the failing syntax owner is outside these paths, stop at that seam and issue a new exact authority boundary.

Solo active cap 1200 seconds, no carryover; one Cargo process at a time; focused checks at most 120 seconds. No workers/reviewers under the user's no-subagent instruction. All results remain solo and unreviewed. Checkpoint and non-forced push coherent outcomes; keep worktree clean.

## Parent continuation

R310 is preserved as `OPEN_CONTINUATION`: member graphs now retain exact receiver/result/effect rows and nested FieldTail before the session fails closed with `DeferredSelectionUnavailable`. Its next step is a use-local FreshUse consumer behind authentic stable method selection. R311 addresses the separately observed pinned `say` carrier gap first because it prevents the actual Console provider body from entering LocalSource at all. Both sample gates remain OPEN.
