# Sprint R312 — stable FieldTail selection and same-use member graph

Status: RESULT, solo Luna primary; selection parent remains OPEN. Parent R149 remains OPEN.
Branch / baseline: `research/simple-sub-intrusion` / `3eb3b64eb`.
Authority: unchanged user goal; `notes/design/2026-10-20-r149-types-console.md`; unified design §§4.1–4.5, 6, 9 stages 2/4 and 10; proof companion §§3.2–3.8, 4.5, 7.2–7.4; R310/R311 receipts.
Dispatch: degraded serial continuation because the user explicitly prohibits subagents. No independent proof or review receipt is claimed.
Contract revision 2, primary-approved lease expansion: the pinned Display role declaration and its concrete implementations are in different modules, while the current role implementation resolver only inventories same-module implementations.

## Parent and measurable outcome

Keep the exact Yulang2 Types and Console examples, pinned library bytes and expected outputs. The immediate Types blocker is the authentic `pair.say` `FieldTail`, currently retained as a four-row obligation and ultimately rejected as `DeferredSelectionUnavailable`.

Build a source-authenticated route from the settled receiver bounds to exactly one applicable `Display.say` member schedule, then instantiate that member graph for this source occurrence with the existing FreshUse mapping. The receiver Value/effect and result Value/effect ports must all use the same FreshUse map; caller-specific receiver constraints must not flow back into the shared member template or sibling uses. Keep the operation deferred while the relevant receiver frontier can still change. Ambiguous, missing, duplicate, stale, or unstable candidates fail closed.

Success evidence for this sprint: a focused source-backed test shows (1) the unchanged Types module's exact `pair.say` obligation reaches the actual `Display.say` default/implementation candidates from authenticated role and implementation identities; (2) selection waits until the receiver frontier is stable and selects exactly one applicable source; (3) the selected Member graph is copied for that use and all four ports use one FreshUse mapping; and (4) a second use receives disjoint local rows. The unchanged sample must advance beyond its current `DeferredSelectionUnavailable` boundary or the exact next missing premise is recorded with source owner and falsifier.

This sprint does not claim the whole Types or Console sample executes, does not resolve imported `+` value ownership, and does not close source/native correspondence, A/B, principality, termination, independent review or production.

## Evidence and invariants

R310 already captures separate `MemberGraph`s keyed by exact `SourceMemberRootId`, with receiver, result and effect rows explicit; captured nested FieldTail records remain attached to that graph. `FreshUse` already records each FieldTail's four graph-row indices and transports them through one `rows` map. The unresolved part is the stable resolver and the consumer that makes the selected member graph live at the source use.

Use `SourceRoleMemberId`, exact implementation source identities, role/member metadata and original receiver bounds. A role spelling, member spelling, stable numeric solver level, provider body text, or candidate ordering cannot establish selection. Do not trial-type candidates. The receiver's complete admissible class and implementation-uniqueness premises must come from established source-owned bounds and authenticated implementation ownership. Keep all actual effect contributions; contravariant `[io]` denotes `[io,'e]`, so `[state]` by itself is not a violation.

Falsifiers: any candidate selected by spelling/order alone; selection changes after an unrelated later bound; unknown receiver evidence becomes success; an instance/member body is aliased across uses; any of the four ports is omitted or remapped under a different FreshUse; unresolved or duplicate implementation source is chosen arbitrarily; or the pinned sample bytes are changed.

## Exact leases and resources

Exact write leases: `crates/yu-solver/src/candidate_source.rs`, `crates/yu-solver/src/candidate_scheme.rs`, `crates/yu-solver/src/candidate_context.rs`, `crates/yu-solver/src/shadow_apply.rs`, `crates/yu-solver/src/lib.rs`, `crates/yu-hir/src/module.rs`, `crates/yu-hir/src/module/source_exports.rs`, `crates/yu-hir/src/module/source_role.rs`, `crates/yu-hir/src/module/source_impl.rs`, `crates/yu-hir/src/shadow.rs`, `tools/inference-playground/src/lib.rs`, this contract, `notes/theory/2026-10-22-r312-stable-fieldtail-selection.md`, and Luna-owned `tasks/agent-loop/current.json`. Other paths, pinned sources and expected outputs are read-only. Expand leases before touching an unlisted owner.

Solo cap 1800 seconds, no carryover; one Cargo process at a time; focused checks at most 120 seconds. No workers or reviewers under the user's no-subagent instruction. Results remain solo and unreviewed. Commit and non-forced push at coherent milestones; keep the tree clean.

## R312 result

The sprint added an authenticated cross-module role/member inventory, exact implementation-member schedule identities, solver input transport for source-owned targets, and a bounded simple-name/tuple structural view of implementation targets with plan memory accounting. HIR and solver focused checks passed. The unchanged Types example still ends at `DeferredSelectionUnavailable`; no receiver-bound applicability, where-obligation discharge, stability proof, FreshUse instantiation, sample success, independent review, or commit was achieved. Continue under a fresh resource envelope; do not treat this RESULT as closure of R149.

## Stop conditions and continuation

If no stable receiver frontier is observable without trial typing, preserve the pending obligation and establish the precise source-generation or solver-consumer owner gap. Do not change the accepted sample source, method semantics, effect rules, or proof quantifiers to make this packet pass. Parent R149 remains OPEN until unchanged samples and required proofs are complete.
