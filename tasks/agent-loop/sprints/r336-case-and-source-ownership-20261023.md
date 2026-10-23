# Sprint R336 — Original Button Case obligations and source ownership

Status: ACTIVE; direct-primary serial; revision 1. Branch `research/simple-sub-intrusion`. Frozen code baseline `17e57af2c4605d7084c7d76792b115674776bbe2`.
Selector: `/root/r333_selector` recommends ending post-refresh local-use investigation and advancing the original Button Case-obligation question alongside the independently evidenced Callback Hygiene import-scope owner.

## Original goal and fixed outcome

Continue the unchanged goal: make the same original Yulang2 playground samples work on the evaluation machine while preserving original sample bytes, expected outputs, accepted semantics, source/native correspondence and Simple-sub A/B quantifiers. Catalog, source/native, A/B, receiving, principality and production gates remain OPEN unless their own obligations close.

R335 is closed with `NO_SAFE_CODE_SLICE` for a source-driven local use after FieldTail refresh. Do not invent a new scheduling phase or revisit the helper-only activation path.

This sprint has two direct-primary work packets:

1. **Button proof packet.** On the unchanged original Button source, establish or refute the controlling invariant for its guarded deferred `show` obligation. Trace the actual Case occurrence, arm ordinal, `(tag, arity)`, scrutinee row, Variant payload endpoints and binder-to-receiver relation through source construction, Capture/FreshUse and member dispatch. Determine exactly what the original Case semantics lets a consumer conclude for each guard. Any inactive-arm discharge requires a nonempty closed actual tag frontier, exact source/native constructor and payload correspondence under the same FreshUse, and a recheck after all nested member constraints drain. Finite lower observations or a complete count alone do not prove an exhaustive runtime domain. Success is a constructive source-qualified argument, a source-valid counterexample, or a precise controlling missing premise and `NO_SAFE_CODE_SLICE` for Button discharge. Preserve the original source domain and all A/B quantifiers.

2. **Callback Hygiene source-import packet.** Authenticate the preserved Callback Hygiene source bytes and reproduce the current import-resolution outcome. The archived source has a `for i in 0..3` binder whose `h i` use lies in the loop body; the HIR `SourceImportScopes` scanner currently records binding parameters, lambda binders and Case binders. Determine whether the exact `ForStatement` causes `i` to be misclassified as a free import request. If confirmed, retain only positively parsed loop-binder facts over the actual loop body using existing import resolution. Keep malformed/recovered forms fail-closed, do not suppress a genuine free use outside the loop, and preserve all input bytes. Follow the unchanged source to the next real compiler boundary. An import-scope repair does not establish runtime success or close the Callback Hygiene semantic theorem.

## Frozen evidence and dependencies

Code baseline `17e57af2c4605d7084c7d76792b115674776bbe2`. Source hashes at sprint start:

- `crates/yu-hir/src/module.rs`: `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`
- `tools/inference-playground/src/lib.rs`: `45bf78af436efa50e02ca97ba3b639c11f7dd88272d87c47f2822643786653d4`
- `tools/inference-playground/oracle/callback-hygiene.yu`: `9f6b445a2dc87e86448cf6e8cdba45a7af3ef9e6a76eec430df41f90e49e8385`
- `tools/inference-playground/oracle/callback-hygiene-identity.yu`: `1152f84a824bf13fca4c2aa1e10a3d788c8049ad162fcf2be7eb7ebb9da9190f`
- `web/playground/examples/yulang2-button.yu`: `880059461e5c8868f605d5fe71c2ccd388485d8e12d09bb80d8c9edd196fcb7c`
- `crates/yu-hir/src/module/local_source.rs`: `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1`
- `crates/yu-hir/src/source_identity.rs`: `4bd5fa4066a1fd445a9757374c44d602decd1d791a394cd81c6066efa063fb23`
- `crates/yu-syntax/src/expression/for_decl.rs`: `fd50ab8b049addc3c366a0eda5519fd38bda31a2b518ba139d90ad24949714ec`
- `crates/yu-syntax/src/syntax_kind.rs`: `fc0cde7e3347b65d7641a589ee02cdc1da6b7fba3fed07cc7d378df20a7bb6a3`
- `crates/yu-solver/src/candidate_scheme.rs`: `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5`
- Button/guard locator: `notes/theory/2026-10-22-r330-console-role-frontier.md`, SHA-256 `b95706ba243801f344361caca73c3cb6e12a9dbf79bdfb81293d3d689f3f0931`
- Callback Hygiene source/semantic locator: `notes/theory/2026-10-15-playground-callback-hygiene-construction.md`, SHA-256 `58ea1150921254a92479c7c35a189a18121b64a842376b2034ceb6c00c145d66`
- R335 reviewed lifecycle result: `notes/theory/2026-10-23-r335-source-driven-local-use.md`; pre-review source-trace SHA-256 `37c234a8f2d3afbf4e3ceb19e26846ed112fb8b284fd4e6b2de0f51c52d4adec`.

Historical notes are locators, not proof of current behavior. The present `web/playground/src/main.ts` no longer contains the archived Callback Hygiene source; use the preserved oracle file above and record this distinction. Keep solver Case/dispatch, HIR LocalSource, syntax, runtime, standard-library and frontend source owners read-only initially. Any needed write outside the grants below requires a versioned exact lease update.

## Work lanes and falsifiers

- **Proof lane, direct primary:** inspect the original Button constructor/Case source, actual retained recipes and consumers. A falsifier is a source-valid guarded call whose condition or payload correspondence is lost, borrowed from another arm/use, or changed through dispatch; a proof gap is not itself a compiler counterexample. Return the result to the original source/native and A/B obligation without changing its quantifiers.
- **Implementation lane, direct primary:** only if ordinary import resolution on the preserved Callback Hygiene bytes confirms a false free-name request, make the smallest `SourceImportScopes` owner repair and add an authentic regression that checks both loop-bound and genuine out-of-scope names. Follow that unchanged program to the next actual compiler boundary. A failure to reproduce means no code slice for this packet.
- **Review seam:** freeze the Button proof and the complete HIR/playground source change with dependency hashes. A fresh isolated `compiler_referee` review is required before acceptance. Review must check source ownership, lexical interval boundaries, recovery behavior, unmodified original input, and the exact limits of the Button source/native claim.
- No semantic changes, new language constructs, changed catalog source, altered expected output, Button branch-discharge implementation without its proof, or production promotion.

## Exact leases and resources

Writable paths granted only to `/root`:

- `crates/yu-hir/src/module.rs`
- `tools/inference-playground/src/lib.rs`
- `notes/theory/2026-10-23-r336-case-and-source-ownership.md`
- `tasks/agent-loop/sprints/r336-case-and-source-ownership-20261023.md`
- `tasks/agent-loop/current.json`

Direct-primary serial work; no child, Astra or parallel writer. Fresh envelope: 3,600 active seconds, no R335 carryover; R335 charged 600 seconds and its unused 3,000 seconds are discarded. One heavy Cargo process maximum. If a source fix is confirmed, run focused HIR and playground source regressions serially; no catalog-wide or runtime claim without its own evidence. Stop at the fixed outcomes, a source-qualified obstruction, a bounded no-progress result, the cap, user STOP or session end. Preserve all UNKNOWN legacy worker reservations and quarantined paths.

## Integration and Git

The primary owns adjudication, exact-path staging, commit and push. Stage only the five granted paths plus any explicitly added exact path. Never stage pending question bundles, rewrite history, force-push, alter frozen main, or change the original samples. At closure, record measured/conservative charge, reviewer stop receipt and the next material trigger. The unchanged parent gates remain OPEN throughout this sprint.
