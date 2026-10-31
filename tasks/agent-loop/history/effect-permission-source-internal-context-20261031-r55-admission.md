# R55 admission — source/Internal context construction

Assignment: EFFECT-PERMISSION-SOURCE-INTERNAL-CONTEXT/20261031-R55
Contract: tasks/agent-loop/sprints/effect-permission-source-internal-context-20261031-r55.md
Contract SHA-256: 6583202e628a854dfeade9834788de76f2fad8422335383dd54884e9c35646bc
Branch: yulang3
Full base HEAD: bedcf5ecedc43b1d27b5cfa9bfc80845940fbff9
R54 accepted checkpoint: 7e3e48703469250d37ecf2119e7d96fcc0107433
R54 pushed-state receipt commit: bedcf5ecedc43b1d27b5cfa9bfc80845940fbff9

## Authority and reconciliation

This is a fixed-gate continuation of the user's existing Yulang inference/effects goal. The Luna primary admitted the exact R55 contract after R54's bounded independent PASS. No user language, semantics, source-domain, production or parent-claim authority changes.

Live roster at admission: /root/next_action_selector completed its R54-end consultation; R54 Rust and Lean authors and reviewer returned STOPPED; no R55 author or reviewer had started. Existing UNKNOWN worker rows, quarantined paths and all 32 pending question records are preserved. The already-recorded user capacity override remains idempotent at 13 slots; no path quarantine or UNKNOWN lease is released.

## Exact assignments and budgets

- /root/r52_rust, requested Luna/high, 1,800s: candidate_receiver.rs, candidate_effect.rs at the exact baselines in the contract, plus R55 Rust handoff.
- /root/r52_proof, registered Lean proof owner, 1,800s: SourceInternalContextR55.lean and R55 proof handoff.
- /root/r37_inventory_review, fresh independent read-only review, 1,200s after both authors STOP.
- Primary Luna: 1,200s including 500s closeout. Astra: 0. Total 6,000s.

## Exact source pins

All leased baselines match immediately before admission:

- candidate_receiver.rs cd914826f79cec065af2dbba7bb79d0ddc7681080e12a0e974738186118e769f.
- candidate_effect.rs 2a86befde95581decef8fe01698961062bd22388cff2459e9611570a20b9fba3. This is the existing dirty worktree baseline; it is retained exactly, not replaced by HEAD or a clean checkout.
- candidate_context.rs 8fa738f5050b642a9a52a55ffb2744cadeb95a0a0decefcc336663430deb4f89 (read-only).
- candidate_scheme.rs bf8f5c80ce2761dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631 (read-only).
- candidate_source.rs 96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a (read-only).
- candidate_call.rs fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f (read-only).
- local_source.rs 7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1.
- shadow.rs b964bab6dcdb7ebeca9f964c134ac8fb041c928c20ce0a895fea6b6af0fbb93e.
- source_annotation.rs 409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f.
- source_identity.rs 4bd5fa4066a1fd445a9757374c44d602decd1d791a394cd81c6066efa063fb23.

R39/R45/R47/R48/R49/R51/R52/R53/R54 Lean inputs match all exact hashes in the admitted contract.

## Lease and stop boundary

The exact leases are the two Rust source files and their handoff; one new Lean module and handoff; primary-owned review report, contract, admission, outcome and current.json. All other files are read-only. In particular, no HIR source, lib.rs, candidate_context.rs, candidate_scheme.rs, candidate_source.rs, constructor producer, runtime path, R54 artifact, question record, UNKNOWN/quarantined path or public API may be edited.

Both authors must first prove that required source constructors are recoverable from the retained R54 owner. If a full Catch/LocalSource or R39/R45 reader requires adding HIR retention or changing a source/experiment producer, that is outside this admission: stop before such a write and return the precise missing owner fields plus minimal required lease revision. Do not infer complete tables from selected-arm data or replace missing constructors with assumptions/defaults.

No builds, tests, Cargo, Lake project build, formatter, scratch/cache/target, environment/worktree/service, nested CLI or persistent process. Lean 4.35 stdin only; only git diff --check and python3 tools/agent_sprint.py check are permitted. Independent review starts only after both authors STOP. Luna retains sole Git integration.
