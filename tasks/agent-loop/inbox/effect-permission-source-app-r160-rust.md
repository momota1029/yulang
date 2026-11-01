# R160 Rust source/native handoff

Sprint/contract: `EFFECT-PERMISSION-ORIGINAL-APP-PA/20261102-R160`,
`tasks/agent-loop/sprints/effect-permission-original-app-pa-20261102-r160.md`,
SHA-256 `c2a81e706d633687bd8f1332f0d6bea8a7eb32a012a1bcbf4ed06094e218cc95`.
Baseline: `6b5e8f592c222c41df88bfe1cb99a0830fe7c760`.

## Outcome

**`NO_SAFE_CODE_SLICE` for constructing original App profile P or independent
admission A.** The clean Rust path below preserves structural source Apply
identity and builds native function/effect ports, but leaves original typing,
finite Checking evidence, descriptor formation, and source admission to
unresolved suppliers. Adding an observer or filling an input with a derived
answer would not construct the missing source law.

## Frozen owners and source path

The following baseline hashes were checked before this read-only mapping:

| Owner | SHA-256 | Relevant evidence |
|---|---|---|
| `crates/yu-hir/src/module.rs` | `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646` | ordinary Apply projection retains the exact two child indices, occurrence, source form, errors and range (`ResolvedExpr::Apply`, around line 3076). |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` | local Apply carrier stores separate callee and argument slots; empty call tail produces Unit. |
| `crates/yu-solver/src/candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` | candidate relation and `ApplySourceInput` retain both source operands, their value/effect endpoints, result/application effect, exact occurrence and checking/cause IDs. These IDs are provenance, not the two finite source Checking judgments. |
| `crates/yu-solver/src/shadow_apply.rs` | `99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5` | native negative Function demand connects argument value, argument effect and invocation effect to result. Callee-evaluation and invocation effects are separately added to application effect. A fresh invocation row is allocated before solving, but this does not prove distinct final rows or effect soundness. |
| `crates/yu-solver/src/candidate_call.rs` | `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f` | candidate observer exposes native fields and exact source operands; `PendingCallConstruction` explicitly leaves Gen-Call-0 and source typing/admission suppliers unresolved. Its comment states that scalar checking provenance or a negative Function is not original typing. |

This refines the independently reviewed R159 source/native route at
`tasks/agent-loop/inbox/effect-permission-source-app-r159-source-native.md`
(SHA-256
`eb23cb7433fb40fb5a6212325dfa552c256005bc6bbcdd0fc69caa796cbf6445`)
and source owner trace at
`tasks/agent-loop/inbox/effect-permission-source-app-r159-rust.md`
(SHA-256
`cd1c4d5b356313a88740fa81aebbd024fddbacd16b38c47cff1328ff05632ce8`).
Those already identify the absent original-law owner before candidate/native
planning; R160 did not find a downstream Rust constructor that supplies it.

## Parent application and limits

R159's Lean `app_admission_iff` remains the exact proof target. R160 Rust
confirms that the listed candidate/native nodes can receive operands and ports,
but no checked Rust owner here constructs P/A at the original binder or
connects them to the two finite Checking judgments. Thus neither the candidate
observer nor native effect join discharges R159's remaining source premise.

Effect hygiene evidence is structural: callee evaluation, invocation, argument
evaluation, and application effects occupy separately named endpoints and
ports with recorded polarities. This audit does not prove their solved rows are
distinct, that every source effect is retained, or that effects are sound.
Dirty/quarantined `candidate_receiver.rs`, `candidate_scheme.rs`, runtime files,
and untracked quarantined artifacts were not read.

No source edits, Cargo, Rust build, test, Lean build, scratch output, or new
environment/cache/worktree. This handoff is frozen for fresh independent
source/native review. Production promotion and source semantics remain OPEN.
