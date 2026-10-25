# Sprint FULL-PAPER-TYPE-SUBSTITUTION-20261025/r17 — shared-context forall transport

Status: ADMITTED by Luna after R16.2 acceptance and fresh review. Baseline commit `ef70266396de7500abb61945d6c1c1d8c0493682` (`research/simple-sub-intrusion`). This is an isolated proof candidate. It grants no production, semantic-adoption, Rust, or main-checkout source rights.

## Parent goal and fixed outcome

Parent remains the original full-paper typing substitution theorem and the user's goal of Lean proofs for Yulang type inference/executor semantics. Preserve the manuscript's value-only universal-introduction rule and its freshness condition: `α ∉ fv(D, Γ)`, with `Γ` containing every captured/shared value. Do not change original quantifiers or exclude any represented declaration, graph, environment, value, computation, continuation, or type.

R16 prerequisite, now accepted after independent review: `tasks/agent-loop/inbox/paper-typing-subst-r16-adjudication.md`; proof source `PaperExecutionBinderLaws.lean` SHA-256 `568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a`.

R17 outcome: represent declaration table `D` and graph environment `Xi` as indices, alongside the existing `Γ` index, in all six mutual judgments: `ValuesTyped`, `ValuesAllTyped`, `RecordPayloadsTyped`, `PaperValueTyped`, `PaperComputationTyped`, and `PaperContinuationTyped`. Preserve every existing constructor and premise. Add the missing `PaperValueTyped.typeAbstraction` constructor for the actual `.typeAbstraction` syntax, with result `.poly bodyType` and body premise under all three contexts shifted together by `shiftTypeSubstitution`. This is the formal de Bruijn form of freshness over the shared declaration/graph/type environments; do not replace it with an unproved freshness assumption, a closed-context restriction, a newly selected witness, or a term-only shift.

Prove arbitrary simultaneous substitution transport for all six judgments, with the original `∀ σ` scope and all constructors. The type-abstraction case must map the body under `liftSub σ`; use the accepted R16 syntax, declaration-table, graph-environment and type-environment commutation lemmas to reconcile shifting with arbitrary substitution. Keep `PaperExecutionSyntax.lean` independent of `PaperExecutionBinderLaws.lean` to avoid an import cycle; the typing-substitution module may import the accepted BinderLaws module. No edit to BinderLaws or other dependency is leased.

## Success evidence and falsifiers

Success requires a focused successful build of the changed syntax and typing-substitution modules; exact printed theorem types for the six transports; complete axiom audits for those theorems and the new type-abstraction derivation path; and a concrete type-abstraction application showing that `D`, `Xi`, and a shared `Γ=[Ty.var 0]` are shifted together (the captured type becomes `Ty.var 1`, never silently generalized as new `Ty.var 0`). The accepted R16 dependency must rebuild from the changed syntax hash. No `sorryAx`, unapproved axiom, failed declaration dependency, `sorry`, or `admit` is accepted.

Falsifiers include lost or narrowed context indices, missing constructor or side premise, dropped shared environment, failure to preserve the existing type-application/nominal/operation instantiation cases, wrong binder index, a type abstraction generalized over captured `Γ`/`D`/`Xi`, changed syntax mapping under `liftSub σ`, or any admitted assumption standing in for freshness.

Even complete success closes only these six judgment transports and the forall-introduction premise. Full paper-rule coverage, recursive graph guards, executor/inference safety, original A/B, source/native/Rust correspondence and production remain OPEN.

## Exact authority, ownership and resources

Source map: manuscript `docs/yulang-operational-type-safety-ja.tex:203–207,237,953–977`, SHA-256 `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`; `PaperExecutionSyntax.lean`, SHA-256 `8789ee5a79b93d6fef2cff1db8692de67f4bc8b290a92ec3e37cac34b0074939`; `PaperExecutionTypingSubstitution.lean`, SHA-256 `30f13a5fbbb11cd5763347efebcc5300e9119884eb4494a41d97bdaeb0731241`; accepted `PaperExecutionBinderLaws.lean`, SHA-256 `568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a`; `PaperTypeSubstitution.lean`, SHA-256 `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861`; `PaperTypeFormation.lean`, SHA-256 `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`; `DeclSubst.lean`, SHA-256 `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`. No other code path is authorized.

Worktree: `/tmp/yulang-r17-forall`, detached from the frozen baseline. One registered `lean_prover` owns only that worktree's `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`, `PaperExecutionTypingSubstitution.lean`, `.lake/R17Audit.lean`, and `tasks/agent-loop/inbox/paper-typing-subst-r17.md`. Its source dependencies are otherwise read-only; its cache is worktree-local. Primary owns this contract, main `current.json`, final calls 11–12, final cache, review assignment, Git and integration. Never overlap with old UNKNOWN leases in the primary checkout. No implementation lane is admitted: `NO_SAFE_CODE_SLICE`.

Budget: maximum 1800 active seconds, 12 serial Lean/Lake calls, and 180 checker seconds. Calls 1–10 are construction, with calls 11–12 reserved for primary final focused build, exact types and complete axiom audits. One Lean/Lake process at a time, `-j1 -M1024`; no version-only or reconnaissance calls. Do not transfer R16's unused calls 9–10 to R17. After freeze, a fresh non-author independent reviewer may receive a separate bounded review packet.

Stop at the first mathematical contradiction in the paper rule, inability to derive the exact shared-context shift from existing mappings, import cycle that cannot be resolved within the exact two-file lease, unproved premise/decrease, changed dependency hash, budget/time ceiling, or any need for a narrower quantifier or extra assumption. Preserve full diagnostics and a versioned handoff. No source/dependency/hash edits outside this packet.
