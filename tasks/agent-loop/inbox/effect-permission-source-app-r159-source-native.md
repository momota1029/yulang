# R159 Rust source/native Apply and effect trace

Sprint-ID / contract revision and SHA-256: `EFFECT-PERMISSION-SOURCE-APP/20261102-R159`, admitted contract; SHA-256 `ac7b61c03de0d1adae68452e9ae5df88e8500f890af96700719e828873abe7fc`.
Assignment-ID / handoff revision: `R159-SOURCE-NATIVE` / 1.
Parent gate / original theorem and scope: original App descriptor/profile formation and independent logical admission law, unchanged source domain and quantifiers; contract outcome is source/native path assessment only.
Baseline / direct dependency hashes: baseline supplied by contract `d3ed59fc63713e5cbe90332be5c9df74e730aa55` (not re-read through Git in this packet); reviewed R159 Rust owner map `cd1c4d5b356313a88740fa81aebbd024fddbacd16b38c47cff1328ff05632ce8`; prior R158 Rust map `8cfd25213a38b2f52b698fc4ff428f3942fd9e9a09cc0575c87b304a03b5a399`; R158 Lean handoff `2e5a6aa0e833a1013dbae786a6f654739b99c0c29f43709d26690c5b18b1f8a1`.
Role / actual worker ID / current session / launch or resume receipt: assigned `compiler_referee`; worker `/root/r159_source_native`; current session/runtime receipt unavailable.
Requested model and effort / observed model and effort: Sol / medium requested; observed model UNKNOWN, observed effort UNKNOWN.
Exact leased paths / authors and descendants: only this handoff path; author `/root/r159_source_native`; no descendants launched.
Outcome class: `source-native-evidence` and `NO_SAFE_CODE_SLICE`.

## Source -> candidate -> native trace

The inspected clean Rust chain retains actual syntax and candidate identity, then constructs a native-shaped constraint, but it does not supply the original App law.

1. `yu-hir/src/module.rs` ordinary preflight (`lower_ordinary_admission`, around 2871) recognizes a bounded syntax projection. `finalize_ordinary_admissions` (around 2977; Apply assembly around 3049–3076) reconstructs each Apply with its allocated occurrence, source form, exact callee and argument children, range, and descendant diagnostics. This is structural source admission, not typing.
2. `yu-hir/src/module/local_source.rs` ordinary formation stores `LocalSourceForm::Apply { callee, argument, source_form }` at exact operand indexes. The ordinary call-tail route uses the actual child when present and records `Unit` for an empty `CallTail`; associated-chain handling recovers only the fixed source tails tied back to the original chain. These constructors retain source occurrence and operands, not finite Checking judgments.
3. `yu-solver/src/candidate_source.rs::emit_candidate_source` visits that Apply. It reads `positions` for both operand indexes and retains `CandidateRelation::Apply` with callee value/effect, argument value/effect, result value and result-effect coordinates. It creates an `ApplySourceInput` whose checking occurrence is the same Apply occurrence with local slot 0 and whose cause is derived from that identity; recipe/source-input links preserve the registration. This is provenance and candidate coordinates, not the original source derivations or logical-admission premise.
4. `shadow_apply.rs::admit_candidate_fact` checks the source-input/recipe association, occurrence, candidate endpoint identities and effect/result coordinates. Under the scoped experiment it also invokes the scoped structural authenticator. The Apply branch builds positive callee and argument terms, a negative result, a positive argument-effect term, a fresh negative invocation-effect row at the application row's level, and a negative Function demand carrying argument, argument effect, invocation effect and result. It retains a `NativeInterface` with callee/argument evaluation effects, invocation row/effect and application effect (the Apply result-effect component). The native effect admission then admits callee-effect -> application-effect at slot 1 and invocation-effect -> application-effect at slot 2. Thus the two call effect coordinates remain separately named in the interface; this does not prove they have unequal row ordinals or source-semantic meanings. The argument evaluation effect is retained in the demand's Function argument port.
5. `candidate_call.rs::observe_inner` checks that the retained source is still `LocalSourceForm::Apply`, that both exact operand indexes match, and that Apply/checking/cause identities agree. It resolves both actual source operands and checks HIR ownership and scopes. It validates the native negative Function's argument, argument effect, invocation effect and result, and each native port's component kind and polarity; invocation row ordinal must match. Formal introduction is checked only when its conditional source route exists. This is a candidate structural observer; it does not manufacture operand typing or the original App admission law.

## Exact FreshUse / BoundKey observation and effect hygiene

`candidate_effect.rs` retains an operation signature view with `ViewOrigin::Operation`, including the source operation declaration and exact operation occurrence. In `shadow_apply.rs::source_operation_apply_effect_joins`, a requested observation is accepted only when all three occurrences are owned, the requested outer occurrence resolves to an Apply, and the exact `fresh_use` occurrence is inside that Apply's callee source tree.

The observer then follows a module route whose use occurrence and source owner match the requested FreshUse and Apply owner. It selects an effect bound with positive side and an operation Support operand at positive polarity; the other endpoint is a negative effect Row. It requires the retained complete key to equal `BoundKey(EffectRow(source_row), Positive, Support(source_view))`. The operation view must carry the requested occurrence. It reads the retained `effect_operands` FreshUse-map entry at that exact operation node, requires a copied Support view, then checks declaration pointer identity, owner, source position and occurrence across source and copied views. Finally it requires the route's mapped effect row to have negative effect polarity and the same row ordinal as the native invocation or application effect term. It emits separate `Invocation` and `Application` records, retaining the exact bound/relation indexes and both native terms. It does not join by family, canonical row equality, graph reachability or unordered endpoints.

This preserves polarity, operation identity, occurrence and complete BoundKey in the observed join. The observer is explicitly candidate structural evidence: it cannot establish source typing, permission, or whole-program effect soundness. The actual FreshUse-map construction owner is `candidate_scheme.rs`; that file is explicitly excluded by this packet, so the conclusion is limited to the map entry as consumed here, not an independent audit of its constructor. The consumer can return both tagged records if the mapped row ordinal happens to equal both native rows; it does not prove those rows are distinct.

## Parent application, missing owner law, and TODO

The original source/Checking App constructor remains the first missing owner, before candidate planning. It must connect the same original App binder and exact arbitrary operand derivations to lawful descriptor/profile formation and independent logical admission using every frozen Local premise, both finite Checking judgments, both annotation alternatives, selected interfaces, exact occurrence, payload/extension, and the conditional singleton-formal origin. It must also identify how those source judgments yield the native operand interfaces and complete admitted BoundKeys observed above. Neither the structural Apply constructor, candidate relation, negative Function demand, operation FreshUse observer nor row match supplies that implication. The earlier reviewed R159 owner map reached the same `NO_SAFE_CODE_SLICE` boundary; this trace fills its expressly uninspected FreshUse/effect-consumer edge without changing that disposition.

TODO request ID `R159-APP-SOURCE-CHECKING-OWNER-1` (request only; no write authority): original App/Gen-Call-0 source owner; provide the source constructor or an all-premises countermodel deciding descriptor/profile formation and independent admission at the same ViewLogic binder. Required inputs: original App statement and all frozen premises, both operands and finite Checking derivations, selected interfaces and conditional singleton-formal origin. Required output: source-grounded law plus a witness relating these exact source identities to candidate/native endpoints and complete keys, or a source-interpreted countermodel. Falsifier: a model satisfying every supplied original premise but violating the law; if such a model exists, no Rust admission slice is justified. The consumer mapping is downstream and remains conditional on this source-owner result.

## Evidence reused, scope, checks, and freeze

Reused: the reviewed R159 Rust owner map and its seven clean-owner hashes; R158 Rust correspondence map and its conditional FreshUse/Replay findings; R158 Lean handoff only as a frozen locator. The earlier R159 map's structural source/candidate/native chain remains valid at its stated hashes. Its explicit gap was the actual FreshUse-map construction/consumer; this handoff inspects the permitted `candidate_effect.rs` and `shadow_apply.rs` consumer only. I did not read the excluded `candidate_scheme.rs`, `candidate_receiver.rs`, quarantined runtime files or untracked artifacts.

Frozen clean input hashes:

| Path | SHA-256 |
|---|---|
| `crates/yu-hir/src/module.rs` | `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646` |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `crates/yu-solver/src/candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `crates/yu-solver/src/candidate_call.rs` | `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f` |
| `crates/yu-solver/src/shadow_apply.rs` | `99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5` |
| `crates/yu-solver/src/candidate_effect.rs` | `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15` |
| `crates/yu-core/src/shadow_call_formation.rs` | `394c763e5b4e2de6ae692ffacf22c07db8958f00129a47f1332f238c9a8eb5eb` |
| `crates/yu-core/src/shadow_derivation.rs` | `714fa4f53ee14f7a4d4e1d38ff0820157838de9c4b70a266bee1998eb2851dc2` |

No code edits, Cargo/build/test, Lean, Git, checker, formatter, new environment/target/cache, or runtime execution. No implementation or theorem is claimed, and there is no review or production promotion. Budget grant: 1500 active seconds; exact active seconds not instrumented, remaining amount UNKNOWN. No generated outputs or disposable scratch paths created. This handoff is the only new path.

Next related step inside the fixed sprint: original App source/Checking owner derives the law or exact all-premises countermodel; then map its witness into the retained source/native identities under a separately granted code lease. Until then, Rust outcome remains `NO_SAFE_CODE_SLICE`, source/native closure and parent theorem OPEN.

Worker state / writes-stopped receipt: STOPPED; this file is frozen at revision 1. I stopped writing after the final hash check; no descendants or other output leases exist.
