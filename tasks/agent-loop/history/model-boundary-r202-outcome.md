# R202 outcome — static model boundary audit

Status: **MODEL BOUNDARY CLARIFIED; original roots OPEN**

## Authenticated inputs and scope

The final contract is `tasks/agent-loop/sprints/model-boundary-r202.md`, SHA-256 `4ec339119cc66db8b9f7a6c3db7ce52d113bbd4b7f5d52728c94ab8556a6ed88`. The read-only architect authenticated all five pinned inputs against current files after the contract correction: top-level inference principles `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`; selected Source-Generalize definition `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`; selected Source-Generalize construction `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`; `Contracts.lean` `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`; and R201 outcome `7f0e93f174a26b6470cf39a283f5d9a7eb8548040fb5e0db0fb157844755bddd`.

R202 performed no Rust reads, Lean/build/test runs, environment/cache/target/worktree/scratch creation, or quarantined/pending-question reads. The existing roots and full source domain were not changed.

## Result

The unchanged `Contracts.lean` parent does not require Rust runtime `Inputs` to define source typing. The selected Source-Generalize construction already supplies an independent declarative source judgment, separate from solver success and generated constraints. This confirms the user's proposed proof direction: establish Yulang's static type/effect metatheory at that declarative boundary, then prove the Rust/native correspondence as a separate bridge.

A suitable candidate presentation is `Σ ; Γ ; Ξ ⊢ s @ h : I ▷ C [ω]`: `Σ` fixes independently specified declaration, checking, Call and effect rules; `Γ` retains resolved lexical bindings, annotations and roots; `Ξ` retains the original dependent binder tree and event/future obligations; `I` retains Value/Computation entry and full interfaces; `C` retains local obligations at original scopes; and `ω` is one strategy shared across the whole tree. A type/effect projection `τ ! ε` may summarize this judgment, but cannot replace its scoped obligations or witness.

The decisive rule constraints are:

- **Literal:** retain the authentic complete declaration rule for the raw literal and its original Return/effect/local evidence. A fixed base-type table does not imply that complete rule.
- **Branch join:** derive both branches under the same enclosing witness and join both types and effects. The approved `if true {1} else {"str"}` example yields `int | str`; constant `true` does not erase the string branch from static inference. Runtime evidence remains guarded by actual branch selection.
- **Lambda:** retain both Value and Computation entry modes, annotation identity, captures, body checking and invocation-return relation. Preserve all four Function ports and variances; a formal function-use constraint alone does not discharge contextual checking.
- **App:** retain independent callee and whole inert argument derivations plus the original complete Call relation: same provider/receiver/receipt/carrier, actual entry/consumer, all admitted challenges and observations, invocation Return/Request, and ordered pending suffix. The application effect cannot be replaced by a simple union of component rows without an original rule.

All original forms remain in scope: 13 expression forms (Literal, Primitive, Name, App, RefSet, Lambda, Tuple, Record, PolyVariant, Select, Case, Catch, Block), 11 pattern forms (Wild, Literal, Var, Tuple, List, Record, PolyVariant, Con, Ref, As, Or), and 3 statement forms (Let, Expr, Module). The report preserves each constructor's source-order, binding, guard, annotation, publication or comparison obligations and marks concrete realization equations unresolved rather than rejecting or narrowing forms.

Effect hygiene remains a static source obligation. Permission, actual inflow and residual stay distinct. Alias sharing, independent instantiation, recursive publication, all uses/futures, event scope and the one correlated witness must remain in `Ξ`/`ω`. This audit proves no new effect law.

## Exact stop and parent delta

The candidate declarative judgment can faithfully restate the selected Source-Generalize judgment if it carries the complete original rule evidence. That restatement does not establish the missing map from an independently solved Simple-sub assignment into those rules. If the candidate carries only a `τ ! ε` projection, correspondence is likewise unproved.

The first exact local stop is the selected Source-Generalize construction's L1 / §3.1 Literal equation: a static literal derivation must imply the authentic original literal declaration's complete typed relation at the same occurrence and under the same `Ξ/ω`, including guards, effects and permitted alternatives. The selected authority retains this local obligation but does not supply its law. L2/L4/L5 also preserve original Return, Call, world and future obligations.

Therefore **no unchanged parent premise is discharged**. `InferenceSoundness` still requires, from the same satisfying assignment, an original `sourceJudgment` witness and `sameScoped` package. Source-scoped coverage, principality and termination also remain open; no new proposition, source semantics or narrow source subset is adopted. The parent delta is `0/4 roots; 0/5 packages`.

Falsifiers retained for any future proposal: erasing the string branch; dropping a Function effect port or changing its variance; conflating permission and inflow/residual; omitting any Call challenge, observation or pending suffix; splitting the shared witness; or claiming source correspondence from a type/effect projection without the realization equation.

## Integrity correction

The initial R202 contract text had a mistyped R201 outcome digest. Before independent review, the primary corrected it, recomputed the contract SHA, and the architect reauthenticated all five current pins. The final contract and pins listed above match. The earlier draft contract hash `2232d090…` is superseded; it is not the contract reviewed for this outcome.

## Independent review and next step

The fresh `spec_auditor` reviewed the exact pre-receipt outcome SHA-256 `1f13bde570059042cfec33f8551ad3e8a7b9768c296a86053fcf76a6cc6ef473` and final contract SHA-256 `4ec339119cc66db8b9f7a6c3db7ce52d113bbd4b7f5d52728c94ab8556a6ed88`: **PASS**, zero blocking/major/minor findings. It authenticated all five pins, including the corrected R201 digest; confirmed preservation of source forms, both entry modes, annotations, Call, effect distinctions, recursive publication and the shared scoped witness; and confirmed no replacement semantics or proved correspondence was claimed. Parent delta remained zero. Review limitation: documentary conformance only; no theorem, axiom audit, implementation correspondence, runtime activity, or test evidence was verified.

Next, retain the selected declarative boundary and make the literal source-realization and Simple-sub reflection maps explicit as separate proof obligations. Do not resume L1 construction from Rust runtime representations, and do not report parent progress until an original premise is actually discharged.

## End dispatch

The `next_action_selector` reviewed the completed R202 result and recommends a precise stop: no safe constructive proof packet is ready from the frozen inputs. The exact blocked edge remains “independent Simple-sub literal solution → selected Source-Generalize §3.1 literal local relation,” at the same occurrence, scope and shared witness. R201 already built candidate literal outputs; repeating that work would not identify them with the original relation.

Before assigning a proof, Luna as primary source-model authority must authenticate or define the original all-payload literal local relation, including descriptor/value interpretation, guards, effects, permitted alternatives and scoped dependencies. This must be an explicit mathematical definition or an authenticated existing definition; the solution-to-relation implication must remain a theorem obligation, not an assumed law. The dispatcher classifies this as missing model input, not a counterexample or a request for changed semantics. Current disposition: **BLOCKED_AT_L1_DEFINITION**; no new worker or Rust task. Resume when an approved relation or a derivation identifying it exists. Parent delta remains `0/4 roots; 0/5 packages`.
