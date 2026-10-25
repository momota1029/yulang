# Question: operational wrap graph-guard rule

Question ID: `2026-10-26-operational-wrap-graph-guard`
Question revision: 1
Predecessor/history: none; follows R30–R33 source/authority intake at commit `b5c4f2b81`
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): Yulang branch commit `b5c4f2b81`; operational manuscript `docs/yulang-operational-type-safety-ja.tex` SHA-256 `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`; source manuscript SHA-256 `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`; raw syntax SHA-256 `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`
Task/thread locator: current working conversation; external locator unavailable
Governing source/section: `rules/design-authority.md`, “Approval and implementation gate”; `rules/question-board.md`; operational manuscript `:151–165,184–185,224,258–268,362–376,1002–1008`; R33 intake `tasks/agent-loop/inbox/paper-wrap-guard-authority-intake-r33.md`

## Requested scoped decision

Give one complete constructor-indexed operational rule for `wrap` during typed finite-graph head observation. Treat the following points as a single decision because the cycle judgment, callable shape argument, and adapter typing depend on them together:

1. Whether reaching `wrap` itself satisfies the graph guard, observation stops at that wrapper, or both guard and traversal behavior apply.
2. Whether observation follows the wrapped function child, and the order used through nested wraps.
3. Whether references in argument/result adapter code are immediate graph edges, deferred code edges, or handled by another explicit rule; state when those references participate in observation and cycle checking.
4. How the rule retains the outer callable type `C(A',B')`, inner callable type `C(A,B)`, and both adapter typing derivations when observation crosses a wrapper.
5. The guard outcome for a wrap-only function-reference cycle and for nested wraps, with the exact finite-graph premise that makes callable shape reasoning sound.

An alternative rule is acceptable if it answers all five points explicitly. No source correspondence inference or call-entry peeling rule alone resolves this question.

## Background and current premises

The operational value grammar includes `wrap(v,a,r)` and describes `a` and `r` as argument/result adapter code (O `:151–165`). Its `rec` clause says cycles go through actual data, lambda, or delay and excludes alias/roll/type-evidence-only cycles, but does not state the `wrap` case (O `:184–185`). The typing rule gives `wrap(f,a,r):C(A',B')` from `f:C(A,B)`, `a(z):A` under `z:A'`, and `r(z):B'` under `z:B` (O `:224`).

The finite heap `H` and type map `Xi` are immutable and graph typing requires every node to type under `Xi` and satisfy the guard premise (O `:258–268`). Separately, `Call` entry peels wraps, delays the argument adapter and saves result adapters; argument-adapter code is not executed during peeling (O `:362–376`). The callable shape argument can expose lambda or wrap at type `C(A,B)`, without defining the graph edges or guard behavior for wrap (O `:1002–1008`).

R30–R33 identified this as the first unresolved constructor classification after the supported data/lambda/delay cases. The source manuscript's SCC/closure account can establish capture correspondence, but it does not select the operational guard rule. The current paper is a research derivation, not an approved production specification. Preparing this question does not adopt a rule.

## Options and consequences

These are candidate shapes for a complete answer, not endorsed semantics. A different answer may supply another explicit rule.

1. **Opaque guarded wrapper:** `wrap` itself satisfies the guard and head observation stops at the wrapper. This makes a cycle through the wrapper pass without exposing the underlying function or adapter references to that observation.
2. **Transparent function edge:** `wrap` is not itself a guard; head observation follows the wrapped function in the stated order. Adapter references remain deferred or separately represented under an explicit rule. The function-position self-cycle below is rejected unless some inner constructor supplies a guard.
3. **Guarded traversal with typed edges:** `wrap` satisfies the guard and observation also follows the function child, while adapter code has separately labeled edges and explicit typing/observation conditions. The answer must say how the wrapper guard composes with cycles reached through each edge.
4. **Other complete rule:** state the constructor clause, all edge labels/order, guard condition, adapter behavior, type evidence, and both discriminators below.

**Function-position discriminator.** `Xi(r)=C(A,A)` and `H(r)=wrap(graphReference(r),idArg,idResult)`, with identity adapters admitted under their ordinary code typings. A rule that counts the wrapper as a guard permits the wrapper cycle at that constructor; a transparent function edge with no wrapper guard follows `r → function → r` as an unguarded cycle. This is a discriminator, not an established typed graph counterexample because the missing constructor rule controls graph-edge observation.

**Adapter-only discriminator.** Put a recursive reference only inside deferred argument-adapter code while the wrapped function is a lambda with no such recursive reference. A rule that follows every nested syntax child and a rule that follows only the callable function edge observe different paths. The finite-heap typing/admission of this case must be stated rather than assumed.

## Affected work

Blocked scope: final paper classification of `wrap`; full constructor-indexed guard theorem; typed graph observation and callable shape proof where they depend on `wrap`; source/native correspondence and any implementation or production work depending on those rules.

Independent authorized work: unrelated proof and compiler gates may continue under their existing authority, leases and budgets. All A/B, source/native and production parent gates remain OPEN.

Required answer: give the complete scoped rule requested above, including whether it is intended as an authoritative language decision or only a manuscript correction candidate. If it changes operational semantics, it still requires independent review and explicit user approval under the governing design process before adoption or implementation.

Pending publication: keep this entire question directory unstaged and uncommitted until the questioning primary discovers and validates an explicitly approved local answer and commits the matching question/draft/answer together. The answering primary never mutates Git. Posting the question does not pause the goal; only dependent wrap-guard work waits.
