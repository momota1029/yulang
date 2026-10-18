# R21: source distinctions for the field-root bridge audit

Status: FROZEN research-only falsifier specification, revision 1; independent review pending.
Author: `/root/r21_bridge_falsifiers`, sole author, no descendants.
Baseline: primary-pinned `d2ff62845`, R21 contract rev1. Parent OPEN; original closure 0.

## Evidence classes

The R21 contract reports R20's exact focused runtime target passed 18/18. Its local-g fixture and sibling control may therefore be reused as baseline implementation evidence within that receipt's scope. This author did not rerun or independently observe that test. Runtime receipt success does not prove a captured static field task or the parent theorem.

The checked-in solver tests `v1_source_argument_selects_and_consumes_the_exact_callback_definition` and the two v1 conflict-publication tests express the baseline source contracts described below; this author read their source but did not run them. Their expected assertions are test specifications, not new observations. In particular, the old source tests distinguish `response` and `other_response` identities with identical annotations.

Every newly written source mutation below is a **candidate**: parse, HIR admission, candidate acceptance, actual field receipt, and execution are UNVERIFIED. A read-only matcher calculation establishes only the listed structural property conditional on the expected HIR shape. General saved-suffix contexts are explicitly **hypothetical/original-open** when they fall outside the v1 matcher. No source-qualified counterexample is claimed.

## Baseline specimen and exact initializer selection

The baseline response specimen has:

```yu
act outer:
    our next: () -> int
act signal:
    our ping: () -> (int -> [outer] int)
my result = catch signal::ping() {
    signal::ping(), k -> {
        my response: int -> [outer] int = \x -> outer::next();
        my other_response: int -> [outer] int = \x -> outer::next();
        k response
    }, v -> v
}
```

The existing source test selects `k response` and `k other_response` in separate runs and expects different recorded response-definition identities. The same-family operation body and same annotation text cannot select the member. R6's exact resolved h_arg and the distinct callback operation occurrence are essential.

A stronger unexecuted mutation declares `outer::other: () -> int` and changes only the selected callback body to `outer::other()`. Expected evidence obligation: c at the unchanged ping request stays fixed, while the selected callback-operation declaration/use and corresponding native member provenance follow the actual new body. Keeping old m0 because `[outer]` still matches is invalid. Numeric IDs across separately lowered HIRs are not assumed stable; comparison must use each compilation's resolved source positions and declarations.

A pure-body mutation `response = \x -> 0` has the same compatible annotation at the source-language level, but fails the current v1 matcher's required Lambda-body Apply/Operation shape. It cannot be presented as a v1 accepted counterexample. It still distinguishes the general principle: an allowed effect annotation alone proves no actual callback-body operation lower.

## Smallest direct-scrutinee arm-discard candidate

```yu
act outer:
    our next: () -> int
    our other: () -> int
act signal:
    our ping: () -> (int -> [outer] int)
my result = {
    my g = catch signal::ping() {
        signal::ping(), k -> {
            my response: int -> [outer] int = \x -> outer::next();
            my other_response: int -> [outer] int = \x -> outer::other();
            my ignored = k response;
            other_response
        }, v -> v
    };
    g 0
}
```

Inspection of `operation_v1_catch_source` establishes that its `find` searches recursively through block binding initializers and final expression for the unique Apply with callee resolving to the chosen CatchBinder and argument resolving to a local definition. It does not require that Apply to be the arm's final expression. The candidate above preserves direct `signal::ping()` scrutinee, a unique `k response`, an exactly annotated response, and the required callback-body operation shape. Conditional on that HIR shape, the h_arg matcher selects response, not other_response.

`Work::Finish(Catch)` constrains the actual arm-body endpoint into the Catch result. In this block, that endpoint comes from the final `other_response`, not the ignored binding. Source/value semantics therefore require separate result provenance. The companion note's minimal model explains why promoting response m0 to g from h_arg alone is false. Actual source acceptance and runtime results remain unverified. A future discriminating execution can give `next` and `other` different outer-handler results; that is an experiment proposal, not a run in this packet.

The native forwarding calculation is explicit: `candidate_source.rs:1428–1441` gives the Block a `CandidateRelation::Group` whose child is the actual final-expression endpoint; `shadow_apply.rs:1791–1795` checks that child's positive endpoint against the block's negative result endpoint; Catch's slot50 then links the actual arm endpoint into the Catch result. Binding initialization effects use separate block-effect links and are not binding-value-to-block-result edges.

The positive control is `{ my tmp = k response; tmp }`. Here tmp's initializer/result is installed, the final Name resolves to that tmp local, and its actual capture/FreshUse and Group edge supply the result route. Returning tmp is not the same syntax as returning `k response`, yet can preserve the result incidence under the necessary local-use theorem. The negative control is `{ my tmp = k response; other_response }`: the same intermediate computation exists, but the Group child names other_response. A third case `{ my tmp = k response; my alias = tmp; alias }` needs the corresponding chain of real local uses. All three are unexecuted candidates. The rule must follow constructive value provenance through those owners; requiring the k Apply to be syntactically final would reject the valid forwarding route and would not solve the general result theorem.

A still smaller mutation changes the final expression to a pure callback of compatible annotated type, with the same earlier `k response`. This asks whether the bridge fabricates an actual lower for a discarded response. Its v1 h_arg may still be selected from response, but complete typing/receipt behavior is unverified. An ordinary allowed effect overapproximation must not be confused with evidence for a specific original callback member.

## Continuation result matrix

| Case | Status in this packet | Required incidence result |
| --- | --- | --- |
| Direct ping, raw continuation returns response, arm returns that k result | Baseline shape; R20 reports one concrete runtime success. | Derive same actual source field through the exact continuation and final result map; no type-endpoint equality. |
| Direct ping, raw continuation returns response, arm discards k result and returns another callback | New candidate above; matcher structure inspected, full admission unverified. | Response field can remain at its argument/intermediate result; final g uses actual other provider's independent field, if supplied. |
| Saved suffix ignores response and returns a different callback | Hypothetical/original-open for this v1 route: direct-scrutinee check does not accept such a suffix. | No automatic response field at k result; use actual output provider. |
| Saved suffix applies response and returns an integer | Existing ordinary monomorphic source test has an analogous scrutinee `(signal::ping())(1)` with pure callback type; not a v1 effect-field acceptance result. | Response callback field is not an incidence of the integer result. Preserve invocation effects separately. |
| Saved suffix is nonreturning/effectful | Hypothetical/original-open; no execution here. | No completed returned-field receipt without actual return; retain full Call/entry/return/future alternatives. |
| Handler never resumes k | Outside current h_arg requirement when no matching Apply exists. | No resumption incidence; do not interpret absence as an original parent source restriction. |

## Two FreshUses, shared anchors and scopes

Take the baseline local-g source and replace its one final `g 0` by `my first = g 0; g 0`. This is an unexecuted candidate with two resolved Name occurrences. If both routes succeed, `context.begin_use()` supplies distinct context-use IDs. The second route may capture a later graph than the first; equality of their entire capture snapshots is not assumed.

Required discriminating mutations of a future field-use certificate are: replace u2's context-use with u1's; replace its mapped member/allowance/root or source-bound key with u1's; replace its physical emission/drain/ack with u1's; keep correct c/q/h_arg and all same-family text while making that swap. Each must fail the *u2 discharge*. No source program should be rejected simply for having two valid uses.

For shared old/nongeneric anchors, the ordinary row map may satisfy `phi1(n)=phi2(n)=n`. Thus a test that only compares endpoint inequality cannot distinguish the two uses, and a rule that force-freshens n changes the algorithm. Use-indexed evidence and actual graph-node coordinates must carry the distinction. This is a conditional map characterization from the pinned FreshUse owner, not an executed shared-anchor example.

The existing R20 sibling fixture adds `{ my g = g; g 0 }` inside the final block. Its static receipt is reported accepted while the runtime gate rejects attaching the outer g receipt to the sibling cell. That bounds the runtime receipt API; it is not a language rule banning aliases or a proof that static FreshUse transport covers arbitrary scopes.

A future scoped mutation nests the g use or moves a response binder while keeping spelling/family equal. It must preserve actual source ownership and use the authentic scope/input/root/license maps; a foreign binder or missing license cannot inherit the old field. Ordinary operation-v1 disables the scoped experiment, so such general scope behavior is untested and unproved here. Do not label a default empty map an all-scope proof.

## Oracle independence, coverage and failure conditions

No oracle, generator, random seed, range, sample, mutation engine, checker, compiler, runtime, Cargo or build was executed. Independence is methodological: this lane derived the discard witness directly from frozen R20 equations and pinned matcher/Catch owners rather than assuming either proposed bridge's transition rules. Shared assumptions are the accepted source semantics, R6 source identities, R20 owner equations, and the contract's reported R20 run. All-source adequacy, actual provider validity, generic effect hygiene, principality and termination are omitted unresolved obligations.

The finite mutation list covers equal annotations/different initializer and callback; direct return versus arm discard versus hypothetical saved-suffix discard/different provider/nonreturn; two use identities; shared anchors; scope and binder changes; and late-conflict publication. It is not exhaustive enumeration of the original theorem's contexts/providers/worlds/futures. A new concrete run must record parse/HIR/candidate acceptance before being called a source counterexample; a failing admission alone refutes no semantic theorem.

Recommended next action: review the concrete bridge rules against the direct-scrutinee arm-discard candidate and require their result constructor to follow the actual final arm value. Once a rule is adopted and separately implemented, a bounded source-driven regression can discriminate its own-use and discard behavior without injecting proof IDs or endpoint fixtures.
