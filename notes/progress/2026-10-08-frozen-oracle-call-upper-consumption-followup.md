# Frozen Oracle: per-formal call-upper consumption follow-up

Date: 2026-10-08
Yulang3 baseline: `800c490e382a432d17d9e1761f615640f34d7911`
Frozen Oracle: `/tmp/yulang2-oracle-rebuild`, `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Status: bounded historical characterization; compiler-referee reviewed after repair
Authority: none for current language semantics, proofs, or production implementation

## Question and finding

The current `ORIGINAL_ASSOC` gap requires an independently typed original
owner/view-kernel producer for the ordinary `f x` Call: source-stable
`beta`/`Slots(beta)`, typed `p0`, ownership of the complete receiver
contribution, and one original `xi=(nu,K,D)`. Earlier Oracle archaeology found
per-formal call-upper accumulation but left its consumer path unresolved.
This follow-up traces that retained historical data into construction of a
Lambda's public parameter upper.

The nearest historical mechanism is a two-stage, formal-keyed aggregation:
each eligible local-call occurrence retains a `NegId` Function upper under its
resolved formal `DefId`; later Lambda lowering selects a public, nested
projected, erased, or original formal upper, and can observe selected argument
and return components across those call uppers. This is a concrete
source-to-interface construction path in the historical implementation. Its
conditional branches and omissions prevent identifying it with the current
original source judgment.

## Historical data flow

All Oracle paths below are relative to the pinned checkout.

1. `lowering/expr/tail.rs:690–704` resolves a direct local callee to its
   `DefId` and reads that local's projection state. Under the existing
   `call_erased_upper` guard, `:603–614` records the application-specific
   `callee_upper` via `record_local_call_upper` and separately submits the
   local value against the erased annotation upper. The recorder
   (`:707–716`) sets `call_erased_used`, records nested-frame status and
   appends distinct upper IDs to `LocalBinding.call_uppers`.
2. `lowering/local.rs:6–23` shows the shared formal state: resolved `DefId`,
   value endpoint, annotation/public and erased uppers, projection flags,
   per-call upper IDs and frame markers. The list is keyed by the formal
   record, not by a source Call occurrence: the appended item is only a
   `NegId`.
3. At Lambda construction, `lambda.rs:978–1039` retrieves that local state
   from the Lambda parameter's binder. Branch priority is explicit: use a
   declared public upper if present; else, for an eligible nested projected
   call with retained uppers, build a fresh projected endpoint and submit
   `Pos::Var(projected) <: call_upper_with_body_effect(U_i, body_effect)` for
   every observed upper; else use an erased annotation upper if present;
   otherwise use the parameter's
   original value variable.
4. For public or erased annotation branches,
   `callable_upper_with_observed_wildcards` (`lambda.rs:1041–1095` and
   following lines) can replace a `Bot` argument with an observed argument
   endpoint constrained from every retained call upper, and replace a wildcard
   `Top` return with an observed return endpoint. For each retained call upper
   whose return is a variable, the consumer submits both
   `observed_ret <: call_ret` and `call_ret <: observed_ret`; this is mutual
   subtype coupling through the fresh endpoint, not a one-way join. The
   annotation still supplies the other ports, including its effect ports.
5. The unannotated path is separate. `tail.rs:740–799` can build a
   frame-scoped push/pop wrapper around the call return effect for unannotated
   formal locals. `unannotated_call_frame_index` (`:801–825` onward) selects
   the relevant defined frame with an active-skeleton exception. This supplies
   historical frame/effect plumbing, not an original static call slot.

## Conditional discriminator

Assume two direct call occurrences resolve to the same local formal `d`, both
pass the erased-upper recording guard, and their Function upper IDs are
distinct `U1` and `U2`. The recorder retains both in one `call_uppers` vector.
Assume further that the parameter's declared public upper has a bottom
argument port and top return port. At Lambda construction, the helper creates
fresh observed argument/return endpoints. Each call argument is constrained
below the observed argument endpoint. Each variable call return is mutually
subtyped with the observed return endpoint. Unmentioned annotation ports
remain sourced from the annotation.
This is a control/dataflow derivation from the assignments and guards, not an
execution or claim about satisfiability, solving, or an accepted source
program.

The discriminator shows why the historical mechanism is more than “all calls
share one variable”: it explicitly retains several call constraints, then
uses selected value ports to refine wildcard positions of a separately
prepared formal upper. It also shows why `call_uppers` cannot simply be read as
the missing current tuple: the retained elements carry no source Call key,
typed path, receiver identity, contribution owner, exhaustive slot inventory,
or shared original `xi`. The enclosing Lambda branch and effect/frame guards
determine which projection is used.

## Authority boundary and limits

This historical path may guide a correspondence question: does the successor
source producer need a per-formal shared interface plus occurrence-indexed
call contributions, with a separately specified projection from complete
calls to the interface? It cannot answer that question's semantics. In
particular, neither `DefId`, `NegId`, an annotation endpoint, an observed
argument/return port, nor a selected frame is identified here with
`beta`, `p0`, `s`, `c`, or `xi`.

No Oracle query, output, test, build, or mutation was used. Blob equality
establishes only that the inspected historical source matches the pin. The
route shares one historical implementation's assumptions and is not an
independent semantic oracle. This result closes no current proof or semantic
gate; `ORIGINAL_ASSOC`, `SIG_RULES`, licensing and admission remain open.

## Scope and checks

Inspected the direct call-upper producer/recorder, formal state, Lambda public
upper consumer, wildcard refinement helper, and unannotated frame/effect
route. Oracle `HEAD` equals the stated pin. Each directly used file matched
its pinned Git blob byte-for-byte:

| Oracle source | SHA-256 |
| --- | --- |
| `crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| `crates/infer/src/lowering/local.rs` | `300bc2b12d8f13aed0ae5f65cdec93683e7de2719be38bb33724f51730e52f81` |

No test, build, executable experiment, benchmark, Oracle run, or Git mutation
occurred. The note changes no source interpretation or production code.

An independent compiler-referee review found one minor imprecision in the
observed-return description. The repaired text now records the two subtype
directions for variable returns and the projected-branch constraint direction;
the referee's delta review passed. This review covers the note's bounded
historical claim only, not current semantic validity or theorem closure.

Recommended next action: use this as a historical correspondence target while
constructing the independently typed current owner/view-kernel introduction;
do not import the historical wildcard, annotation, frame, or effect rules.
