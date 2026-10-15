# Native permission, inflow and residual: constructor/consumer audit

Status: independently reviewed source characterization; no implementation or theorem
closure. Baseline supplied by primary: `cfded839e`; runtime owner supplied as
unchanged `35e87f844`. Method: bounded static constructor/consumer tracing.

Independent review: compiler-referee `ordinary_carrier_semantic` returned CLEAN
at producer SHA-256 `39ba7ae533b06e717097be8064618343b4b0bf19617b72d8f400fd028b93b6bf`.
The reviewer checked current annotation policy §1.2 after its review-metadata
update (current SHA-256 `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`);
the producer's earlier read snapshot remains recorded below. All compiler and
other authority hashes matched. General subtraction and the original parent
remain OPEN.

## Authority and claim boundary

The exact question revision 1 / approved draft `annotation-declared-envelope-a1`
revision 1 governs. Its approved answer distinguishes declared permission,
constraint-derived inflow and subtraction residual. A declaration alone does
not justify adding a member back to a residual with no such inflow. Unknown
variables, filters and symbolic dependencies remain. It selects neither offered
option and gives no blanket verdict on Support. See the integrated design
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §1.2 and the
top-level inference principles §1/§1.1.

This audit establishes a concrete declared-interface-to-call-effect route. It
is justified by `questions/2026-10-05-source-annotation-boundaries/approved-answer.md`
decision 2: after checking the current endpoint against the target, the target and
realization evidence pass outward; the next boundary uses that endpoint.
`notes/design/2026-10-10-concrete-effect-annotation-implementation.md`,
“Annotation checking and publication owner,” explicitly requires checking the
body against the negative target and publishing the positive target, with
Support as a structural **type operand**, not an emitted contribution. The
new correction does not revoke this exposure rule. No examined ordinary native
constructor
first computes an exact handler residual and then adds annotation members back
to it. Consequently this is not a source-qualified residual counterexample.
The original all-`xi,z`, same-provider FIRST-RESULT-ADEQUACY gate stays OPEN.

## Operand roles at actual owners

Locators are in `crates/yu-solver/src/` unless otherwise stated.

| Constructor / operand | What justifies its members | Executable consumer / resulting role |
| --- | --- | --- |
| `candidate_effect.rs:1145` paired positive formal port, explicit covariant row | Declared annotation contract at the actual typed position; same view for positive Support and negative Allowance | `candidate_formal_annotation`, slots 43/44, exposes/checks the paired Function and retains its negative domain. Nested variance determines which Function side carries Support. This is not an operation event. |
| `candidate_signature_effect:1619,1690`, positive annotation signature | Declared covariant interface members plus an optional shared symbolic tail | Module annotation / local annotation / expression ascription expose a positive Function. Function RE comparison can propagate this Support into an invocation row; ordinary effect comparison expands it into all AnnotationMembers and the tail. |
| `candidate_signature_effect:1619`, omitted covariant annotation port | An empty declared view, not a discovered event | Empty Support expands to no members. Omitted formal ports instead use shared rows at `candidate_formal_effect_port:1147`; do not identify these cases. |
| `candidate_signature_effect:1584`, operation outer RE with no explicit row | Mandatory operation family, with actual operation declaration and lookup occurrence retained in `ViewOrigin::Operation` | Lookup exposes a callable; actual Apply RE dispatch puts the family into invocation type support. Lookup alone is not invocation. |
| `candidate_signature_effect:1659–1683`, operation outer RE with an explicit row | Mandatory operation family **and** declared signature members; they share one Operation-origin view | All are expanded by the same Support consumer. The mandatory family has a request-constructor justification; companion declared members must not thereby be called actual emitted requests. Nested signature ports receive no outer family. |
| `candidate_catch_operation:821–864`, positive payload/response Function signatures | Packet field's declared interface | Payload/continuation typing uses signature construction. The code expressly does not inject the outer operation family into these packet fields. |
| `candidate_effect_contribution:949`, Contribution | Retained concrete family and source origin, distinct from an annotation view | `candidate_check_effect_operand:1004` checks its family against Allowance or forwards it into the unmatched tail. This constructor is not called by ordinary `candidate_operation`; FreshUse recreates existing Contribution operands at `candidate_scheme.rs:1191`. Tests also manufacture Contributions. |
| `candidate_annotation_computation_effect:1432`, root computation row | Actual initializer evaluation effect is the lower; annotation is its negative Allowance | Explicit comment and implementation prevent a positive root Support from entering initializer/local scheme. Listed members are accepted, unmatched members constrain the tail, and unknown tails remain rows. This is a check, not a proof that every listed member flowed. |
| `candidate_formal_entry_annotation:1176`, concrete computation-formal row | Permission for local handling; symbolic tail equated with actual entry row | Concrete members generate no Support/closed incoming upper here. Actual formal Name effect is separately linked by `Action::FormalNameEffect` (`candidate_source.rs:1353`). |

The first table row's exact publication owner is
`candidate_effect.rs::candidate_formal_annotation`: positive-to-parameter slot
43, parameter-to-negative slot 44, and `formal_domains.insert(parameter,
negative)`. The symbolic method name, rather than a moving line number, fixes
this locator.

`candidate_signature_value:1512–1561` flips polarity and variance in Argument
and ArgumentEffect, preserving them in Result and ResultEffect. The live
Function consumer at `lib.rs:12630–12662` compares upper Argument/AE against
lower Argument/AE and lower RE/Result against upper RE/Result. It does not
inspect an implementation body to decide which declared members to remove.
`candidate_function_port_admit` (`candidate_context.rs:3001`) preserves the
actual parent/source relation, swaps inherited context on Argument/AE and
preserves it on RE/Result. Scoped flow additionally stamps AE and protects RE;
unscoped and scoped execution must not be identified.

## Authenticated small source routes

### Pure body with a declared interface

The existing source fixture in
`crates/yu-solver/tests/candidate_effect_annotation.rs:69` is:

```yu
act E
my id x: int -> [E] int = x
my first = id 1
my second = id 1
```

The earlier test in that file inspects the HIR annotation as the **whole
generated lambda**, with Int argument, Int result, and declared E on its result
effect. The fixture asserts successful candidate inference and two fresh alias
uses; these assertions were read, not executed in this audit. There is no
Operation expression in `x` or `1`; the source gives no E request constructor.

Actual static route for either use, preserving its own source Call:

1. `candidate_source.rs:1153` schedules the binding Annotation.
   `candidate_annotation_pair:1355–1390` checks the generated lambda against the
   negative annotation and publishes the paired positive annotation to the
   binding root at slot 41. Both sides share value/effect variables and views.
2. Its positive Function RE contains Support of the E view
   (`candidate_signature_effect:1690`). This is declared-interface support.
3. Module route / FreshUse preserves Support with its mapped view/tail
   (`candidate_scheme.rs:1176–1182`); no body/event classifier is inserted.
4. Apply allocates its invocation row and builds a negative Function with that
   row as RE (`shadow_apply.rs:1565–1584`). The authentic source-call observer
   verifies this exact association (`candidate_call.rs:482–492`).
5. Function RE dispatch constrains exposed RE to that invocation row
   (`lib.rs:12647–12653`). Apply slot 2 then constrains the invocation row to
   the application effect (`shadow_apply.rs:1675–1682`).

Thus this executable native relation carries declaration-side E support into
the call's effect type through its declared interface, as required by the
approved target-publication rule. It does not establish runtime E emission.
The same route is present for local annotations:
`construct_candidate_local_annotation:1278–1290` checks the actual initializer
but installs a new root containing the positive annotation; the original
initializer evaluation effect stays on its block edge.

### Actual operation family

The existing fixture at
`crates/yu-solver/tests/candidate_operation_source.rs:73` instantiates:

```yu
act tick:
    our next: () -> int
my answer = tick::next()
```

The source owner is `LocalSourceForm::Operation` resolved to its original
declaration; `candidate_operation:803` builds that declaration's positive
signature and emits it at slot 42. `candidate_signature_value:1544` injects
`tick` only for the outer signature's RE. The same actual Apply/RE path above
propagates this operation-family support. The companion lookup-only fixture
at lines 43–58 explicitly has zero source Calls. Hence operation lookup,
invocation-family type support, declaration companions and event emission
remain distinguishable even though native comparison uses Support for several
roles.

These are independently retained source constructions, not freely chosen
profiles or a scalar equality argument. No new source acceptance claim was
obtained by execution.

## Handler, filter and Allowance consumers

* **Ordinary Catch:** `candidate_source.rs:870–885` emits scrutinee effect to
  Catch effect at slot 51 and adds arm effects. This is a conservative forward
  edge. It is not a subtraction algorithm and cannot authenticate a claim
  about the exact subtraction residual of the examples above.
* **Allowance:** `candidate_check_effect_operand:980–1040` expands Support into
  every view member plus its unresolved tail. Contribution/AnnotationMember
  checks nominal membership. A listed member succeeds without being inserted
  into the tail; an unlisted member is constrained into the tail if present.
  This consumer therefore does not itself add listed declarations to an
  otherwise empty unmatched tail. Unresolved tail propagation is explicit.
* **Context filter discharge:** `candidate_context_execute_relation:3230–3288`
  validates executable zero-word filters and applies/replays the same actual
  lower against Allowance. It stores a residual **context expression** for
  future propagation; this is not an effect-row subtraction result. It does
  not construct a new positive Support. Nonempty filters on Value and
  unsupported symbolic/context fragments remain availability boundaries.
* **Private receiving residual experiment:**
  `candidate_receiver.rs:322–521` is separate from ordinary solve. It requires
  one original module use, intercepts one original Catch slot-51 edge, follows
  actual lower bounds, and expands closed Support to members. A symbolic tail
  or an unestablished empty row stops the experiment. At lines 465–494 it
  suppresses only the selected family whose view has the exact selected
  **Operation** provenance. Annotation-origin members are forwarded unchanged
  at lines 496–500. No subtraction result is independently supplied to this
  decision. This restricted experiment cannot decide whether a declaration
  member reached its input as actual inflow or only as an exposed interface;
  it must not be generalized to the approved source domain.

## Result and next owner

Established bounded characterization: positive declaration support can reach
an actual application-effect row; root computation Allowance does not insert
its listed members into the unmatched tail; ordinary Catch has no exact
subtraction consumer; the private residual experiment distinguishes Operation
and Annotation origins but does not establish the permission/inflow bridge.

No genuine source/native disagreement after actual subtraction was established.
Pure body plus exposed declared type alone is insufficient for that verdict.
The exposed Function RE is a justified source-type input to the invocation
constraint; replacing it with the original body's narrower endpoint would
contradict the publication rule. The unresolved correspondence lies at the
**actual subtraction owner**: construct the permitted local subtraction on
constraint-derived inflow with genuine attachment/context inputs, preserve
unresolved dependencies, and show the residual does not acquire additional
members solely from a permission declaration. Ordinary Catch's forwarding edge
and the narrow private experiment do not establish that bridge. This is an
existing source-subtraction implementation/proof gate, not an unresolved choice
about target exposure. Preserve correlated W/F_R and all original xi,z.

Recommended next action: apply the established target-publication law to the
exposed-RE→invocation edge, then assign the existing subtraction owner the exact
attachment/inflow/residual bridge. If a reversible observation is
then needed, inspect that one source Call's original RE bound origin and one
Catch input/output relation; do not add a body classifier, packet execution,
new registry, or scoped-guard bypass.

## Frozen dependencies and resource use

SHA-256 read snapshots:

* approved answer: `7c564a6e28c85059473b2c8498fdff72fd5f5e8f6378e9a8dce2780b63d69785`
* hygiene integration design: `00e032688c1d146c782e96c2978045fbacc8709da9e27d10a1888e9558f0ee7d`
* source-annotation-boundaries approved answer: `e1e2ff77b181fe42edd404ee0d69cfc6d3bb0fbc99ba7e7f092710025d11fb12`
* concrete annotation implementation design: `3a3186723cd93edd2f767a7e4a481cb6dbed701fc749502e640071f65a4d89ae`
* candidate_effect.rs: `a330100b418f14be1c8f600c62970efdb4859818b603190846796de39fa8cef2`
* candidate_source.rs: `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38`
* candidate_receiver.rs: `620b09011ec4dc4bfa71998e2b6fc1498b9299b3056662fdaa80b17376ba23c3`
* candidate_context.rs: `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6`
* lib.rs: `199963ac9cd13eebca44c4881b859eeb1f801259cc944bf1d5a57df78dc0c070`
* shadow_apply.rs: `357b274d0de509931bda3015a99b1a1cf2ac86d75a45d230d62ab456c56740ba`
* candidate_call.rs: `cbad9cf51a05343eb7a29ab77aac520891467a8aa4edc3201ea3d91f978984a1`
* candidate_scheme.rs: `2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e`

Checks: bounded `rg`/`sed`/`cat` reads, dependency `sha256sum`; no test,
build, probe, Git operation, delegation, or runtime execution. One research
artifact written. Aggregate wall time within assigned 15-minute static pass;
CPU/RAM not measured. Existing test assertions are static source evidence,
not fresh verification. Shared status/theory/design updates and independent
review remain with the primary.
