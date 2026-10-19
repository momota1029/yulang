# R85 positive role-call contract and adoption offer

Date: 2026-10-19  
Status: Draft; proposed semantics remain unadopted  
Sprint: `effect-hygiene-runnable-role-slice-20261019-r85`, revision 1  
Baseline: `af3ccf2d63ba7f87e0359e183568db548ea53307`  
Approved by: none

This file is the **only R85 semantic decision surface**. The sprint contract,
proof, readiness and reviews cite its exact hash. They must not restate or
extend its proposed semantics. This offer deliberately gives positive
certificates only to a bounded matching interface; it defines no general
three-way declaration classifier.

## 1. First executable call

```yu
role SecondInt {
    my second: int -> int -> int
}
impl int: SecondInt {
    my second self selected = selected
}
my answer = SecondInt::second 1 2
```

The proposed result is `2`. The role qualifier identifies one member; the
receiver is the first ordinary curried Call/Apply stage. The first executable
milestone is this exact Value/int instance. The same role-preservation argument
also covers a finite matched parameter vector whose entries are Value `int`,
Value unit `()`, or explicit `[_] int` Computation, when ordinary inference
establishes every required endpoint. Those additional shapes do not block the
first run.

## 2. Positive interface relation

The R85 interface relation is a **positive certificate premise**, not a total
classification of every possible declaration pair. For a role member and an
implementation member, `InterfaceMatch` holds when all of these facts are
already established:

1. The signature is a module-local monomorphic member with an `int` Value
   receiver, ordinary `int` result, and one or more explicit parameter slots
   from Value `int`, Value unit `()`, or explicit `[_] int` Computation.
2. The implementation is an authentic member of that role's `int` receiver
   implementation, with one executable receiver binder and the same finite
   number of simple explicit binders.
3. Ordinary endpoint evidence establishes the same supported endpoint type at
   each corresponding receiver/formal position. An unannotated formal remains
   Value under §21; its `int` endpoint must come from ordinary inference.
4. Charter §21 assigns the same entry role to each paired signature/formal
   slot from the executable formal's own source annotation. A role signature
   does not rewrite the executable binder.

`InterfaceMatch` makes no judgment about a body result. It does not prove the
member identity is unique, validate the body, select a target, construct a
Call graph, admit a candidate, or establish runtime support. It supplies none
of the R84/R81 producer obligations P1–P4.

When an interface pair does not meet these premises, it receives **no R85
positive certificate**. This offer does not classify that pair as
`Incompatible` or `Unsupported`, does not declare a language error and does not
add adapters. Existing ordinary syntax, name resolution, type/effect checking
and diagnostics continue to govern their current domains. A future rule for
non-matching interfaces needs its own explicit design decision.

## 3. Separate obligations after interface match

These obligations are independent and must not be folded into
`InterfaceMatch`:

### CheckedBody

Ordinary inference and checking validate the actual implementation body
against the role member's declared result and effect obligations. A body that
returns the wrong type does not receive `CheckedBody`; this is handled by the
ordinary body/result checker. R85 adds no body-result mismatch classifier or
new diagnostic.

### ValidatedTarget

The compiler has authentic, unique role/member/implementation identities and
validates the actual body root, lexical environment and original executable
binder annotations. It then constructs the selected member call as the
ordinary graph `Apply(Apply(C_member, E_receiver), E_argument)` with whole
arguments, caller environments and source provenance retained. Complete
candidate metadata is admitted before RuntimeProgram publication. A failed or
ambiguous target produces no R85 executable target; it must not be resolved by
spelling, declaration order or an unrelated admission exemption. New
diagnostic behavior is outside this offer.

### Ordinary execution

Given `InterfaceMatch`, `CheckedBody`, `ValidatedTarget` and successful
ordinary literal/Name/Call transitions, existing receiver-first Apply
consumers execute the pure example to `2`. The call and actual producers are
future work. An adoption decision alone is not evidence of current execution.

## 4. §21 role-preservation claim

For every matched explicit formal, the executable binder's own source
annotation determines its role: unannotated or ordinary value annotations
enter as Value; an explicit outer `[_]` annotation enters as Computation.
`InterfaceMatch` compares the signature role with that actual binder role and
inserts no annotation or adapter. Therefore the positive certificate preserves
the binder's §21 role at every paired position. This finite source relation
does not prove that a future producer retains those binders or that the full
source/runtime theorem is closed.

## 5. Method-syntax boundary

R85 proposes `Role::member receiver args` for the first role-qualified method
call. It leaves `receiver.member(args)`, dot dispatch, field/method precedence
and callable-field collisions OPEN. The exact call lowers to existing ordinary
curried Call/Apply; no special method evaluator is proposed.

## 6. Breadth of effect-hygiene obligations

The effect work remains broad in coverage and bounded in proof obligations.
The six evidence/owner/falsifier rows from R84 readiness are preserved in the
R85 readiness artifact:

1. ordered handler matching and priority;
2. Value/Computation entry under §21;
3. wrong or sibling permission;
4. a shallow unmatched outward request;
5. one continuation capture/resumption path;
6. one static-to-runtime path.

No row is silently discharged by `InterfaceMatch`, the role-call proof or a
successful first run. Protected-sibling behavior, full continuation
preservation, native K,D/residual correspondence, original F1/FK1 and
source/native A/B remain OPEN. Storage/fiber inventories and dot-method
collisions are not prerequisites for this first call.

## 7. Exact adoption question

After independent compiler and specification review, the user can adopt or
reject this exact package as a unit:

1. Accept `Role::member receiver args` for the first role-qualified method
   call, with receiver first and ordinary curried Call/Apply lowering.
2. Accept only the positive `InterfaceMatch` relation above for issuing an
   R85 certificate; define no general mismatch classifier, language rejection
   or adapter rule here.
3. Keep ordinary body/result/effect checking separate as `CheckedBody`.
4. Require authentic unique identity, source-owned binder/body/environment
   retention and complete candidate admission as `ValidatedTarget` before
   execution.
5. Preserve executable roles from each binder's own source annotation under
   §21; do not inherit roles from signatures.
6. Keep all six effect-hygiene rows as open, evidence-led obligations with
   their current owners and falsifiers; do not block the first call on unrelated
   storage/fiber or dot-collision work.
7. If adopted, make the next sprint the vertical implementation of
   `SecondInt::second 1 2`, with exact source owners and future verification
   commands pinned before running anything.

This offer grants no code, test, fixture, diagnostic, expected-output,
production or Git authority. It does not narrow the original Simple-sub/A/B
claim or close any parent obligation. A clean review and explicit adoption are
required before a separate implementation contract.
