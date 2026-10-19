# R82 bounded role/member compatibility

Date: 2026-10-19  
Status: Draft; proposed pilot judgment, not adopted semantics  
Sprint: `effect-hygiene-role-call-20261019-r82`, revision 1  
Contract SHA-256: `a11cd61b71548ce144f60557c3c8b6fe32d3cce698b4dd58657fb6e33d85adce`  
Baseline: `af3ccf2d63ba7f87e0359e183568db548ea53307`  
Supersedes: none

## Supported declaration envelope

This single definition is the compatibility domain for the R82 design, proof,
source examples, classifications and adoption offer. A frozen copy's SHA-256
must be cited by each dependent artifact before proof work starts.

An eligible member signature has one Value receiver slot of ground type `int`,
one or more explicit parameter slots, and ground result `int`. Each explicit
slot is exactly one of:

- `int` with Value entry;
- `()` with Value entry;
- explicitly annotated `[_] int` with Computation entry.

An eligible implementation has exactly one receiver binder and the same
number of explicit binders. Its receiver and explicit endpoint evidence must
be ordinary inferred or ordinary-annotation evidence. Under charter §21,
each executable binder's own outer source annotation determines its entry
role: absent or ordinary annotation is Value; explicit outer `[_]` is
Computation. The role signature never annotates a binder. The body result is
checked through the ordinary endpoint evidence and must be `int`.

The pilot excludes zero-explicit-parameter members, polymorphism, unresolved
or non-ground endpoints, `bool`/`str`, other receiver types, Computation
receivers or results, closed/non-wildcard effect rows, higher-order slots,
patterns, implicit parameters, adapters, and field/dot collision rules.
Exclusion means unsupported by this pilot only; it imposes no restriction on
ordinary language inference or future method syntax.

## Three-way judgment

First classify each signature and implementation independently. If either is
outside the supported envelope, return **Unsupported**. Otherwise compare the
supported vectors of slots and result:

```text
Compatible     iff receiver and explicit slot counts agree, each corresponding
                  ground endpoint agrees, each entry role agrees, and result
                  endpoints agree.
Incompatible   iff both sides are supported but at least one compared count,
                  ground endpoint, entry role, or result endpoint differs.
Unsupported    iff either side uses any excluded form above.
```

| Classification | Proposed pilot consequence | It does not mean |
|---|---|---|
| Compatible | Continue to independent ordinary type/effect checking; only after all producer/admission checks may the implementation become executable | that a role call is already implemented or that endpoint checking is discharged |
| Incompatible | Reject this implementation for this role before executable member admission; retain both declaration and binder anchors | that the whole module's other declarations must be discarded |
| Unsupported | Do not publish an executable target through this provisional pilot; preserve the existing ordinary inference outcome and report no general language error from this judgment alone | that the source program is ill-typed or rejected by the full language |

No signature-to-binder role inheritance, implicit conversion, adapter insertion,
permission-as-effect-cap interpretation or role-specific Call semantics is
part of this definition. An adapter would be a separate declaration and
decision.

## Classification examples

Assume the ordinary type evidence shows each implementation body returns
`int`.

| Role member signature | Executable binders | Classification | Reason |
|---|---|---|---|
| `int -> int -> int` | `self`, `selected` | Compatible | receiver and one Value `int` parameter agree |
| `int -> [_] int -> int` | `self`, `(action:[_] int)` | Compatible | explicit Computation parameter agrees |
| `int -> [_] int -> int` | `self`, unannotated `action` | Incompatible | executable `action` is Value under §21 |
| `int -> int -> int` | `self`, `(action:[_] int)` | Incompatible | Value/Computation roles differ |
| `int -> int -> int` | `self`, `selected`, `extra` | Incompatible | both shapes are supported but arity differs |
| `int -> int -> int` | `self`, `selected:()` | Incompatible | supported ground endpoints differ |
| `int -> bool -> int` | matching `self`, `selected:bool` | Unsupported | Boolean parameter is outside this pilot, not a general rejection |
| `int -> {io} int -> int` | matching closed-row binder | Unsupported | closed-row Computation is outside this pilot |
| `[_] int -> int -> int` | `(self:[_] int)`, `selected` | Unsupported | Computation receiver is outside this pilot |

An explicit ordinary annotation can supply the endpoint evidence only as the
existing ordinary inference rules allow. It does not change the slot role
except through the existing §21 outer annotation rule. When ordinary inference
cannot establish a ground endpoint or a complete result, the declaration is
Unsupported for this compatibility pilot; no special type solver is introduced.

## Preserved effect boundary

This definition selects no effect permission, handler order, request matching,
continuation, residual or storage semantics. Its only effect-related role fact
is the existing §21 distinction between Value and explicitly retained
Computation binders. A qualified role call must still use ordinary Call/Apply
and preserve its first unanswered request and suspended suffix. R82's proof
must reference this exact definition by hash; no wider role domain is implied.

General `receiver.member(args)` method selection and callable-field collision
remain OPEN. The explicit pilot path is `Role::member receiver args`.
