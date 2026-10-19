# R84 role-call compatibility judgment

Date: 2026-10-19  
Status: Draft; proposed pilot judgment, not adopted semantics  
Sprint: `effect-hygiene-runnable-role-slice-20261019-r84`, revision 1  
Contract SHA-256:
`fd6de85efe1926696f3a45894aa1e3a8a612b31d257bb71b339cc7c79d7c2f48`  
Baseline: `af3ccf2d63ba7f87e0359e183568db548ea53307`

This file is the single normative classifier for R84. The adoption offer, proof
and every example must use its ordered cases without adding a second priority
rule.

## 1. Pilot domain

The first proposed call is:

```yu
role SecondInt { my second: int -> int -> int }
impl int: SecondInt { my second self selected = selected }
my answer = SecondInt::second 1 2
```

The source form is `Role::member receiver args`; `Role::member` supplies the
selected member identity and the receiver is the first ordinary Call stage.
The proposed value is `2`, conditional on the future implementation path in
the adoption offer. General dot dispatch, field/method precedence and callable
field collisions are outside this pilot.

The supported signature envelope is a module-local monomorphic role member
with a ground `int` Value receiver, at least one explicit parameter, an
ordinary ground `int` result, and parameter slots from:

- ground `int` with Value entry;
- unit `()` with Value entry;
- explicit `[_] int` with Computation entry.

The source-signature predicate is:

```text
SigEligible(s) iff s is module-local and monomorphic,
  its receiver is int/Value,
  it has at least one explicit slot,
  each slot is int/Value, ()/Value, or [_] int/Computation,
  and its result is int.
```

`ImplEligible(i)` is independent of a signature. It holds iff the implementation
declaration is module-local and monomorphic, has one receiver binder, at least
one explicit binder, uses simple identifier binders with only unannotated,
ordinary value-annotation, or outer `[_]` annotation forms, and has no adapter,
parameter pattern, or higher-order slot. This is a source-form predicate; it
does not compare counts, infer endpoint types, inspect a body result, or consult
a signature. The source annotations determine §21 entry roles directly.

Other receivers, signature result types, slots, closed rows, endpoint types,
unsupported annotations, polymorphism, higher-order slots, adapters and
patterns are outside this pilot. `Unsupported` means “not covered by this
pilot.” It does not reject the language program or change ordinary typing.

## 2. Endpoint evidence and one decision procedure

Once both independent source-form predicates pass, ordinary inference supplies
the complete signature/implementation endpoint inventory. It includes the
receiver and every explicit formal (including unmatched extra binders). The
signature result is constrained to `int` by `SigEligible`. For implementation
formals the inventory uses the binder's own annotation or ordinary inferred
endpoint. The implementation body result is not part of this classifier;
ordinary body/result checking remains a separate obligation.

Each endpoint in each complete inventory receives exactly one evidence tag:

- `Supported(t)`: ordinary evidence establishes a known pilot endpoint type
  `t` from `{int, ()}`; Computation entry additionally requires the exact
  `[_] int` annotation form;
- `Outside(t)`: evidence establishes a type or form outside the pilot;
- `Unknown`: ordinary evidence does not establish the endpoint.

Let `CompleteSupported(s,i)` mean that every endpoint in both complete
inventories is tagged `Supported`, including unmatched entries. Let
`VectorsEqual(s,i)` compare the full explicit-parameter count, supported
receiver and parameter types, and the §21 entry role of each slot. The
signature result is already fixed to `int`; checking the implementation body's
result remains separate. The judgment is:

```text
if !SigEligible(s) or !ImplEligible(i):
    Unsupported
else if some endpoint in either complete inventory is Outside or Unknown:
    Unsupported
else if !VectorsEqual(s, i):
    Incompatible
else:
    Compatible
```

This order is normative. The complete-inventory guard precedes every paired
mismatch check, so an outside or unknown endpoint dominates a simultaneous
arity or role mismatch. In particular, an extra `bool` binder is
`Unsupported`, while an extra supported `int` binder is `Incompatible`.

## 3. Totality, disjointness and consequences

For a finite declaration pair, both source-form predicates are decidable. If
either is false, exactly the first outcome applies. Otherwise the finite
endpoint inventory either contains an `Outside`/`Unknown` tag or it does not.
Exactly one of those branches applies. For an entirely supported inventory,
vector equality is decidable; exactly one of equality or mismatch applies.
Because the cases are ordered and exhaustive, every input receives exactly one
result:

| Result | Proposed pilot consequence |
|---|---|
| `Compatible` | Continue to ordinary body/result/effect checks and separate source identity, validation, materialization and admission gates. It does not establish them. |
| `Incompatible` | The declarations are entirely within the pilot, but supported arity/type/§21 role vectors differ; do not admit this implementation for the role through this pilot. |
| `Unsupported` | Do not publish a target through this pilot; preserve ordinary language inference and make no general rejection claim. |

`Compatible` does not prove body typing, selected source-member identity,
candidate admission, runtime support, producer hypotheses P1–P4 or any parent
Simple-sub/A-B claim. There is no implicit adapter and no signature-to-binder
role inheritance.

## 4. Discriminating case table

| Signature | Implementation | Outcome | Decision path |
|---|---|---|---|
| `int -> int -> int` | `self, selected:int` | Compatible | all endpoints supported; exact Value/int vectors |
| `int -> int -> int` | `self, selected:int, extra:int` | Incompatible | complete inventory supported; arity differs |
| `int -> int -> int` | `self, selected:int, extra:bool` | Unsupported | complete-inventory guard sees outside endpoint before arity |
| `int -> int -> int` | `self, selected:()` | Incompatible | both endpoint types are supported; paired types differ |
| `int -> [_] int -> int` | `self, action:[_] int` | Compatible | exact Computation role and supported endpoint |
| `int -> [_] int -> int` | `self, action:int` or unannotated `action` | Incompatible | all endpoints supported; §21 role differs |
| `int -> int -> int` | `self, action:[_] int` | Incompatible | all endpoints supported; §21 role differs |
| `int -> [_] int -> int` | `self, action:[_] bool` | Unsupported | outside endpoint dominates the role comparison |
| `int -> [_] int -> int` | `self, action` with unknown inferred type | Unsupported | endpoint evidence is unknown |
| `bool -> int -> int` | any otherwise matching declaration | Unsupported | signature receiver is outside the pilot |
| `int -> int -> bool` | any otherwise matching declaration | Unsupported | signature result is outside the pilot |
| eligible declaration pair with an ill-typed body result | ordinary implementation body | Classifier may be Compatible; ordinary body/result checking fails separately | body result is not classifier evidence |
| implementation uses a parameter pattern | any eligible signature | Unsupported | implementation source-form predicate fails |

The mixed-failure rows are mandatory regression cases for the written
judgment, proof and adoption decision. They fix the priority explicitly.

## 5. Role preservation boundary

Charter §21 fixes each executable binder's role from its own outer source
annotation: unannotated or ordinary value annotations enter as Value; explicit
outer `[_]` enters as Computation. The signature does not rewrite the binder.
For `Compatible`, the vectors are equal, and the relation only compares them;
therefore every implementation binder retains its §21 role. This finite
comparison establishes no complete source-to-runtime preservation theorem.

## 6. Effect-hygiene scope boundary

This judgment introduces no handler-selection, permission, continuation,
residual, storage or dot-method rule. R84 maps the six hygiene frontiers and
their present evidence/owners/falsifiers separately. The conditional R81
ordinary-Apply prefix result is reusable only under P1–P4; those premises,
source-to-native correspondence, full continuation preservation, protected
sibling coverage and original A/B remain open.
