# R83 bounded role/member eligibility and compatibility

Date: 2026-10-19  
Status: Draft; proposed pilot judgment, not adopted semantics  
Sprint: `effect-hygiene-role-call-20261019-r83`, revision 1  
Contract SHA-256: `68fdfda6599d3b894482d4ef447e2940802c64ef97573a602b63abf003ff648b`  
Baseline: `af3ccf2d63ba7f87e0359e183568db548ea53307`  
Supersedes: none

This is the single R83 compatibility definition. Adoption examples, proof
premises, outcome labels and user questions must cite this exact byte hash and
use the same classification.

## 1. Signature eligibility

`SigEligible(s)` holds exactly when one role member signature is:

- monomorphic and module-local;
- one Value receiver slot with ground endpoint `int`;
- at least one explicit parameter slot, each exactly `int` Value, unit `()`
  Value, or explicitly annotated `[_] int` Computation;
- ordinary ground result `int`.

Its slot count is recorded as signature data. `SigEligible` does **not** inspect
an implementation and does not require its count to match any implementation.
Other types, closed rows, polymorphism, higher-order slots and Computation
receiver/result are Unsupported by this pilot.

## 2. Implementation eligibility

`ImplEligible(i)` holds exactly when one implementation member independently
has:

- one receiver binder with an unannotated or ordinary value annotation form;
- one or more explicit binders, each independently using an unannotated or
  ordinary value annotation form, or an explicit outer `[_]` annotation;
- no polymorphic member, parameter pattern, higher-order slot, adapter or
  unsupported effect annotation.

The number of implementation explicit binders is checked only to be at least
one. `ImplEligible` does **not** inspect a role signature and does not require
matching arity. It checks declaration/binder form only: endpoint evidence and
body result come from the ordinary inference/checking path used in pair
comparison. Roles come from the binders' own source annotations; no role or
type is inherited from a signature.

## 3. Pair classification

For every pair `(s,i)`, compare the finite §21 role vectors directly from the
signature slot forms and implementation binder annotations. Ordinary checking
provides bounded endpoint evidence for the implementation against the
signature. This packet introduces no alternate endpoint solver. Its evidence
classification is `EqualSupported` (all endpoints are established within the
pilot and agree), `DifferentSupported` (all compared endpoints are established
within the pilot but at least one differs), or `OutsideOrUnknown` (an endpoint
is out of the pilot or ordinary checking cannot establish it). Then classify
the pair in this order:

```text
if !SigEligible(s) or !ImplEligible(i):
    Unsupported
else if explicit slot count differs:
    Incompatible
else if §21 role vectors differ:
    Incompatible
else if endpoint evidence is DifferentSupported:
    Incompatible
else if endpoint evidence is OutsideOrUnknown:
    Unsupported
else:
    Compatible
```

The outcomes are total and disjoint: independent form eligibility is decidable
for the bounded syntax, role equality is decidable from the finite source
annotations, and endpoint evidence is one of the three stated cases. Arity
compares signature and implementation counts only after both forms
independently qualify. Thus an extra supported binder cannot make the
implementation Unsupported.

| Outcome | Proposed pilot consequence | Scope limit |
|---|---|---|
| Compatible | Proceed to ordinary Call/type/effect checks and the separate declaration/materialization/admission gates | Does not establish an executable target, body conformance, candidate admission or runtime support |
| Incompatible | Reject this implementation for this role before executable member admission, preserving both source anchors | Applies only when both sides are independently supported |
| Unsupported | Do not publish a target through this provisional pilot; retain the ordinary language inference result and issue no general rejection from this judgment alone | Unsupported is not Incompatible and not an ill-typedness claim |

Thus an extra or missing binder of an otherwise source-form-eligible
implementation is Incompatible. A binder with an excluded annotation form, or
ordinary endpoint evidence outside the supported set, makes the pair
Unsupported. An unannotated binder remains eligible as Value while its
endpoint is determined by ordinary inference. No implicit adapter or
signature-to-binder role inheritance exists in this pilot.

## 4. Finite case table

Rows requiring endpoint comparison assume the listed outcome of ordinary
inference evidence. The relation does not provide that evidence.

| Signature | Implementation | Outcome | Reason |
|---|---|---|---|
| `int -> int -> int` | `self, selected` with ordinary int endpoints | Compatible | one supported Value/int parameter and result agree |
| `int -> int -> int` | `self, selected, extra`, each supported Value/int | Incompatible | independently eligible vectors differ in arity |
| `int -> int -> int` | `self, selected:()` with both types otherwise supported | Incompatible | paired supported endpoint differs |
| `int -> [_] int -> int` | `self, action:[_] int` | Compatible | explicit Computation role and endpoint agree |
| `int -> [_] int -> int` | `self, action` where action is unannotated | Incompatible | the implementation is independently eligible as Value, but role differs |
| `int -> int -> int` | `self, action:[_] int` | Incompatible | the implementation is independently eligible as Computation, but role differs |
| `int -> bool -> int` | matching bool parameter implementation | Unsupported | signature and implementation use a form outside this pilot |
| `int -> {io} int -> int` | matching closed-row formal | Unsupported | closed-row Computation is outside this pilot |
| `[_] int -> int -> int` | Computation receiver implementation | Unsupported | Computation receiver is outside this pilot |
| `int -> int -> bool` | implementation whose ordinary body result is bool | Unsupported | signature or implementation result is outside the ground-int envelope |

Each binder's role remains the one determined by its own source annotation
under charter §21. The Compatible case preserves that role because pairwise
comparison requires exact equality and neither relation rewrites the source
binder. Incompatible classifications reject before that implementation
becomes an executable member; Unsupported leaves general source typing
untouched.

## 5. Boundaries

This judgment introduces no permission, effect cap, operation lookup, handler,
continuation, residual, storage or method-dot rule. It does not change ordinary
Simple-sub generation/propagation or body inference. Exact selected-member
identity, authentic executable member root/environment, complete candidate
admission and runtime transport remain separate producer obligations P1–P4
from the conditional R81 proof. General `receiver.member(args)` and callable
field collisions remain OPEN and outside the pilot.
