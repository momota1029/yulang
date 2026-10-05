# Inferred Function call views and annotation-scoped protection

Status: Authoritative
Scope: Source formation of role-indexed Function call views, provisional Handler treatment of unannotated higher-order formals, and annotation-dependent effect protection
Approved-by: user, through integrated `function-call-view-formation/q1` answer `a2` (`61a3651376166346a5baa03ec6679c310b0edbdb`)
Approved-at: 2026-10-05
Drafted-by: primary
Reviewed-by: `spec_auditor` (pre-write scope audit and closure conformance review; no findings)
Supersedes: none; narrows the open formation obligation in callback-context delivery §2 without changing its B contract

This document makes authoritative only the user-approved direction and scope
limits recorded below. It does not supply completed typing or inference rules.
Production implementation remains gated by the proof and
production-conformance obligations below.

## 1. Authority and retained decisions

The source decision is the exact approved answer in
[`function-call-view-formation`](../../questions/2026-10-05-function-call-view-formation/approved-answer.md).
It selects inference from declarations, definitions, uses, and any relevant
recursive component. It does not select detailed constraint-generation rules,
a solver algorithm, or implementation.

The governing callback contract remains
[`callback-context delivery`](2026-10-03-callback-context-delivery.md):
callback-literal B is normative. A known expected context selects Handler
introduction and its boundary before the literal body is elaborated; parameter,
body, and result endpoints are generated independently; the completed
interface is checked by one `F_lit <: F_cb`. Any early propagation or
constraint scheduling must be proved B-equivalent, including acceptance,
principal solutions, method/adapter choices, and residual/evidence behavior.
An existing Pure callable value keeps its actual role and entry when viewed at
a callback slot. No rule here rewrites an actual value's role.

The approved production denotation basis Option A and membership Option 2,
approved annotation-boundary behavior, and all other recorded user decisions
remain in force. This document supplies no production-only membership rule and
does not identify production membership with a source-generated reference
relation.

## 2. Source formation direction

The relevant source declarations, definitions, uses, and recursive component
form one shared role-indexed callback contract. Explicit annotations contribute
constraints when present; an annotation is not a prerequisite for forming the
contract. Generalization and use-time instantiation preserve the shared
relationship selected by the source component.

The source position and its contract form a stable static slot identity
`beta` and the corresponding `Slots(beta)` inventory. Position identity,
annotation presence, and lexical scope survive inference, generalization,
instantiation, and evidence transport. A static slot/profile and a dynamically
activated receiver boundary are different objects.

Typed paths, `Flow`, ownership, and receiver relations come from source
resolution and typed elaboration of names, captures, argument receipt, and
calls. Type shape or success of the pending Function comparison cannot create
one of these relations. The original `nu,K,D` constraints come from the same
relevant source component and remain one jointly scoped assignment; independently
chosen port witnesses cannot be combined to invent a call view.

Complete Function admission remains independent of the pending comparison
`Q`. `Q` cannot create a slot, path, receipt, receiver, protection fact, or
authority. These requirements state the selected source-generation direction;
the exact judgments that construct and preserve each object remain open.

## 3. Unannotated higher-order formal `f`

For the source shape `apply f x = f x`, inference internally treats unannotated
`f` as a Handler Function returning fully handler-protected effects. When the
body supplies ordinary value `x` to `f`, that value evidence determines during
inference that `f` is not a Handler in this inferred formal/use relationship.
This determination must be connected to the provisional protected Handler
view by the eventual inference rules.

This is not inferred by supplying a concrete Pure function value for `f`. It
does not change the actual role or entry of a callable value that is later
passed to `f`, and it does not revise callback-literal B. “Fully protected”
does not mean that the effect row is empty. The approved direction does not
yet define the provisional-view judgment, the ordinary-value role-resolution
judgment, their ordering, or the proof that both use one shared inferred
interface. This approved example does not select a generic rule that every
Function receiving a Value-entry argument is Pure or non-Handler; the
resolution must be scoped to the inferred formal/use evidence while preserving
the actual role and entry of supplied callables.

## 4. Annotation-dependent effect protection

Full protection in the unannotated case is caused by the absence of an
annotation; it is not an empty-effect assumption. In
`apply(f: _ -> [io] _, x) = f x`, the annotation permits `io` to be removed
from `f`. This is permission, not a claim that this definition necessarily
performs the removal. It permits removal of the specified `io` contribution;
it does not permit removing unrelated effects.

The rule that ties an annotation occurrence and its local evidence to the
particular protected effect contribution, and the conditions under which the
permitted removal is realized, remain to be specified. Existing annotation
boundary rules still require a direct current-endpoint comparison at each
actual source boundary, export the target with its local realization evidence,
and retain prior evidence. This section does not turn an annotation into a
general row-subtraction operation.

## 5. Required proof and implementation gates

Before this direction can authorize an inference implementation, the next
design and proof work must provide:

1. A source constraint-generation judgment over the relevant declaration/use
   component that constructs `F_cb`, `beta`, `Slots(beta)`, role and entry
   relationships, typed paths/`Flow`, owner/receiver incidences, and the
   correlated original `nu,K,D` without using `Q` success to form them.
2. The exact two-stage inference rule for this unannotated higher-order
   formal/use pattern: provisional fully protected Handler treatment followed
   by determination from ordinary-value evidence, preserving actual callable
   roles and the one shared interface. It must not become a generic
   Value-entry-implies-Pure rule.
3. The exact annotation-presence/protection rule that implements the approved
   `io` permission, identifies which contribution it governs, retains all
   unrelated effects and evidence, and distinguishes permission from actual
   removal.
4. The required uniqueness or principality result for completed contracts and
   profiles, together with source identity, scope, and generalization/use
   preservation proofs.
5. Source adequacy for the stated envelope and separate production
   conformance: exhaustive comparison-independent membership/admission over
   the approved Option A/Option 2 basis, `D_C(xi) subseteq D_A(xi)`, and
   `forall c in D_C(xi). P_A(c;xi) subseteq P_C(c;xi)`, including
   production-only members.
6. B-equivalence for every proposed scheduling optimization and operational
   evidence preservation at the relevant call and annotation boundaries.

Existing Theorem C and source-contract results remain conditional on already
decorated contexts and their stated formation, typing, admission, and transport
hypotheses. They do not discharge these source-generation or production gates.
No solver algorithm, new carrier, grammar change, test expectation, or
production implementation is selected here.
