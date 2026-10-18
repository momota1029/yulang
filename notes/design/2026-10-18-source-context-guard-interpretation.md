# Candidate interpretation: source-context guards

Status: Draft, R30 research interpretation; not production-authoritative.
Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains
OPEN/closure0. The original parametric theorems, source domain and quantifiers
are unchanged. This document defines one candidate interpretation instance;
it does not claim equality with an unavailable record definition for `j0/a0`.

## 1. Why an interpretation is needed

R29 traced original `j0` and `a0` to independently supplied guard schemas.
The immutable-root definition describes their categories, while the scalar
import construction names them as premises. Neither supplies a complete
dependent telescope, projection equations, or an action on old global
predicates under insertion. The selected contextual function definition
likewise leaves complete source-context/admission relations as independent
inputs. There is no original guard constructor to apply to parsed source.

The user authorized trying research interpretations and reverting candidates
that fail. R30 selects one source-semantic *instance* of these parameterized
schemas for a bounded attempt. The original theorem stays parametric in its
independent guard interpretations; it is not silently rewritten to this
instance. A theorem about the instance applies to the original parent only if
an explicit adequacy map proves that it inhabits each original premise at the
same tuple and for every originally quantified predecessor.

## 2. Candidate dependent signatures

Fix the original source module `M`, caller predecessor `P`, joint assignment
`theta0`, `xi=(nu,K,D)`, `C0,w0,e0`, and `e0=(eta0,h0)`. No field below may
move to a fresh index or replace a source identity with equal spelling. Define
candidate records:

```text
Jsrc(C0,w0,e0;xi) = {
  registry : ResolvedRegistry(P,M;xi),
  scope    : ResolvedScope(P,M,theta0;xi),
  authority_known : SourceVisibleCurrent(P,M,e0;xi),
  incidence_known : ExactTypedIncidence(P,M,C0,e0;xi),
  old_frame : DependentOldFrame(P,w0,W0;C0,e0,xi),
  authority_residual : JAuthResidual(C0,w0,e0;xi),
  incidence_residual : JIncResidual(C0,w0,e0;xi),
  global_residual : JGlobalResidual(C0,w0,e0;xi)
}

Asrc(w0,e0;xi) = {
  alias_projection : OneThetaProjection(M,theta0;xi),
  capture_projection : ResolvedCaptureProjection(P,M,theta0;xi),
  shared_equalities : SameWitnessAtOriginalScopes(P,M,theta0,e0;xi),
  overlap_frame : DependentOverlapFrame(P,M,W0;theta0,e0,xi),
  alias_residual : AAliasResidual(w0,e0;xi),
  capture_residual : ACaptureResidual(w0,e0;xi),
  shared_residual : ASharedResidual(w0,e0;xi)
}
```

The `*_residual` fields are intentional, typed placeholders for original
requirements whose complete field inventory and dependency maps have not been
found. They are not Booleans, success receipts, source facts, or consequences
of the known fields. The candidate schemas mean the full conjunction of
known fields **and** these residuals. No introduction rule may omit them.
Until an independent owner defines and supplies every residual, neither
`Jsrc` nor `Asrc` inhabits original `j0/a0`.

This separates an *enumerated local relation* from a claim that it exhausts
the original parametric predicate. In particular, the record does not define
`j0` to mean its first four fields. The old guard names remain independent
arguments in existing theorems.

## 3. Field meanings and constructors

### Registry and scope

`ResolvedRegistry(P,M;xi)` contains the predecessor's exact old root/member
identities and dependencies plus only resolved module/declaration/member IDs
from the selected source derivation. `ResolvedScope` contains the original
binder tree, lexical/import edges and actual shared binder identities under
the one `theta0`. Construction is source-directed; string equality, generated
IDs, or visible signatures alone are insufficient. It retains old/private
fields at their original binder scopes.

Projection laws for these structural fields are:

```text
restrict_registry(embed_registry(x)) = x
restrict_scope(embed_scope(x))       = x
```

These equations establish identity preservation only. They do not prove
preservation of authority, incidence, any global predicate, or `a0`.

### Authority and incidence

`SourceVisibleCurrent` records the exact parsed source occurrence, its
resolved declaration/member identity, visibility derivation and an
independent witness that the corresponding owner is current at the original
`e0`. Static `PortProv` is retained as source provenance, not interpreted as
current authority. R29 found no exhaustive original `CurrentAuthority` field
definition, so `JAuthResidual` remains required.

For every member of the original incidence index family (the family itself
must come from its original owner), `ExactTypedIncidence` requires:

```text
Path(q,owner(h),b,p)
  Active(h,C0) ∧ Active(owner(h),C0) ∧ Active(b.receiver,C0)
```

The `Path` witness is the existing typed-boundary relation: a matching
profile position and typed-flow route, the original event observation
`Observe(q,v,p0)`, and receipt of that same view by the exact invocation.
Activity is checked separately for the exact handler, owner and original
receiver at this same `C0`. Registration or visibility establishes none of
these facts. `JIncResidual` retains any original incidence requirements not
enumerated by that selected local relation.

`JGlobalResidual` retains every unenumerated interpretation dependency of the
joint schema. A new typed edge can add old-endpoint paths, and a newly current
handler can change global ordered search. Neither fact can be erased by
restricting IDs. If a future definition proves an exact global projection,
that proof may discharge this residual; no such projection is assumed here.

### Aliases, captures and shared witnesses

`OneThetaProjection` maps all aliases of one resolved source binder to its
single original `theta0` witness. `ResolvedCaptureProjection` follows exact
source dependency identities, not same-name members. `SameWitnessAtOriginalScopes`
states semantic and scope equality for every overlap actually established by
the source/predecessor dependency maps. `DependentOverlapFrame` retains old
private/shared witnesses at their original scopes and explains how each
new/old overlap is typed.

The full index family of aliases, captures, overlap scopes and semantic
witness types has not been supplied for original `a0`. The three residuals
must therefore remain. Selecting a convenient finite subset and calling it
exhaustive would strengthen the premise by excluding original cases; merging
two independent witnesses because their keys agree would change its meaning.

### Old-dependent frame

For every predecessor dependent field `x:F(P)`, `DependentOldFrame` must
provide an extension action `extend_F(x):F(W0)` and a scoped restriction with
`restrict_F(extend_F(x)) = x`. For every original predicate `Q` interpreted
over the complete registry/context, it must separately prove:

```text
Q(P) iff Q(W0) on the embedded old coordinates.
```

This is required for all original admissible `P`, at unchanged `xi,e0`,
including old/private/shared fields. It is not derived from key retraction.
The R29 audit found no exhaustive field family or global-predicate action;
until one is supplied, `DependentOldFrame` and `JGlobalResidual` remain
uninhabited by this source constructor.

## 4. Candidate pure context action and adequacy target

The candidate action reuses the caller's actual predecessor tuple rather than
inventing a runtime event. Let

```text
P = (C_P,w_P,e_P;xi, OldFields_P)
```

be the caller-owned context at the original index. `M` supplies the resolved
source root/declaration/member identities and its one joint `theta0`. Let
`ResolvedRoots(M)` be the exact registration/scope fragment produced by the
resolved source derivation. Subject to a source-identity-preserving merge (no
ID capture or same-name substitution), define the *structural* action:

```text
W0 := Extend(P, ResolvedRoots(M), theta0)
C0 := C_P
e0 := e_P
xi := xi_P
```

`Extend` inserts the resolved registrations and lexical edges and retains
every old structural coordinate. It does not execute source, activate a
declaration, construct a new `Path`, change a handler, or alter `K,D`. Thus
the event correspondence is by projection from the caller's predecessor;
it is not supplied by `ModuleRun`. The original application requires the
caller to provide `P` at the exact fixed `(C0,w0,e0;xi)` and the action to
produce the theorem's exact `w0=W0`. This is only a structural construction;
it does not establish that an original guard holds at the result.

The action consumes only independently resolved source structure, the
authentic predecessor and its actual dependent evidence:

```text
ResolvedModule(M)   AuthenticPredecessor(P;C_P,w_P,e_P,xi)   JointTheta(M,theta0)
IdentityPreservingMerge(P,ResolvedRoots(M),theta0)
-------------------------------------------------------------------------
W0=Extend(P,ResolvedRoots(M),theta0), C0=C_P, w0=W0, e0=e_P, xi=xi_P
```

It evaluates no expression or effect and adds no callback or source step.
The displayed merge rule is a new research interpretation, not a renamed
`ModuleRun`. Its structural merge has not yet been shown compatible with every
old semantic dependency. In particular, an old global predicate is
re-evaluated on `W0`; it does not follow from its truth at `P`. Any witnesses
for `JAuthResidual`, `JIncResidual`, `JGlobalResidual`, `AAliasResidual`,
`ACaptureResidual`, `ASharedResidual`, and semantic `OldFieldActions` must be
independently supplied at `W0` or derived by a later field-specific theorem.
The caller payload cannot certify itself. If any residual lacks a valid
constructor under the original semantics, the candidate action does not
produce `j0/a0`.

Even if the action constructs the known registry/scope/path/shared
projections, missing residuals block the original `j0/a0` application. It
cannot conclude full `PhiW` without every installed binding's same-root
`Z.V` or designated `Z.Car` certificate, nor can it construct the fixed-`c`
`DeclContribution`/Operation license.

The adequacy theorem to attempt is:

```text
For every predecessor and source/context tuple admitted by the original
parent premises, the candidate action returns that same tuple and its
Jsrc/Asrc readouts inhabit the original independent j0/a0 parameters.
```

No source-domain or predecessor restriction is part of this statement. If
the candidate only applies under an additional condition, present that
condition as an explicit residual and count no parent progress. A source-
qualified counterexample must satisfy every original parent premise; failure
to construct this particular action alone is not such a counterexample.

## 5. Guardrails and decision boundary

- Keep the existing theorems parametric in independent guard meanings. This
  candidate is one separate interpretation instance, not a retroactive
  equality to an unavailable original guard record.
- Never assume `j0/a0`, `PhiW`, `JointWF`, `OriginalInitial`, a validity flag,
  or the license in the source action's premises.
- Retain old/private/shared fields and every unresolved global dependency as
  residual fields. No field can disappear to obtain a proof.
- Keep current authority separate from static source visibility and exact
  incidence separate from `Path` existence.
- Keep same-root recursive certificates and fixed-`c` license independent.
- No production behavior, source syntax, evaluation order, test expectation,
  API or implementation is selected by this note. A later implementation
  needs a separate exact design authority and reviewed gate.

## 6. Governing evidence

- `notes/theory/2026-10-08-simultaneous-immutable-root-introduction.md`, §3
  (`PhiW`, inert root registration and immediate guard requirements).
- `notes/progress/2026-10-10-initworld-phiw-import-construct.md`, scalar
  instance and exact restriction limit.
- `notes/design/2026-10-08-contextual-function-membership-definition.md`,
  §§1–4 (complete source-context relations remain independent inputs).
- `notes/theory/2026-10-08-call-semantic-input-realization.md`, §§2–4.1
  (original `C0,w0,e0,xi` and independent event/history inputs).
- `notes/design/2026-10-02-typed-boundary-realization-draft.md`, §6
  (exact typed path and current activity relations).
- `notes/design/2026-10-02-typed-source-owner-realization.md`, §§1–4
  (preservation starts from a related decorated state).
- `notes/design/2026-10-05-source-contracts-and-common-allowance.md`, §3.7
  (hard-envelope dependencies).
- `notes/design/2026-10-08-source-generalize-definition.md`, §2
  (allocation, evidence scope and provenance distinctions).
- R29 definition-owner obstruction:
  `notes/theory/2026-10-18-caller-source-context-action-construction.md`.
- R29 native correspondence:
  `notes/design/2026-10-18-caller-source-context-native-correspondence.md`.

Original independent guard authorship/meaning remains whatever the adopted
parent sources specify; absent projections are deliberately left unresolved.
