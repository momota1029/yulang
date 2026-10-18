# Research proposal: caller-owned module initialization transition

Status: Draft, R28 revision 2; not adopted and not production-authoritative.
Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains
OPEN/closure0 with its original domain and quantifiers. This proposal tests the
user-selected caller-initializer route; it discharges zero parent conditions.
It changes no compiler or language behavior.

## Decision target

The approved L4 decision assigns the *complete authentic initial context* to
the compilation caller. It deliberately leaves initialization, reuse,
invalidation and validation semantics open. The selected route now asks
whether a source-owned initialization action can construct the original
`j0/a0` fields from that owner without taking those fields as assumptions.

The unchanged target is the original formation of
`ctrl.choose : Unit -> alpha+` at `(C0,w0,e0;xi)`, with
`xi=(nu,K,D)`, `e0=(eta0,h0)`, and `ins_(r0,q0)`. The original `PhiW`, its
`JointRegistryScopeCurrentAuthorityIncidence` component `j0`, and its
`AliasCaptureAndSharedWitnessAgreement` component `a0` retain their exact
meanings. `DeclContribution` and the fixed-`c` operation license remain a
separate unmet premise. No domain or quantifier is narrowed.

## Three routes and their present status

| Route | Rule shape | What the evidence permits now |
| --- | --- | --- |
| L4 caller continues to supply the complete context | `caller supplies P` with all original judgments and dependencies | This is the approved owner choice. It is not a derivation of those judgments from parsed source, and the selected playground caller does not currently supply `P`. |
| Add a caller-owned initialization action | `M, P, source action -> (C0,W0,e0)` with explicit introductions and dependent extension | This is the route selected for this research attempt. It is a new semantic rule and needs exact policy, proof and user adoption before implementation. Existing `RuntimeProgram::start` is not this rule. |
| Keep the original example structural and open | retain `Sigma0, theta0, Op0, PortProv, j_decl` and stop before the original guard application | This is the only conclusion currently derived for the selected source. It preserves the original theorem but does not advance its guard obligation. |

The second route is worth trying because it gives a concrete owner and event
whose constructors can be compared with the original guard fields. It is not
yet known to be realizable for every context in the original quantifier.

## Candidate rule: source-context action, not source execution

The proposal is to introduce a source/host transition with a named issuer and
an exact result tuple:

```text
M      : resolved, typed source module, including the original source
         occurrence IDs, declaration/member IDs, binder tree, visibility and
         joint theta0; no reconstruction from spelling or equal keys
P      : caller-owned predecessor at xi, with its complete interpretation,
         dependencies, histories, old witnesses and old source identities
init(M,P,xi) : actual host action that forms this module's initial semantic
               context; it does not evaluate source expressions or run effects

CallerInit(M,P,init,xi) -> (C0,W0,w0,e0;xi, initialization derivation I0)
```

`init` denotes a pure context-forming action by the compilation caller, with a
source/native trace to the selected resolved module and its occurrence IDs.
It must not evaluate module expressions: inference constructs source
constraints and performs Simple-sub propagation without first executing
expressions or effects. The action's result is required to be the `C0,w0,e0`
of the original theorem at the identical `xi`; this correspondence is a
theorem obligation, not a name-based convention. Compile-only registration,
HIR construction, `ModuleRun` allocation, a later callback, or opaque caller
payload cannot instantiate `init` by itself. No existing source/native caller
currently supplies this transition.

This is a proposed new rule, not an assertion that current language semantics
already has such an action. The concrete policy decision is: **the caller may
form the initial semantic context from the exact resolved source module and
authentic predecessor before inference, and that context is the theorem's
`C0,w0,e0`.** It adds no source evaluation, callback, force, or extra source
operation. Whether this pure source-context action can supply the original
event-current fields is unverified. Runtime module entry cannot substitute;
that would be a different, evaluation-based rule and would conflict with the
approved inference principles.

The rule is not permitted to take `j0`, `a0`, `PhiW`, `JointWF`,
`OriginalInitial`, a valid-world flag, or a target license as input. Its
immediate target in this research packet is only the original `j0` and `a0`
projections, separately constructed under the unchanged definitions:

```text
Resolved(M)   Authentic(P,xi)   SourceContextInit(M,P,init,C0,w0,e0,xi)
FieldIntro(M,P,init,theta0)    DependentExtend(P,W0,xi)
----------------------------------------------------------------
(j0(C0,w0,e0;xi), a0(w0,e0;xi))
```

The upper-line predicates are not assumed names for the desired conclusion:
each must be defined by independent source/host evidence below. If
`FieldIntro` or `DependentExtend` merely restates `j0/a0`, the rule is
circular and rejected. This conclusion does **not** establish full `PhiW`:
every installed binding still needs its same-root `Z.V` or designated
`Z.Car` certificate. Those recursive certificates, postfixedness, and
`JointWF` remain separate original obligations and no complete bootstrap
application follows from `j0/a0` alone.

## Required independent introductions

1. **Issuer and source action.** The host action records which compilation
   caller issued it, which exact resolved module derivation it consumes, and
   which predecessor/context version it reads. The action cannot authenticate
   itself by a Boolean. A stale/different parse, module, `xi`, or context
   version fails the rule. It forms context only; it does not evaluate source.
2. **Registry and scope.** Begin with the authentic `P` and add only the
   resolved IDs and lexical/import edges actually present in `M`. Preserve the
   original occurrence identities and binder tree. A string/name match,
   generated ID alone, or visibility edge alone is not a source derivation.
3. **Current authority.** For every original authority field, exhibit its
   exact source reference, resolved declaration, visibility derivation and
   independent host/action evidence that the referenced owner is current at
   `e0`. `PortProv` is static provenance and contributes no current activity.
   Any additional atom in the original current-authority predicate needs its
   own owner and constructor; this list is not presumed exhaustive.
4. **Incidence.** For each incidence required by the original `j0`, construct
   the original typed `Path(q,owner(h),b,p)` including its matching flow,
   event observation and receipt evidence, and separately establish
   `Active(h,C0)`, `Active(owner(h),C0)` and `Active(b.receiver,C0)`.
   Recompute `Inc_C0` from these fields. Registration does not activate a
   declaration or receiver. Add no handler or receiver absent from the actual
   source action.
5. **Aliases and shared witnesses.** Construct one witness for each actual
   joint source binder under the original `theta0`; reuse an old witness only
   when the authentic predecessor dependency map identifies that same
   binder. Prove the original semantic and scope equalities for every new/new
   and old/new overlap. Equal IDs alone do not establish `a0`.
6. **Original license.** Keep `DeclContribution(q0,h,c;Omega,rho_h,d)` and
   the fixed-`c` `PrimLicenseContribution` at their actual constructor owner.
   `CallerInit` neither synthesizes nor weakens them. The frozen operation
   audits currently supply no such `d` or complete license projection.

## Dependent extension and the precise hard case

Let `embed:P -> W0` and `restrict:W0 -> P` be dependent maps that retain all
old identities and their original witnesses. The candidate requires:

```text
restrict o embed = identity_P
for each old field F over P:
    restrict_F(extend_F(F)) = F
for each old predicate Q over the complete registry/context:
    Q(P) iff Q(W0) on the embedded old coordinates
```

The third line is not implied by the first two. The original `PhiW` includes
predicates interpreted over the full registry and incidence graph. Adding a
new typed edge can create a new `Path` between old endpoints; adding a
currently active handler can alter a global ordered search or dependency of an
old certificate. Restriction on IDs cannot erase those new witnesses while
claiming the same global predicate. The transition therefore needs a
field-by-field extension action with a preservation proof for every such
predicate, not a copied record or key retraction.

The reviewed source-owner initialization theorem starts from an already
related/decorated state, adds only actual live owners and boundaries, and
transports old evidence through a fresh-identity map. It may supply part of
the `embed` action after an authentic relation is independently present. It
does not construct `P`, `I0`, `j0`, or the global `Q` equivalence above.

**Feasibility remains unproved.** No exhaustive telescope for the old
dependent fields has been found, and no extension theorem applies to every
originally quantified predecessor. An admissibility condition may describe a
real failure, but rejecting predecessors that satisfy the original parent
premises would narrow its domain and cannot count as proof. If full-registry
preservation is impossible under the existing predicates, the route is
blocked pending an explicit semantic redesign; this proposal does not make
that redesign.

## Observable behavior and falsifiers

The candidate action is source-directed and caller-owned. It adds no
user-visible syntax or operation. It must preserve evaluation/source order,
must not execute declarations merely because they are registered or visible,
and must not retain activity after the actual owner/receiver exits. All
existing original boundary identities and histories remain in force.

Any of these observations falsifies the candidate construction:

- a registered-but-unentered declaration acquires `Inc_C0`;
- a handler, owner, or receiver absent/inactive in the same `C0` supplies an
  incidence witness;
- a path without the original typed flow, event observation and receipt is
  accepted;
- a matching name, foreign declaration, stale parse, or different `xi/e0`
  supplies identity or authority;
- a new edge/handler changes any embedded old global predicate while the
  alleged restriction claims identity;
- a private/shared old witness disappears, two independent witnesses are
  merged, or alias agreement is inferred only from equal keys;
- module initialization changes source order, executes an additional
  callback, or fabricates the missing fixed-`c` license.

The original F1/FK1, provider/context/world/source/occurrence/continuation,
whole-Call, future/history and accepted-input quantifiers remain unchanged.
This proposal establishes none of soundness, principality, termination,
Call, `JointWF`, `OriginalInitial`, phase closure or the parent theorem.

## Implementation and proof gate

Current implementation evidence identifies no safe code slice for a
guard-producing adapter: the selected playground path supplies neither
authentic `P` nor the pure source-context transition, and the current runtime
initializer does not correspond to the original `C0,e0,xi`. Even a future
`j0/a0` derivation would leave recursive `PhiW` certificates and the
independent parent license absent.
The previously considered opaque-data transport would preserve bytes but
validate none of the required evidence. No implementation or tests are
authorized by this research proposal.

If adopted later, the first proof packet must provide (i) exhaustive original
dependent field types, (ii) constructors for each original `j0/a0` atom,
(iii) the same-index source/native trace for the pure context action, (iv) the
complete old-field frame theorem for every original predecessor, and (v) the
same-root `Z.V`/`Z.Car` certificate family required by full `PhiW`. A fresh source-owner audit then
identifies the smallest actual compiler path. Runtime tests can falsify
activity/order claims but cannot prove `PhiW` or the frame theorem. The fixed
operation-license proof remains a distinct gate.

## Adoption choices after review

Independent review should answer whether this is a coherent new rule and
identify the smallest exact policy decision. The choices are:

1. **Adopt this explicit source-action policy for a bounded proof attempt.**
   The caller may form the initial context from the resolved source module and
   authentic predecessor without evaluating it; the exact result is
   `C0,w0,e0`. The exhaustive-field and frame proofs remain
   hard gates; this approval alone does not close them or authorize a compiler
   implementation. A failed proof withdraws the rule and restores the
   structural-open result.
2. **Keep L4 caller ownership only.** Require the caller to supply an
   independently authentic complete context under a future reviewed API;
   do not add module-init semantics. The selected executable route stays
   blocked until an actual supplier appears.
3. **Do not adopt either route for this example yet.** Keep the original
   theorem and source candidate open at the structural boundary.

The proposal recommends option 1 only as a bounded attempt because it exposes
the event and predecessor that every further proof must use. Review must not
turn this recommendation into assumed feasibility or production authority.

## Frozen dependency basis

- R28 rev2 contract SHA-256:
  `706879b09e0e71710a461f9ebd433aea7b27e2f305031e043cbc2f78077f2348`
- R28 rev1 source candidate SHA-256:
  `06a924b9ea0b7f987b15b4c4f4509203f3e04c8d03536678794d3e43b2b4c49d`
- R28 rev1 conditional proof SHA-256:
  `50a24c63948efe0c964f45e72c2819b496e5c79461b4d2494124fc97ada12686`
- Approved L4 owner decision: `questions/2026-10-08-l4-initial-jointwf-owner/approved-answer.md`
- Original `PhiW` and parent tuple:
  `notes/theory/2026-10-08-simultaneous-immutable-root-introduction.md`;
  `notes/theory/2026-10-18-caller-module-init-guard-preservation.md`
- Typed path/activity owner:
  `notes/design/2026-10-02-typed-boundary-realization-draft.md`, §6
- Typed source-owner initialization:
  `notes/design/2026-10-02-typed-source-owner-realization.md`, §§1–4
- Frozen fixed-`c` license audits:
  `notes/design/2026-10-18-operation-original-constructor-witness.md`;
  `notes/design/2026-10-18-choose-primitive-license-formation.md`
