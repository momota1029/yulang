# Literal Result incidence naturality remains open

Date: 2026-10-09
Status: bounded conditional research; no source counterexample or authority
Baseline: `eb6032bb0136b3f5a07c2574a202dd850fac4136`
Related candidate: [`Original literal Result owner extension`](../theory/2026-10-09-original-literal-result-owner-extension-candidate.md)
Candidate SHA-256 reviewed: `0c5c58022c6834651fedff6c14d8cdf96002831c0c2d25292843abbae64d3924`

## Result

The candidate's two independent reviews found no blocking, major, or minor
finding within its bounded proposal-only scope. They confirm it is suitable for
a later user decision as a Draft, not that the proposed original registration
rule is selected or that `realizeResult_N` is proved.

A separate read-only naturality investigation found a further proof input
needed even if an authentic original `ResultLiteral` registration is granted:
the selected N and original Return contracts do not, by identity/composition
laws internal to each contract alone, supply a cross-incidence map preserving
the complete witness fibers. Equal erased values and interfaces
(`Return(1)` and `Comp(empty,Int)`) do not identify those fibers.

The bounded discriminator fixes one literal, primitive witness, event,
configuration/world, returned root/provider, assignment and trivial future
indices, while retaining distinct N and original Result incidence keys. Let
the independently supplied complete incidence evidence have two N alternatives
`{l0,l1}` and one original alternative `{m0}`. Both Return fibers are nonempty
and satisfy the same pure Return clause; all retained runtime coordinates are
identical and identity actions satisfy the within-contract laws. There is no
injective one-way map preserving both alternatives into the singleton target,
and therefore no bijection. A many-to-one member map could still exist if the
target contract permits collapsing alternatives, but the approved N boundary
forbids quotienting contract-exposed evidence. This is a conditional interface
discriminator, not a claim that a selected source contract permits these exact
fibers. It fails if the actual Return kernel supplies a complete incidence
reindexing that preserves the exposed alternatives.

## First missing supplier

The next evidence is the independent Return kernel's exact incidence-domain
and reindexing law at this literal Result tuple. A sufficient map has the
shape:

```text
alpha_a : retained N Data/Result tuple -> authentic original tuple
kappa_a = Return_K(alpha_a) : J_a^N -> J_a^orig
forget(kappa_a z) = forget(z)
```

It must commute with the whole dependent action, including transport between
the distinct N and original port keys. Relation equality additionally needs
an inverse and both inverse laws. The q1/d1-preserving bridge requires one-way
lossless transport of each exposed N alternative; it need not be surjective
onto original alternatives. A satisfying Return member may support original
Return introduction, but static registration alone supplies neither that
member nor transport of every N witness alternative.

This is downstream of the candidate's proposed static owner constructor and
upstream of original Reify/Delay, whole-argument checking, emitted membership,
admission and compiler implementation. It does not decide whether to adopt
the proposed constructor. The exact bounded adoption choice is now recorded in
[`question.md`](../../questions/2026-10-09-original-literal-result-owner/question.md).
Even approval would select only the static formation case; it would leave the
Return-kernel domain, witness-map and action-square proof obligations open.

## Authority and implementation crosswalk

The selected original pure Return case is `ReturnMem_A` in
[`call-semantic-input-realization.md`](../theory/2026-10-08-call-semantic-input-realization.md)
§4.2, selected by the Authoritative contextual-function definition §§1,3.
It requires an already licensed original result/provider/root/world
incidence, `JointWF`, and hereditary `ValueMem`; it does not admit an N port or
construct a cross-incidence map. The selected `Application_N` whole-contract
boundary retains all opaque alternatives and its internal action, but defines
no typed transformation from its Result key to the original key. Typed-core's
Result/literal normalization remains Draft and supplies skeleton equations
only. The full source audit and exact locators are in the independent report
for this checkpoint; this is a bounded selected-clause audit, not a global
nonexistence proof.

The current Rust owner boundary is also explicit. HIR retains literal
occurrence and spelling; F5 `emit_integer` emits `Int`/effect constraints;
the shadow structural core can retain an integer spelling but marks the form
pending and untyped. None emits an original Result port or Return witnesses.
The selected typed-evidence shadow layer accepts caller-supplied ports and
validates wiring, without licensing them. Thus the natural implementation seam
is a future approved source-to-typed-core literal constructor before
Reify/Call consumers; interpreting F5 constraint endpoints as a port license
would conflate separate owners. This is current-code characterization, not
implementation authority.

The minimum selected-consumer obligation is now separated from stronger
relation equality. Code-Result needs authentic original Data/Result formation
and one same-tuple Return member. The q1/d1 bridge additionally needs a total
one-way map preserving every contract-exposed N alternative without quotienting
distinct evidence, plus whole-action commutation and actual-domain compatibility.
It need not be surjective onto every original alternative. The two-versus-one
conditional discriminator refutes an injective lossless map for those assumed
fibers only; it does not refute a many-to-one one-way membership map, nor claim
those fibers are selected source inputs. An inverse is needed only for a
stronger relation-equality/invertible-transport claim.

The Draft producer candidate has passed its two bounded reviews, and the
selected-kernel audit found no supplier for the cross-incidence law. Selecting
the static `Original-ResultLiteral` case is now a concrete user decision. That
selection alone would not prove the N-to-original map; it would leave the
domain, witness-map and action-square obligations explicit for subsequent
proof. No compiler implementation can rely on this candidate before approval
is recorded under the question-board workflow.

## Review and checks

- `compiler_referee`: no BLOCKING, major, or minor finding for the exact
  candidate hash; flagged kernel-domain license, complete witness map,
  interpretation/action commutation, distinct-key transport and incidence
  compatibility as closure evidence.
- `spec_auditor`: no BLOCKING, major, or minor finding for the exact candidate
  hash; confirmed Draft conformance and that typed-core §6 is not an adopted
  semantic realization.
- Research producer: read-only inspection of the approved N proposal, literal
  Return construction, old R-flat candidate, Call-input contract, typed-core,
  source-contracts, and selected semantic-input. No executable oracle,
  enumeration, tests, builds, probes or Git operations.
- No independent review of the conditional discriminator itself; it shares
  the assumed Return rule and does not validate that rule.
- `compiler_referee` clarified the minimum target: Code-Result/Return
  introduction needs authentic original formation and one same-tuple member;
  q1/d1's full boundary adds total lossless one-way transport, without
  surjectivity or full relation equality. The two-to-one discriminator also
  excludes injective transport under its conditional fiber premise. Wording
  updated; no change to the candidate claim or user-authority status.

No tests, builds, measurements, or production changes were performed. Full
inference/F5 replacement remains active; this note closes no gate.
