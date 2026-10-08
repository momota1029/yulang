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
bijection preserving all alternatives. This only separates fiber equality or
invertible transport from a weaker one-way map: a many-to-one map may still
exist if the target contract permits collapsing alternatives. The candidate's
required notion of preservation must settle whether that collapse is allowed.
This is a conditional interface discriminator, not a claim that a selected
source contract permits these exact fibers. It fails if the actual Return
kernel supplies a complete incidence reindexing with an established inverse.

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
an inverse and both inverse laws. If only one-way member transport is needed,
the kernel must still exhibit that map; the cardinality discriminator alone
does not refute it. A satisfying Return member may support
original Return introduction, but static registration alone supplies neither
that member nor transport of every N witness alternative.

This is downstream of the candidate's proposed static owner constructor and
upstream of original Reify/Delay, whole-argument checking, emitted membership,
admission and compiler implementation. It does not decide whether to adopt
the proposed constructor. Therefore no question-board decision is ready yet:
first locate the actual kernel supplier or record that its required law is a
separate unresolved premise.

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

No tests, builds, measurements, or production changes were performed. Full
inference/F5 replacement remains active; this note closes no gate.
