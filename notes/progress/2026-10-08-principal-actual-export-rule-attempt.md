# Actual common-export evidence: constructor extraction and first checking cut

Date: 2026-10-08
Status: unreviewed conditional derivation and bounded constructor audit
Baseline: `162aac715e04bc54985737887bcfc9bf98e20a3f`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this note only
Implementation authority: none

## Objective and result

Derive actual-export evidence by examining source/checking constructors,
rather than assuming the predecessor's whole export-elaboration hypothesis.
A finite, acyclic allocation derivation with unchanged non-coverage interfaces
provides a concrete proof-DAG construction. It works even when a public output
allowance strictly exceeds the original output allowance. It is conditional
on the independently supplied complete relation/descriptor contracts and on
acceptance of source-contracts §5.3's proposed resolution calculus.

The ordinary representation-preserving checking rules alone do **not** supply
that result. Their first unmatched case is a single value check with a
nonidentical value interface: `VIncl(A,B)` is not an identical primitive
`Eq` leaf, a provider-guarantee leaf, or an actual Function-introduction
premise. This is a missing evidence derivation, not a source counterexample
or proof that the existing resolver has no other applicable case.

No `ALL_VIEW` or `PRINCIPAL` gate closes. The positive part specializes the
already conditional allocation theorem; its additional content is the
explicit constructor extraction and the first checked-syntax boundary.

## Authority and inputs

The primary fixed the language meaning and baseline. Governing sources:

- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§5.3, 6.1–6.3, 7, 10. Sections 2.1–2.2, 3.1–3.3, 3.7 and 5.1–5.2 supply
  the precise relation constructors, active descriptor premises, complete
  inventories, Option 2 grammar and common formation used below.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §§7, 9; §6's structural synthesis table identifies the source constructors.
- [Certified uses](../design/2026-10-04-certified-callback-and-constrained-use.md)
  §§2–3, 5–6; these carry a supplied evidence DAG, not create its missing leaf.
- [Safe preimages](../design/2026-10-04-common-allowance-context-preimage.md)
  §§3.2, 6.1, retaining independent admission and semantic/evidence separation.
- DAG [ALL-VIEW and PRINCIPAL](../theory/successor-proof-obligations.md), and
  the [predecessor attempt](2026-10-07-principal-whole-relation-factorization-attempt.md).

The committed Option A, Option 2 and inlet-context answers were read and
checked against baseline bytes. Membership remains independently interpreted;
all independently typed compatible punctured contexts remain in the admission
quantifier. Production extras are permitted without source anchors. No Oracle
semantics, observed-support validity, root substitution, role reinterpretation
or new source acceptance restriction is used.

The cited mathematical packages are Reviewed/Draft conditional packages,
not Authoritative adoption of their concrete primitive or resolution clauses.
The accepted user decisions do not promote those clauses to production facts.

## Exact positive class and hypotheses

Fix the original source `S`, scope tree `T`, `xi=(nu,K,D)`, and actual designated
ordinary descriptor `B_common`. Consider an independently checked view with:

1. A finite acyclic decorated derivation using literal, name, operation,
   lambda, reify, result, designated elimination, Call and Bind. Each primitive
   has its independently typed whole relation, descriptor typing and complete
   admission contracts. Each ordinary root alternative is accounted for.
2. A finite §6.1 allocation derivation for each selected outward region.
   Local endpoints belong to original occurrences; the original outer
   endpoint is `E_out`. The public rule adds a separate legal allowance `W`
   and `Cov(E_out,W)`. Every selected contributor is connected to that region
   by its actual allocation premises, rather than by a support observation.
3. Exactly the original non-coverage kernel, value interfaces, actual roles,
   entry, consumers, ordered operands, provider identities and scope tree,
   modulo one legal uniform freshening/graft. Every changed descriptor exposes
   its actual fixed-envelope `Bound` leaves as required by §5.1. Original
   constraints and source-node endpoints remain present.
4. Complete admission and membership clauses in the active common-formation
   shape of §5.1. Setting only the fresh coordinate `a=W` is legal. No predicate
   outside the matched identity or explicitly exposed guarantee cases changes.
5. For production roots, a supplied exhaustive paired §3.7 grammar, with the
   same abstraction `W_abs,Z`, invariant parameters and unchanged-admission
   certificate. Its hard guards have finite `Eq`/`Le` proofs. This is an input
   contract, not a claim that the actual production grammar is already known.
6. The resolver accepts the exact finite §5.3 certificate at the actual roots.
   This is the named local resolution-conformance hypothesis. It cannot be
   removed by the following source induction.

These are sufficient hypotheses for a restricted class within `V_alloc,H`;
they do not define independent validity or its full supported envelope.
Deleting hypothesis 6 leaves a proof in the candidate calculus, without a
proved accepted `Direct` judgment. Deleting the complete primitive/descriptor
premises leaves source synthesis without complete membership evidence.

## Constructor extraction, before the root query

For a source allocation node `n`, let `A_n` be its original allocated output.
The certificate contains original-scoped coverage edges to its parent, and
fixed relation/operand entries. Traverse the finite derivation bottom-up.

| Source case | Coverage extracted | Complete relation proof case |
| --- | --- | --- |
| literal/name | Pure evaluation; preserve any separately latent provider contract. | Identical primitive/root operand `Eq` leaf. Name does not force its provider. |
| operation declaration | Use its declared, independently checked contribution and consumer. | Identical declaration instance, native delimiter and consumer operands. |
| result/reify/lambda | Preserve the returned/stored provider and its latent region; do not execute it. | `Eq-C`/`Le-C` only for the same constructor and captures. A latent body's coverage belongs to its own region. |
| designated elimination | Use the independently identified consumed port's allocation premise. | Same port, profile, consumer and original dependencies; no shape-selected force. |
| Call | Retain allocation edges for callee evaluation and the **complete receiver** output, including supplied source-required argument/hygiene contributions. | Match Call's actual receiver/receipt, entry, body and designated result consumer. Use congruence at their same ordered operands. |
| Bind | Retain both first-computation and ordered-suffix allocation edges, even if the first never returns. | Match result/rebind/current-state witness and suffix. Request continuation keeps that suffix at the current resumed state. |
| public guarantee | Add `Cov(E_out,W)` without replacing `E_out`. | `Guarantee` at an exposed eligible output leaf. |

The Call row does not equate the closure body with complete invocation. A
value entry can execute the incoming carrier before the body; retained entry
can ignore it. Operation invocation includes its declaration-derived consumer
after native return. These are unchanged `z` operands in §5.3, not inferred
from outward effect support.

For each selected contributor `B_j`, follow its finite allocation path through
Call/Bind composition to `E_out`, then the public edge to `W`. Every step is
a referenced original coverage clause. Compose these implications inside the
allowed coverage DAG, obtaining `Cov(B_j,W)`. This composition uses no
successful Function comparison. It covers the syntactic suffix even when
execution has not reached it, because its allocation edge already exists.
Literal/name and latent-construction cases create no extra outward edge.

This proves extraction by induction on the supplied finite allocation tree.
It proves nothing about an arbitrary semantically valid view lacking that
tree, or a latent region that was not inventoried. No endpoint equation
`B_j=W` or `E_out=W` was used.

### A concrete nontrivial source skeleton

With independently typed operation declarations `p: Unit -> [E_p] A` and
`q: A -> [E_q] B`, consider the body derivation

```text
bind(x,
  call(result(operation p), result(literal Unit)),
  call(result(operation q), result(name x))).
```

A lambda can store this body under a supplied fixed parameter interface.
This is derivation notation, not proposed surface syntax. Let `A_p,A_q` be
its original **complete call allocation** endpoints, and `A_b=E_out` its
original Bind allocation endpoint. They are not asserted equal to the
printed declaration rows. The independently supplied allocation premises give

```text
Cov(A_p,A_b), Cov(A_q,A_b), Cov(A_b,W).
```

Every actual selected contributor in either call has its own original edge to
that call's allocation; composing the displayed edges gives its `Cov(B_j,W)`.
This exercises two Calls, actual operation result consumers, one original
result binding and an ordered pending suffix. The argument `x` is the first
call's returned value at the original rebind. No second provider or state
witness is chosen for the suffix. `W` can be strictly wider when an independent
coverage proof licenses that widening. This is a conditional derivation
instance, not a claim that arbitrary raw declarations supply all premises.

The positive effect is visible even in the smallest local certificate with
one eligible provider leaf: `Cov(B,W)` yields
`Eq(Bound(B,u) and Bound(W,u), Bound(B,u))` by `Absorb`. A nonidentity coverage
proof therefore suffices; identical effect endpoints are not required.

## From extracted leaves to the actual-export certificate

Choose `a=W` at its permitted original binder, for each fixed public solution.
The graph and evidence template are finite and fixed for the view; choices do
not occur independently per runtime challenge.

For every selected admission incidence, `Absorb` removes the added common
`Bound(W,u_j)` next to its original `Bound(B_j,u_j)`, retaining the same
provider and full non-coverage envelope. Identity handles all unchanged
primitive/descriptor leaves. `Eq-C` lifts these proofs through each actual
admission constructor, with the same original binder in the same position.
The matched allocation contracts identify the resulting clauses with `D_V`.
This gives a finite `Eq(D_common,D_V)`.

In membership, use absorption at retained incidences and `Guarantee` for an
eligible original output bound covered by `W`. All non-coverage leaves have
identity proofs. Lift with `Le-C` only at positive children; every other child
must have the actual `Eq` proof. Constructor induction gives the source-base
and hard-envelope comparisons. It is a clause comparison that includes
ordinary `DescMem`, not just containment of emitted observations.

For Option 2, pair every equation of the supplied abstraction grammar. Its
source arm uses the proved base comparison; its `Z` arm uses the same whole
extra relation, with no source anchor; its rewrite arm retains the same
`W_abs` witness and uses the recursive pair assumption positively. Conjoin
the proved hard-guard comparison. The registered recursion rule yields `Le`
for the entire membership root. This is an induction on arbitrary finite
abstract derivations, not a fixed bound on their lengths. An unmatched extra
alternative or changed admission rule prevents this lift; it is not discarded.

Finally, apply the one §5.3 `Function` introduction to

```text
Direct(B_common(s,W), R_V(v); constructed finite DAG).
```

It has matched actual role/entry/consumer/interface, the displayed `Eq`
admission proof, the displayed `Le` complete membership proof, and one
original incidence map. There is no intermediate successful root query.
Hypothesis 6 is precisely what makes this candidate DAG accepted by the
resolver. Certified whole-copy/graft transport then carries this evidence,
retaining `C_V`; §5.2's use-projection theorem supplies exact public projection.
It does not enlarge this class to every independently valid view.

## First unmatched checked-syntax case

Erase all composition until one lexical lookup and one proof-only check:

```text
Gamma(x)=Value(A)        independently established VIncl(A,B)
----------------------------------------------------------------
Check(name x : Value(A), Value(B)); retain the same decorated value.
```

Take `A` and `B` nonidentical and not legally identified by retained equality.
The source proof is exactly typed-core §7's value-check case. If it is placed
at a lambda's result, entry and challenge domain can stay fixed while its
checked result value interface changes. No particular `A,B` or Yulang
inclusion example is certified here; this is the smallest unmatched proof
sequent conditional on its independent semantic premise.

In the displayed §5.3 inventory, the resulting changed value/descriptor
predicate has no identical primitive `Eq` leaf. `Guarantee` and `Absorb`
concern allowance leaves at a fixed non-coverage envelope; they do not change
the value interface. Congruence needs an already supplied child proof and
cannot invent that leaf. Registered recursion has nothing to discharge in
this one-node check. The parent `Function` rule also requires matching the
non-coverage interface, so merely granting a semantic value inclusion does
not repair that premise.

The minimum missing bridge is therefore an independently grounded finite
evidence derivation for this particular `VIncl` checking case **and** an
applicable whole-Function resolver case that permits its resulting checked
interface. For a specific structural inclusion, existing ordinary resolver
rules may provide it; the listed source/checking and restricted certificate
constructors do not state that correspondence. A general rule accepting the
bare semantic proposition would conceal the effective presentation obligation
that typed-core §7 explicitly leaves open.

This is not proof that new language semantics is needed. The selected meaning
already distinguishes semantic checking from effective evidence. First derive
or identify the existing evidence clause for one independently established
value inclusion. If no clause exists, specifying/adopting a concrete evidence
rule is a further resolution contract requiring its normal authority gate.
No rule is invented or adopted here. Similarly, the positive allocation
construction still requires adoption/conformance of its displayed `Function`
rule; source syntax alone cannot prove that adoption.

## Evidence quality, exclusions and resources

Method: direct manual constructor/certificate derivation and bounded document
comparison. Source premises are independent of pending query success. The
proof shares the explicitly supplied primitive, descriptor, active-root,
coverage and paired-abstraction contracts with the cited packages; it is not
an independent oracle establishing those contracts. No transition checker,
differential oracle, search, seeds/ranges or mutation executions were used.
Failure conditions were inspected symbolically: changed value leaves, changed
Call consumers, different Bind state/suffix, lost contributors, omitted extras,
changed admission, moved binders or missing resolution acceptance each blocks
the indicated proof step.

Coverage is the displayed constructor inventory and finite acyclic allocation
class, plus supplied paired positive production abstraction. General recursive
source checking, unmatched abstraction grammars, all semantic `VIncl/CIncl`
proofs, adapters, handler images, mutable State, production conformance,
complete primitive semantics and validity inversion remain unverified. No
repository-wide absence or source counterexample is claimed. Initial large
navigation outputs were truncated; decisive governing sections were reread
in bounded ranges.

Checks: bounded `cat`, `rg`, `sed`; read-only Git HEAD/branch/status; one Python
process comparing baseline `git show` bytes with live dependency bytes and
SHA-256; final leased-note scope/whitespace inspection. Zero builds/tests,
formatters, heavyweight processes, children or Git mutations. No numeric
CPU/RAM/wall-time limit was supplied beyond bounded reads and zero builds/tests.
Peak RSS, CPU and total reasoning wall time were not measured. The output is
one note; no executable artifact needs a deterministic run. Writes stop at
submission; no independent review is claimed.

Recommended next action: assign one known, independently established
representation-preserving value inclusion to its existing actual-root resolver
rule, preserving the fixed domain and all original decorations; derive that
missing leaf and parent case before attempting generic checking completeness.

## Dependency pins and freeze

At final comparison, all below matched baseline bytes. SHA-256 pins:

```text
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186 notes/design/2026-10-05-source-contracts-and-common-allowance.md
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e notes/design/2026-10-02-typed-computation-core-elaboration.md
887bc7c0743d2f34608b46ccb8e5ee9b58ea4a39995b93a5aaced764295bae80 notes/design/2026-10-04-certified-callback-and-constrained-use.md
e3aa657d281f8e528d41544d862ee5e938bb6d3c4d36fa60fd04306c1f1dfb7e notes/design/2026-10-04-common-allowance-context-preimage.md
9dbf397ec1ea5f9ce5ea8ed732e4c5c5c6bfdb5c9719010d5fc8b002a8f98487 notes/progress/2026-10-07-principal-whole-relation-factorization-attempt.md
18bfa4e5bb461616ca17a0c9a1492f75ff7fca2f6231a13b3d68e0a3335136dc notes/theory/successor-proof-obligations.md
7e7f3c717b16a70fc754c930a1654666c8b61a89a4861fca27b0ae3fa5f1890a questions/2026-10-05-production-function-denotation/approved-answer.md
d9ddea04a44d2307cf587bc4ae9b2a1c50d062c4077306a5bf9ea9da00eca179 questions/2026-10-05-production-function-bound-membership/approved-answer.md
9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3 questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md
```

Rules `research-lab.md`, `design-authority.md`, `git-concurrency.md` and
`question-board.md` also matched pinned bytes. Task/index navigation was read
for routing only; no unfinished worker artifact was a premise.

## Commit packet

- Exact leased path: `notes/progress/2026-10-08-principal-actual-export-rule-attempt.md`.
- Baseline SHA: `162aac715e04bc54985737887bcfc9bf98e20a3f`.
- Changed dependency hashes: none at final recheck.
- Claim/review status: frozen unreviewed conditional derivation and bounded
  unmatched-constructor audit; research-only, no independent certification.
- Checks already run: exact governing-section reads, committed-answer/baseline
  byte equality and SHA-256 checks, final leased-path/whitespace inspection.
  Zero builds/tests/probes.
- Proposed message: `research: derive matched allocation export evidence and isolate value-check cut`.
- Shared-record deltas intentionally left for primary/curator: optionally link
  this note from `ALL_VIEW` as its matched allocation construction and single
  `VIncl` evidence boundary. Keep `ALL_VIEW`, `PRINCIPAL`, complete checking,
  descriptor/admission and production gates open. Do not claim a new source
  counterexample or promote the candidate §5.3 calculus to selected semantics.
  No shared task/index/authority/theory, question bundle, compiler, manifest,
  lockfile or other worker file was changed.
