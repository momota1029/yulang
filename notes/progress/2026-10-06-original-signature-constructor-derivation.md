# Original signature construction: inversion through the decorated-kernel leaf

Date: 2026-10-06
Baseline: `ea3ae1706e318ffd2261694b17244353f0ea4c0a`
Status: frozen, independently compiler-referee-reviewed bounded research; no semantic or implementation authority
Method: constructive rule-output analysis and induction on constructor derivations
Exclusive lease: this new note only
Review: `compiler_referee` PASS, no findings, on frozen SHA-256 `bd96dfd2bfb4da1875a88b797abf0a7fead6300c9b1af8ab147aa75652e7048d`; scope is the conditional leaf-retention and sequential two-Call derivation only

## Objective and result

Attempt to derive OriginalSignatureFormation from the ordinary source/core
constructors for the approved candidate:

```text
my apply f = { my step x = f x; step }
```

The ordinary constructor outputs do not discharge the requested formation
law. The first unsupplied **input of an existing rule**, rather than a newly
named licensing predicate, is the original decorated signature/owner/view
kernel consumed by the complete Call certificate. Gen-Call-0 constructs the
upper output address and its ElimOrigin correspondence. The subsequent
`TypedCallCert_Dec` explicitly consumes supplied decorated profile premises.
Neither `WF_Dec(U)` nor complete invocation checking constructs them.

The new bounded derivation is a leaf-retention theorem: inverting transport
or adding one ordinary sequential Bind preserves this unsupplied input;
neither operation can convert its output to an exhaustive original constructor.
The second-use extension also separates shared contract identity from distinct
upper occurrences without selecting a slot-sharing policy. This is a proof
obstruction for the inspected rule composition, not a source impossibility,
semantic counterexample, or demonstration that a user decision is required.

## Authority, dependencies and hypotheses

The assigned `2026-10-06-source-contracts-and-common-allowance.md` locator does
not exist. The existing document is
[source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md);
this correction was reported to the primary. The governing sections used are:

- [Inferred call views](../design/2026-10-05-inferred-function-call-views.md)
  §§1.1–5, and integrated [answer a2](../../questions/2026-10-05-function-call-view-formation/approved-answer.md):
  one shared source contract, original identity/scope, Q independence, and
  detailed formation rules still open.
- [Directional decision](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
  §§2–4: protected-variable to original upper output, no lower backflow,
  distinct introduction witnesses versus static slots. The user's direct
  decision governs; the proposed notation itself remains Draft.
- Source contracts §2, §3 opening, §6.1 and §§8–10: independently interpreted
  primitives and independently typed owner/view kernel are inputs; the
  decorated source envelope already supplies typed paths/owners/receipts;
  allowance coverage is conditional and preserves its non-coverage kernel.
- [Exact nested meaning](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
  §§1–3: sequential local binding, inert return of step, same outer capture;
  no authority for other brace forms.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §§2–3,6: ordinary Name/Result/Lambda/Bind/Call meanings, Value entry, and
  unknown endpoint checking obligations.
- [Typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md)
  §6: source elaboration supplies signature profiles; indexed relational
  transport retains source witnesses and creates no boundary or grant.

The four assigned predecessor notes and the
[Call construction](2026-10-06-source-call-generation-construction.md)
§§4–5 are reviewed research inputs. The
[FVIEW/SRC entries](../theory/inference-theorem-dependencies.md) retain their
open source-generation and conditional decorated-input scopes.

Fix original source identities/scopes and **one candidate whole row X**,
including `xi=(nu,K,D)`, upper demand U, providers, world, continuation and all
checking constraints. No complete/admitted solution is presumed. Logical
witnesses remain inside their original rigid dependencies. Reused hypotheses
H are the approved core correspondence, lexical resolution, ordinary symbolic
core rules, the selected unannotated seed and same-root seed-at-exposure
witness. Independently typed packet correspondences are explicit conditional
inputs whenever packet transport is used. H does not include complete original
slots, a profile certificate, successful Q, or admission.

Established predecessor result: the exact component has one direct justified
upper introduction `a0=(k,beta,u,sigma_x,outEff(U))`. Its constructor inventory
is not repeated here, and its scope is not promoted to singleton Slots.

## Partial construction and the first existing-rule input

Use `beta=(d_f,R)` with the same original formal and shared contract root R.
Ordinary parameter and Name rules give `Value(A_f)`, `Value(A_x)` and actual
returning Name roots `J_f,J_x`. The source Call emits, without solving them:

```text
U : one dependent complete Function demand
p0 = outEff(U)
ElimOrigin(C_fx,u,d_f,R,p0,p_out(C_fx))
WF_Dec(U;xi), VIncl(A_f,U;xi)
WholeArgCompatible(J_x,CarrierContract(U);xi)
CIncl(ExecuteCallableImage(J_f,Delay(J_x),U,e;xi), Comp(E_c,A_c);xi)
TypedCallCert_Dec(C_fx,U,e;xi)
```

Then the selected directional rule constructs a0 from the original protected
variable and upper-use premises. This tree supplies a mandatory member,
address sorting, protection and absent annotation grant. It does not need
`TypedCallCert_Dec` to be solved first, and it does not certify that obligation.

The Call construction §5 explicitly states that `TypedCallCert_Dec` retains
the **supplied decorated** receipt, profile, operation, observation and
correspondence premises beyond the initial source incidence. Source contracts
§2.1 separately requires independently typed primitive and owner/view kernel
contracts. Typed-boundary §6 supplies profiles from source elaboration and
leaves their derivation open. Thus the earliest relevant open leaf on this
chosen proof spine is the original signature/profile part of that input,
before its receiving realization or event activation is considered.

The concrete field still lacking a source constructor is a complete original
table of **(source-owned slot, signature occurrence, complete contribution,
original scope/dependency witness)** for U at beta, together with the rule
that inverts every row of that table. A complete contribution retains the
invocation's entry/body/consumer and original provider/world predicates;
it cannot be represented by outward support or a bare effect endpoint.
`ElimOrigin` supplies the p0-to-source-output field for the mandatory member;
it does not supply the table's full contribution interpretation or closedness.

This locates the needed input inside an existing complete-Call rule. It does
not claim that the missing field requires a new runtime carrier or source
feature. It could be supplied by an expanded source Function constructor.

## Leaf-retention derivation

Consider the finite derivation fragment formed by ordinary core rules,
Gen-Call-0, Dir-Protect and the specified typed packet images. Treat a supplied
original profile/table leaf P as a formal input, with separate provider/result
inputs `P_i`. Write its packet occurrence as `M_*P`; retain the source tag in
every image. This is proof notation for the existing transport operation.

The relevant constructor equations, on one X, are:

```text
Name/capture:     P_read = Id_* P_environment
Result/rebind:    P_rebound = M_result_* P_received  [actual Return required]
returned value:  P_result = union_i M_i_* P_i        [indices retained]
Bind:            share RHS result and environment with the ordered suffix
Lambda:          retain captured packets without executing the body
Dir-Protect:     append the one original witness justified by its premises
```

**Conditional leaf-retention theorem.** In this fragment, any original own-beta
incidence carried from P to the captured f read has an inverse derivation
ending at P with the same source witness, scope and xi. If the input witness
is a provider/result arm, inversion instead ends at its separately indexed
`P_i`. No rule in these inverse trees proves exhaustiveness of P's original
applicability table.

Proof by induction on the packet derivation:

1. At Name or capture, invert the indexed identity image; recover the same
   input path, source tag and full packet.
2. At Result/rebind, invert the given typed image and retain its actual Return
   witness. Pending receipt has no such inverse; it does not create a read.
3. At a multi-input result, the output witness identifies its source index i.
   Invert only that image. Shared beta labels or equal endpoints do not choose
   an arm and cannot turn provider inheritance into a fresh introduction.
4. At Bind, retain the shared result/environment witness and invert the RHS
   or suffix premise selected by the indexed packet. No separate xi is chosen.
5. At Lambda, recover the captured lexical reference; inert closure creation
   introduces no original effect occurrence.
6. At Dir-Protect, recover its protected-variable and source-upper premises.
   Its conclusion accounts for a0; it contains no premise-free conclusion
   that every incidence belongs to this case.

These exhaust the chosen fragment's constructors. The f capture/read route is
an identity-address schema on `Paths(A_f)` (Call construction §4.4). Therefore
an input incidence in that schema is preserved rather than erased along this
route. This is a conditional statement about an incidence supplied to P;
it asserts neither the existence nor permission of an additional incidence.

Consequently the ordinary induction has a genuine remaining leaf. Defining P
to contain exactly the directional conclusions removes that leaf by a new
closedness assumption. Inverting a solved `WF_Dec(U)` or `VIncl(A_f,U)` would
instead recover decorated membership/typing evidence; no displayed rule turns
that evidence into the required original source-table constructor.

This is a bounded nonderivation in the explicit rule composition. It is not
a proof that all future derivations fail or that the selected language has
two meanings. In particular, arbitrary relabelings or extra rows of P are not
presented as valid Yulang source models.

## One minimal typed-core grammar extension

Replace the step body's single Call by the existing ordinary core term:

```text
bind(y,
  call(result(name f),result(name x)),
  call(result(name f),result(name y)))
```

This adds one Call under one sequencing Bind. It is the smallest sequential
spine in the inspected core grammar that contains two upper uses of the same
formal: with one Call there is no pair; two computation nodes require the
grammar's Bind to retain sequential result/state sharing. This minimality is
about that spine, not all possible source syntax or branch constructions.
No Yulang brace spelling, acceptance or extension to the narrowly approved
nested-block meaning is inferred.

Let the first upper occurrence be u0 at `sigma_x`, the second u1 at the suffix
scope `sigma_y`. Ordinary Bind rebinds `y:Value(A_0)` after the first actual
result; its complete relation retains the original suffix and current state.
Generation can emit both complete demands symbolically:

```text
VIncl(A_f,U0;xi)      VIncl(A_f,U1;xi)
u0 != u1             same d_f, A_f, R, beta
p0^0 = outEff(U0)    p0^1 = outEff(U1)
```

The two source occurrences stay distinct even if their endpoint values happen
to coincide. Sharing A_f does not by itself assert `U0=U1` or decide whether
their static slots coincide. Each complete Call has its own supplied decorated
kernel leaf `P^0,P^1`, constrained jointly on X. Bind transports their indexed
inputs and introduces no rule for identifying their slots or contributions.
The leaf-retention induction therefore extends with exactly its Bind case.

If the original seed-at-exposure premise is independently supplied for u1,
Dir-Protect also derives `a1=(k,beta,u1,sigma_y,p0^1)`. This is conditional;
the extension does not prove multi-use seed eligibility, role aggregation or
late-seed replay. It supplies no new protection on the first result's latent
shape or either provider lower occurrence.

The smallest remaining input now has two independently indexed kernel rows
and a source justification for their slot association. A normalization equating
endpoint values cannot supply that association. This discriminates the needed
identity data; it is not an admitted-event counterexample or two alternative
language meanings with different observables.

## Exact stopping condition and required next evidence

Construction stops before supplying the original source-owned signature kernel
of the complete Call certificate. The necessary producer must give actual
constructor clauses for that table and show, on the same X and xi:

```text
source constructor for (slot,position,contribution,scope)
    => original licensed table entry
original licensed table entry
    => inversion to such a source constructor
```

For the exact candidate, the known p0 member must survive both directions.
For the sequential core extension, both upper occurrences and their association
must survive without forcing equality or disjointness by convention. Inherited
provider/result packets remain distinct source arms in both directions.
Generalization or fresh use must apply one capture-avoiding action to all
coordinates, retaining original rigid dependencies and shared K,D; preservation
of arbitrary generalization is still unproved here.

No source counterexample was found or searched. No two fully specified,
authority-consistent semantics with a different observable on one admitted
event/path were constructed. Therefore this result supports a proof-work
handoff, not a new user question. It does not establish `Slots(beta)={a0}`,
complete-row nonemptiness, all-view principality, production membership or
initial/history admission. Successful Q would not fill this input.

## Checks, independence, coverage and resources

Commands: bounded `cat`, `sed -n`, `rg`, `rg --files`; read-only HEAD lookup;
Python SHA-256 and byte comparison using `git show <baseline>:<path>` for all
13 direct document dependencies; note-local integrity/dependency recheck at
freeze. All 13 current inputs matched their pinned blobs. Some aggregate
captures truncated; the decisive constructor, profile-input and FVIEW/SRC
clauses were reread in bounded captures. No absence result relies on truncated
output or a repository-wide search.

No tests, builds, checker, Oracle source/output, executable experiment,
formatting, Git mutation, child delegation or scratch output. Source rules
and independent kernel meanings are shared assumptions with the predecessor
proofs; this induction does not independently validate them. A checker that
implements these image equations would only check the same conditional rules.
Seeds/ranges and executable mutations are inapplicable. Coverage is the exact
candidate's existing derivation fragment and the one sequential two-Call core
extension, conditional on the stated decoration/exposure inputs.

Proof mutations fail at explicit premises: omit source indices and inversion
cannot distinguish own versus inherited evidence; replace the complete kernel
with endpoint equality and contribution/slot identity is lost; drop actual
Return and rebind invents a read on Pending receipt; choose xi separately for
the calls and Bind loses its original shared result/provider/state witness;
declare Dir-Protect exhaustive and assume the missing source-table inverse.
These are logical failure conditions, not executed tests.

Resources: short lightweight shell/hash processes, zero heavyweight processes,
one leased output file. No numeric CPU/RAM/wall-time limit was supplied.
Aggregate CPU, peak RSS and elapsed wall time were not instrumented. Omitted
scope includes arbitrary source forms/annotations, recursive formation, multiple
use-role aggregation, semantic slot association, complete kernel interpretation,
all carriers/worlds/histories, production-only observations and principal solving.

Recommended next action: expand the original signature/owner/view part of
`TypedCallCert_Dec` into source constructor clauses and their exhaustive inverse,
first for this exact root and the sequential two-use core extension. Require
original complete-contribution and slot-association data; another profile-image
checker or source-node inventory leaves that exact leaf unchanged.

## Frozen direct dependencies

The table below is appended from the pinned-byte check; these hashes describe
inputs, not authority or independent review of this output.

| Direct input | SHA-256 |
| --- | --- |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| `notes/progress/2026-10-06-original-profile-applicability-derivation.md` | `d66a7ec9a57c676668d0ad4531a1607594e681a59c17d0cf239e29cd7cd02905` |
| `notes/progress/2026-10-06-original-signature-licensing-construction.md` | `f5032a91781706551dcd01474f6024eb34fcb0cb110fa6157f7ec577ccfc5cff` |
| `notes/progress/2026-10-06-original-signature-source-supplier-map.md` | `9f160920a0aa43518e93ec8a139e80657a58032a69e13a7bcfd26ba6a3dd1c59` |
| `notes/progress/2026-10-06-source-profile-admission-construction.md` | `00f9e4e8db427fe97a46bd25245cf235c02d2e38007c5b9bb9088d9b40db8636` |
| `notes/theory/inference-theorem-dependencies.md` | `2bab50a7ec42a10f4927a7db2ffd34da5482ad60e8348e7bc9293c53e6200ac6` |

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-06-original-signature-constructor-derivation.md`.
- Baseline SHA: `ea3ae1706e318ffd2261694b17244353f0ea4c0a`.
- Changed dependency hashes: none; 13 direct inputs match their baseline blobs.
  Historical predecessor dependency inventories are not silently updated.
- Claim/review status: frozen, compiler-referee-reviewed bounded derivation and
  conditional leaf-retention theorem; no semantic selection or gate closure.
- Checks already run: governing-source and rule-output reads, constructor
  induction and same-row/index/scope audit, minimal sequential-spine analysis,
  13 dependency hashes and pinned-byte comparisons, note-local integrity check.
  No runtime verification.
- Proposed one-line research-checkpoint commit message:
  `research: locate original signature kernel leaf by constructor inversion`.
- Shared-record deltas intentionally left for primary/curator: record the
  existing complete-Call certificate's original signature/owner/view input as
  the precise source producer leaf; link the leaf-retention derivation and
  conditional sequential-use extension without promoting FVIEW/SRC, Slots,
  complete-row existence, admission, principality or production conformance.
  Tasks, theory maps, indexes, authority and question bundles remain untouched.

Writing stopped after the frozen artifact was submitted and independently
reviewed. Primary owns integration and shared-record adjudication.
