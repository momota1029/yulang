# CALL_TYPE local-law falsification: rejected one-output separation

Date: 2026-10-07
Baseline: `035f7f8e97f5544ccd028bd1f167b83054134fdc`
Branch supplied by primary: `research/simple-sub-intrusion`
Status: compiler-referee reviewed research; failed separation at the complete-premise boundary
Claim class: logical nonimplication for a displayed reduced premise set; no countermodel to complete SEM_JOINT and no Yulang source counterexample
Exclusive lease: this note only
Implementation and semantic authority: none

## Objective, inputs and preserved decisions

Adversarially test the `CALL_TYPE` pointwise typing obligation, complementary
to the separately assigned constructive proof. Seek a model satisfying the
complete fixed independent semantics in which a complete Call output or
pending observation lacks its required descriptor typing. Do not manufacture
an attachment premise inside `TypedCallCert_Dec`.

The exact governing sources inspected are:

- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2–3, §5 and §10: independent descriptor interpretation; complete Call
  equations; separately assumed local typing; conditional comparison calculus.
  Its header says **Reviewed conditional mathematical package; concrete clauses
  remain Draft**. The assignment does not promote it to Authoritative.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md) §9:
  actual provider entry, complete consumer, original raw pending suffix,
  current resumed state and whole joint challenge/observation quantifiers.
- [DAG](../theory/successor-proof-obligations.md), `CALL_REL`, `DESC_CLAUSES`,
  `ADMISSION_CLAUSES`, `SEM_JOINT`, `CALL_TYPE`: independent interpretation
  and its pointwise theorem are separate gates.
- [Full-attack review](2026-10-07-successor-full-attack-review.md),
  “Complete-DAG review and repair”: the independent predicate definitions were
  missing upstream; the reviewed decomposition exposes that prerequisite.
- [Source-association audit](2026-10-07-successor-source-association-falsification.md)
  §§2–4; [Call generation](2026-10-06-source-call-generation-construction.md)
  §5; [complete contribution](2026-10-06-attach-call-contribution-construction.md)
  §§3–6; [conditional lift](2026-10-07-original-association-conditional-call-lift.md)
  §§2–4: retain the supplied typing/profile boundary and distinguish local
  typing from original association. The lift's `H_type` is expressly an input.
- [Source-indexed realization](../design/2026-10-04-source-indexed-callback-realization.md)
  §§3–4: complete constructor images, reference derivations and independent
  initial/response/resume/future-use inventory.

The committed approved [Option A answer](../../questions/2026-10-05-production-function-denotation/approved-answer.md)
fixes the existing complete typed-observation relation and original `Rel_C`
at the same `xi=(nu,K,D)` as the production basis; it does not approve completed
concrete membership clauses. The approved [Option 2 answer](../../questions/2026-10-05-production-function-bound-membership/approved-answer.md)
allows conservative extras with independent complete constraints; it does
not make every production observation source-generated. Both files matched
the pinned commit before consumption.

The primary's selected directional protection, exact sequential nested
`apply/step` meaning, actual callable role and entry, and original source arm,
binders, providers and `X/xi` stay fixed. This attack neither reinterprets them
nor repeats slot cardinality, uniform-witness, endpoint-identity or Oracle
archaeology attacks. It changes one candidate descriptor truth value only.

## Quantified target and the complete-premise boundary

Fix one original candidate `X`, its scope tree and `xi`. Let `h` range over
the independently admitted operand/current-world assignments of that same
Call. Let `w` retain the original operation/provider/consumer/state/continuation
witnesses at their original binders. Write the already constructed raw image
as

```text
F_call(X,h) = J_f >>= ((actual_f,C) =>
    ExecuteCallable_X(actual_f,Delay(J_x),C; original view operands)).
```

The notation is explanatory indexing of the existing relation. It adds no
membership definition, runtime carrier or semantic coordinate. For any
complete output/pending tuple `O` emitted with that original witness, the
target has the following pointwise form:

```text
forall X at original scope, forall h, forall original w, forall O:
    H_local(X,h,w)
    and F_call(X,h,O,w)
    => DescMem(R_call,O,w;xi).
```

`H_local` here denotes the actual fixed ordinary descriptor/carrier,
provider-entry, consumer and independent operand/world premises required by
the governing Call rule. It is a locator for the premises to instantiate,
not a new predicate that this note is permitted to assign independently.
No existential scope is moved outside its original binder. In particular,
the formula supplies no actual inhabitant of an operand/world domain.

Pending typing must retain the original request and its whole remaining
entry/rebind/body/consumer/return suffix. Any extension is quantified in its
original independently admitted response/resume/future-use domain at the
current state. A new compatible extension cannot silently replace the old
`xi`, independently hide its witness, replay receipt or change the receiver.

The full premise means **a jointly justified interpretation satisfying every
original clause**, not an arbitrary interpretation of names occurring in
the displayed constructor equations. At the pinned baseline, `DESC_CLAUSES`
still requests exhaustive descriptor/carrier/local-constructor clauses;
`ADMISSION_CLAUSES` requests exhaustive independent history operands;
`SEM_JOINT` requests their common justified interpretation. These are open
specification/realization obligations, not a supplied finite axiom list from
which exact model satisfaction can currently be checked.

## The smallest rejected candidate and exact satisfaction audit

Use one original scope/assignment, one current configuration `C`, one callable
provider `f`, one ordinary value `a`, and one initial carrier `T`. Use retained
entry with a constant body and the identity designated return consumer, so
the carrier is received inertly and never forced. There are no requests or
future interactions in this candidate. The raw constructor interpretation is

```text
J_f = Return(f,C)
ExecuteCallable(f,T,C) = Return(a,C)
F_call = Return(f,C) >>= ExecuteCallable(-,T,-) = Return(a,C).
```

Receipt/receiver/body/consumer incidences retain their distinct original
labels. This is an abstract interpretation of the displayed constructor
fragment, not a declaration of a source-admitted Yulang program. The argument,
callee and output descriptor occurrences are distinct; the mutation changes
only the output occurrence's membership.

Let `H_display` consist only of those raw constructor equations, a fixed
shared tuple, distinct typed stage labels, and the requirement that named
operand/world predicates are independently evaluated rather than queried
through `Q`. Interpret those named operand/world predicates as true at this
single tuple. Keep `M_E(h,Return(a,C),w;xi)` true and set

```text
DescMem(R_call,Return(a,C),w;xi) = false.
```

Changing that last value to true leaves every `H_display` equation unchanged.
Thus, by a direct two-interpretation argument, `H_display` does not logically
imply the target descriptor fact. One output is minimal for this reduced
separation: with no emitted output tuple the target implication is vacuous.
This is a propositional/relational observation, not a bounded source result.

| Requirement | Candidate satisfaction | Consequence |
| --- | --- | --- |
| Raw Return/Bind/Call equations | Yes, by the displayed reductions | The whole raw Call emits the sole output. |
| Same original tuple and stage incidences | Yes within the candidate | No callee-prefix/receiver collapse or separate witness choice occurs. |
| Request equation and retained pending suffix | Vacuous because there is no request | Supplies no pending-history coverage. |
| Comparison independence | Yes for the assigned candidate atoms | No `Q`, containment oracle or resolver is used. |
| Actual independent operand/world admission | **Uncertified** | Truth assignment to an atom is not a derivation from its original clauses. |
| Complete descriptor/carrier/provider-entry/consumer clauses | **Uncertified** | A typed callable clause may require precisely the output fact erased here. |
| Justified common SEM_JOINT interpretation | **Uncertified** | There is no basis to claim the candidate satisfies every original clause. |
| Source-contracts §3.5 local descriptor typing hypothesis | **No** | The proposed erasure violates the relevant constructor typing lemma. |
| Complete decorated `CIncl` against the target result, if required as a premise | **No** under its ordinary complete inclusion meaning | A sole output outside the target descriptor cannot satisfy that inclusion. |
| Source-valid counterexample / gate falsification | **No** | The candidate is rejected at the complete-premise boundary. |

The candidate therefore proves neither nonimplication from full SEM_JOINT nor
a false local law in Yulang. Adding one request, more providers or an exhaustive
finite search would leave the same premise uncertified. The lane stops here.

## Why the two apparent repairs do not resolve this attack

Source-contracts §2.2 defines the constrained observable bound using both
`M_E` and `DescMem`. Consequently membership in that already filtered bound
implies descriptor membership. The erasure candidate has an empty filtered
fiber, despite its nonempty raw constructor image. Inverting that conjunction
does not prove that every raw source-generated observation survives the
descriptor filter. Section 2.2 explicitly requires a constructor typing
lemma to avoid that loss, and §3.5 assumes those lemmas in C-realization.

The Call-generation note §5 retains complete `CIncl` of the execution image
against the original result, together with `TypedCallCert_Dec`'s supplied
decorated premises. If independently established complete `CIncl` already
entails the sought output membership, it rules out this candidate directly.
That is a conditional extraction from an inclusion premise. It does not
derive the inclusion from independently admitted operands and source
constructor clauses. It also cannot be used to justify a certificate that
already assumes the original attachment targeted downstream.

Source-contracts §5.3 supplies congruence/inclusion rules for **fixed** jointly
interpreted constructors, preserving all non-child operands and existing
ordinary descriptor membership. Its soundness establishes comparison under
those semantics. It gives no rule allowing this candidate's arbitrary
provider predicate to certify the erased output fact.

This is a rigorous failed separation: the displayed equations admit the
reduced candidate; every route that certifies the missing complete premises
either remains uninstantiated or imports a typing/inclusion condition that
rejects it. No impossibility or uniqueness of a complete semantics follows.

## Incidence, independence, omitted cases and next method

The sole callee prefix here is `Return(f,C)` and has no executing request.
That makes prefix versus invocation incidence inert in the candidate, rather
than proving it for effectful callees. For the full theorem an effectful
callee's request must compose with its original pending invocation suffix
under Bind; its request stays at the callee's typed incidence. The receiver's
upper invocation view covers actual entry, body and designated consumer. No
Call typing conclusion licenses stamping every prefix request with the
receiver's upper protection. This is already fixed by the complete Call
records, not a new selected meaning.

No Oracle source, output or semantics is used. There is no reference/candidate
executable pair: a checker implementing these same supplied equations would
only establish consistency of those equations. The reduced separation shares
their whole tuple and transition equations and varies one unconnected output
descriptor fact. Its failure to certify the complete clauses is explicit.
Seeds/ranges, executable mutations and measured performance samples are
inapplicable. Exactly one analytical output-membership erasure was attempted;
no larger probe matrix was run.

Unverified scope: real typed operand/world inhabitance, the complete
independent descriptor/provider/consumer clauses, Value entry and its Force,
operation-native return plus declared consumer, effectful callee prefixes,
pending/resume/future histories, latent returned handles, recursive consumers,
production-only Option 2 extras, original association/licensing, whole-source
adequacy, principality and production conformance. Soundness and all these
obligations remain intact.

**Recommended next action:** ask the constructive lane to identify the actual
independent descriptor/provider-entry/consumer last rules that reject this
one-output erasure, including their typed Bind/pending premise at the same
original `X/xi`. If those last rules cannot yet be instantiated, return that
local clause boundary to `DESC_CLAUSES`/`SEM_JOINT`; do not enlarge this search
or introduce attachment into `TypedCallCert_Dec`. This is a research-premise
blocker, not a newly established user-decision blocker.

## Checks, resource use and frozen dependencies

Commands: bounded `cat`/`sed`/`rg` reads of the sources above; read-only
`git rev-parse HEAD 035f7f8e9`; an eleven-path Python byte/hash comparison
using read-only `git show BASE:path`; leased-path absence check. The initial
broad `rg` included nonexistent `spec/`, returned status 2, and was followed
by targeted searches of the actual design/progress/theory paths. The initial
combined navigation read was truncated; the exact governing sections and
specific relevant predecessor sections were subsequently read narrowly. No
complete repository search or nonderivability claim is made.

All eleven direct dependencies matched the pinned commit before writing.
No builds, tests, compiler/code edits, checker processes, formatting, Git
mutations, child delegation or shared-record edits occurred. Only this leased
note was written. Independent read batches used at most three lightweight
processes; no heavy process ran. No numeric resource budget was supplied with
the assignment. Total wall time and peak memory were not instrumented;
individual read/hash tool calls reported subsecond durations. No performance
claim follows. Final path-local integrity/freeze evidence is in the handoff.

| Direct dependency | SHA-256 |
| --- | --- |
| `notes/theory/successor-proof-obligations.md` | `18bfa4e5bb461616ca17a0c9a1492f75ff7fca2f6231a13b3d68e0a3335136dc` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-04-source-indexed-callback-realization.md` | `76874a219ac86068027b1f08a5bc27a12d93a0169a52cebd896a6ff6f2c6b671` |
| `notes/progress/2026-10-07-successor-full-attack-review.md` | `ad449e58f693f55e87f8b3c9a7680ef96ebf177759d7b27e1db0da031c012a2e` |
| `notes/progress/2026-10-07-successor-source-association-falsification.md` | `09a4aee423985c03f1365574e1d4572e67cc6b2f3f3c25fa747b711bbe304738` |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| `notes/progress/2026-10-06-attach-call-contribution-construction.md` | `4261105c8f9a5012a693cc39dc0f7df8c0e70024594a10282046dbaebf851a96` |
| `notes/progress/2026-10-07-original-association-conditional-call-lift.md` | `af3e95a760bee396a0f07d421d8fe2a8c775ab414b354abf15b103345d1cc46a` |
| `questions/2026-10-05-production-function-denotation/approved-answer.md` | `7e7f3c717b16a70fc754c930a1654666c8b61a89a4861fca27b0ae3fa5f1890a` |
| `questions/2026-10-05-production-function-bound-membership/approved-answer.md` | `d9ddea04a44d2307cf587bc4ae9b2a1c50d062c4077306a5bf9ea9da00eca179` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-07-call-type-local-law-falsification.md`.
- Baseline SHA: `035f7f8e97f5544ccd028bd1f167b83054134fdc`.
- Changed dependency hashes: none at the prewrite comparison; the final
  comparison/freeze evidence is reported in the handoff.
- Claim/review status: frozen unreviewed research; reduced nonimplication and
  rejected countermodel; no closed `CALL_TYPE` or independent-review claim.
- Checks already run: governing/prior-note reads; eleven pinned dependency
  byte/hash comparisons; leased-path absence; final narrow artifact integrity
  checks in the handoff. No executable semantic check or compiler check.
- Proposed one-line commit message: `research: record Call typing falsification boundary`.
- Shared-record deltas intentionally left for primary/curator: optionally cite
  the rejected erasure and distinguish raw-image typing from filtered
  membership or supplied `CIncl`; retain `DESC_CLAUSES`, `SEM_JOINT` and
  `CALL_TYPE` open. No task, theory, index, authority or question record changed.
