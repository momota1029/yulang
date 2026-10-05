# Recursive Name return: generalized alias source bridge

Date: 2026-10-06
Status: frozen unreviewed research-only conditional derivation; no gate closure
Method: source judgment factorization for one generalized member use
Baseline: `ee9bc4bdf03bfe76be2d56aed86844f7a38e73cd`
Lease: this file only; no code, tests, probes, or implementation authority

## Objective and result

For exactly

```yu
my f x = g
my g y = f
my h = f
```

with no use of `h`, supply the source interface of the last Name occurrence
from the recursive component's generalized member interface. Continue the
reviewed Name-row transport result without repeating its HIR mapping.

The selected Name rule derives the occurrence interface once a member-use
judgment supplies `Gamma_h(f)`. The approved a2 direction fixes joint contract,
static identity, and scope preservation as requirements on that judgment.
It expressly does not supply the judgment, its origin-bearing inputs, or a
realization of the legacy recursive binder. Therefore no unconditional source
interface assignment or classification of `rho_h` is derived. The useful
reduction is a two-part missing bridge: source generalization/member-use
transport, then origin-complete realization of `r0/rho_h`. Neither part can be
replaced by static slot/profile preservation or value-relation equivalence.

## Authority and frozen dependencies

The assignment fixes these governing sections and accepted decisions:

- Charter §§1–2: legacy F5 schemes are comparison material; their closed
  scheme shape is not the successor target. F4's Integer/Name infrastructure
  does not select recursive Function or effect generalization.
- Charter §20: request opening retains dependent binder/witness correspondence;
  aliases cannot split that witness. Hidden request binders and solvable
  inference existentials are distinct. Lifecycle preservation remains open.
- Charter §§22–23: introduced-existential guards re-enter every derived
  comparison; levels belong to variables. Exact coverage and preservation
  remain obligations, with no blanket rule about fresh allocations.
- Authoritative source-result synthesis §4: `Gamma(x)=I` gives
  `Synth(name x)=I`; lambda result synthesis preserves known source positions.
- Authoritative inferred-call-view §§1–2,5 and integrated q1/a2: relevant
  declarations/definitions/uses/recursive components form a shared contract;
  generalization/use preserves source identities and scope. Complete admission
  is independent of pending comparison `Q`. Exact construction and transport
  judgments, uniqueness/principality, and production conformance remain open.

`tasks/current.md` fixes the current gate and accepted production facts. The
reviewed Name-row note supplies the occurrence seam; the reviewed member-use
note supplies only its explicitly conditional value-relation comparison.
The origin inventory supplies the previously isolated missing source rule.
No new compiler audit is performed and no pending question is consumed.

All nine direct dependency paths matched the baseline at inspection:

| Dependency | SHA-256 |
|---|---|
| `tasks/current.md` | `6179c0f37b1c9fb34bccf877ecf769f12c4884d1649bc5806e7a7f10ff624631` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/design/2026-10-02-source-result-synthesis-choice.md` | `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |
| `notes/progress/2026-10-06-rec-name-return-name-row-origin-transport-attempt.md` | `b7a6f86a625bb7e6047433da3512a7eda96833d0f57a124eae2d76c09295c10e` |
| `notes/progress/2026-10-06-rec-name-return-member-scheme-bridge.md` | `fea42929e591c160d8a92edcb4f103254fb2726feef0be58ca747fb7075cf84e` |
| `notes/progress/2026-10-06-rec-name-return-origin-rule-inventory.md` | `2f5ac6958addac1b108511493526426702b3b3ec210e90f6bd03221b77260282` |

The candidate 2026-09-30 SCC constraint-scheme note was read to distinguish its
assumed graph/use semantics. It contributes no premise here: substituting its
all-local partition, existential root projection, or freshening rule would
choose the missing semantics rather than derive them. The other prior notes
above already record that candidate's status and comparison limits.

## What the selected rules construct

Write `S={f,g}` and `u_h` for the final occurrence of `f`. Assume temporarily
that a recursive source environment `Gamma_S` has already been supplied with
interfaces `I_f,I_g`. With separately supplied parameter roles `P_x,P_y`, §4
constructs these synthesis steps:

```text
Gamma_S(g)=I_g              Gamma_S(f)=I_f
------------------         ------------------
Synth(name g)=I_g           Synth(name f)=I_f

Synth(lambda(P_x,name g)) = Fun(P_x,Result(I_g))
Synth(lambda(P_y,name f)) = Fun(P_y,Result(I_f))
```

This derives the two expression interfaces conditional on the supplied
environment. It does not derive that the recursive definitions bind those
interfaces, choose self/export endpoints, introduce recursive source binders,
or solve the simultaneous assignment. Setting `I_f` and `I_g` equal to those
expression interfaces would add a recursive binding rule not present in §4.
Putting independently selected profiles on the two expressions would also
violate a2's one jointly scoped assignment requirement. No recursive equality,
root-lens projection, or existential classification is inferred here.

For the alias, the exact selected derivation has the form

```text
MemberUse(S,f,u_h) supplies Gamma_h(f)=I_(f,h)
------------------------------------------------  prerequisite, still open
Gamma_h(f)=I_(f,h)
---------------------------  selected Name synthesis
Synth(name f at u_h)=I_(f,h)
```

The lower rule contributes no new source binder. It preserves any binder,
profile, or dependency already present in `I_(f,h)`. It does not determine
whether the preceding `MemberUse` opens or instantiates anything. Binding
that expression to `h`, classifying its occurrence row, and later generalizing
`h` are separate judgments; only the first source occurrence is studied here.

## Smallest conditional generalization/use bridge

The following notation names missing judgments; it does not adopt their rules:

```text
Gamma_outer |- Form(S) => (D_S, J_S)
(D_S,J_S) |- Generalize(S) => Sigma_S
Gamma_outer; Sigma_S |- MemberUse(f,u_h) => (I_(f,h), J_h, T_h)
```

`D_S` is a source derivation with a simultaneous environment assignment.
`J_S` is its complete joint ledger. `Sigma_S` is a generalized interface with
the member correspondence required to supply `f` at this use; it need not be
an F5 closed scheme. `T_h` is the use's transport/realization evidence. A
minimal sufficient conditional bridge has three hypotheses:

H1. **Origin-bearing formation.** `D_S,J_S` exist and specify the source
interfaces, binder/introduction history, lexical scope, and original correlated
constraints. Every relevant source identity and dependent occurrence is
accounted for. In particular, the predicate “introduced under §22” is derived
from source typing, not inferred from a constructor, allocation, or level.

H2. **Generalization and member-use preservation.** The two latter judgments
supply `I_(f,h),J_h,T_h` and preserve the jointly scoped relationships selected
by a2, with an explicit treatment of generalized identities, preserved outer
identities, recursive references, and any source introductions at this use.
No relevant obligation is independently solved and pasted into another port;
no introduction is silently added or removed. This does not require a
bijective renaming of every type variable: a representation may use a
different recursive presentation, but then must prove its correspondence.

H3. **Origin-complete R realization.** For this exact use, the evidence contains
a judgment of the following shape:

```text
D_S; Sigma_S; (I_(f,h),J_h,T_h)
  |- Realize_R(r0 at f-member, rho_h at u_h) => C_h
```

`C_h` relates the legacy binder and its restored bounds to the appropriate
source recursive reference or representation. It states whether `rho_h`
represents a §22-introduced variable, which other introduced variables it
depends on, and how their original scopes/witness correspondence survive.
It must account for the complete representation and any opening in the use
judgment. It cannot merely equate erased values, rename `r0` to `rho_h`, or
claim identical levels. This is a correspondence obligation, not a new
source opening or exemption rule.

**Conditional conclusion.** H1–H2 and the selected Name rule give exactly
`Synth(u_h)=I_(f,h)` with the supplied joint correspondence preserved and no
additional source introduction in that Name step. H3 gives precisely the
classification it certifies for `rho_h`; it is not generated by this theorem.
If H3 certifies that `rho_h` represents no §22 introduction, that particular
classification follows conditionally. Any retained dependencies on introduced
variables still require their own §22/23 comparisons. A full negative origin
classification additionally requires H1/H2 to certify the relevant source
origins and use events; no such certificate is currently supplied.

Proof: use H2 to supply the Name premise, apply selected §4, and retain the
same joint ledger and evidence by H2. Apply H3 only to its named representation.
The proof neither constructs H1–H3 nor verifies guard/extrusion preservation.
Its claim is a conditional judgment composition, not source adequacy.

## Why value and slot correspondence do not fill H3

a2 closes a design choice: generalization/use must preserve the source
component's shared relationship, static `beta`/`Slots(beta)`, annotation
presence, and lexical scope. These are necessary constraints on H2. It does
not construct the slot inventory for this source or certify a particular
profile. In particular, “no callback call appears here” is not a proof that
all nested inventories are empty.

A static slot or transported profile can keep the same source position while
its type variables require a separate source binder/instantiation derivation.
The protected Handler seed in the approved `apply f x = f x` example supplies
no origin classification for this top-level recursive `f`: names coincide,
but there is no ordinary-value call evidence in this gate. Likewise, the
static position is not a dynamic receiver activation.

The reviewed member-use comparison is insufficient for a second, concrete
reason. Under its H1–H4 candidate preorder assumptions, the forward witness
transformation chooses `rho=F(s_g)`; it does not identify `rho` with `s_g`,
`s_f`, or an exported root. Equality of the projected member relation thus
does not provide a source binder map even in that conditional carrier. It
also does not preserve the simultaneously exposed root pair. Reusing that
algebra as H3 would need new origin, profile, and scope correspondence proofs.
No such map is inferred from `R`, freshness, equal levels, or the witness shift.

## Retained joint dependencies and boundary

The bridge must retain the two definitions' correlated source derivation,
their internal Name references, parameter and result interfaces, any outer
anchors, binder scopes and introduction history, and the original `nu,K,D`,
typed paths/Flow and owner/receiver incidences when present. H2 does not assert
that every identity is generalized or that different member views have one
identical quantifier partition. Those choices remain unspecified.

For production correspondence the prior reviewed facts remain exactly
`c_h <: R_h`, incoming `L_h <: c_h`, and replay `L_h <: R_h`, with
`L_h=P0(Top-,P0(Top-,rho_h+))`, restored `L_h <: rho_h` and
`rho_h <: Top-`. The occurrence `c_h`, alias root `R_h`, target root `r_f`,
and fresh recursive substitution `rho_h` remain distinct. Their caller
assignment, direct edges, and restored bounds cannot be discarded to classify
one variable. This note supplies neither denotation for these comparisons
nor the prior note's missing occurrence-row realization. No reverse
`c_h <: r_f` is used.

The precise blocker is the absent provenance-bearing recursive
formation/generalization/member-use judgment, followed by its R realization;
a2 explicitly retains those proof gates. A larger toy graph or another
origin-free completion would leave this premise untouched. The next method
should construct the missing source judgment rather than extend such probes.

## Checks, resources, omissions, and failure conditions

Read the three required rules in full and the exact governing sections and
integrated answer/receipt. Used bounded `cat`, `rg`, `sed`, `git rev-parse
HEAD`, scoped `git diff --name-only BASE -- <nine dependencies>`,
`sha256sum`, and final leased-path integrity/dependency inspection. Initial
HEAD matched the baseline and the dependency diff was empty. Some initial
batched locator/rule output was truncated; used authority sections and the
required design/Git rules were reread narrowly. This is a bounded inventory
of named sources, not an exhaustive historical absence proof.

No executable oracle, seeds/ranges, finite enumeration, or executed mutation
campaign. The deduction is grounded directly in the selected source rule,
independent of an assumed transition checker. H1–H3 are shared assumptions of
the conditional bridge and are not proved by its composition. Prior production
and member-relation notes are documentary evidence with their own shared
premises; they are not independent source-adequacy oracles. No own/joint output
is independently certified here.

No code, tests, builds, probes, formatter, children, interactive questions,
Git mutations, or shared-record writes. At most four lightweight read shell
processes ran concurrently; heavyweight process count was zero. CPU/RAM peaks
and total wall time were not instrumented; no numerical resource budget was
supplied. The sole output is this leased note.

Unverified: H1–H3; source assignment/acceptance of the recursive group;
occurrence-row realization; complete §22/23 coverage and preservation;
production denotation/admission, principal inference, diagnostics/failure
ownership, `h` generalization/publication, applications, annotations, mixed
member boundaries, and arbitrary caller inventories. No selected meaning,
production route, or test contract is changed.

Failure conditions: selected rules or dependent artifacts change; member-use
transport loses a joint constraint or original scope; a hidden source opening
is omitted; R realization identifies a representation variable with a source
binder without evidence; or value/slot equality is used to manufacture origin
authority. The conditional bridge cannot validate its own premises.

Recommended next action: construct and review one provenance-bearing source
`Form/Generalize/MemberUse` derivation for this exact component/use, exposing
its R correspondence and introduction events before attempting classification.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-rec-name-return-generalized-alias-source-bridge.md`.
- Baseline SHA: `ee9bc4bdf03bfe76be2d56aed86844f7a38e73cd`.
- Changed dependency hashes: none; nine direct hashes are pinned above.
- Review status: frozen unreviewed research-only conditional derivation;
  no independent certification, gate closure, or implementation authority.
- Checks already run: authority and prerequisite section inspection, baseline
  and scoped dependency equality, dependency SHA-256 capture, final leased-path
  scope and integrity inspection. No executable semantic checks.
- Proposed one-line research-checkpoint commit message:
  `research: isolate generalized alias source and R realization bridge`.
- Shared-record deltas left for the primary/curator: distinguish a2's selected
  preservation requirement from an established source generalization/use
  rule; retain H1–H3 and the independent occurrence realization/guard gates;
  record that conditional member-value equivalence supplies no R origin map.

Writes stop before submission. The note is frozen for independent review.
