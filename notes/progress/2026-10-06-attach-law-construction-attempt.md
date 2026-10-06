# Attach law: constructive attempt at original contribution typing

Date: 2026-10-06
Baseline: `1868c9bee71cf6759b7d85542ab7374d1078ab7d`
Status: frozen, compiler-referee-reviewed research-only derivation attempt; no findings in scope
Method: backward construction of the dependent attachment judgment
Exclusive lease: this note only
Semantic and implementation authority: none

## Objective and bounded result

Starting from the reviewed complete Call operand, attempt to construct the
original association `(beta,s0,p0,c0)` and type its contribution. The result
is a **bounded localization of the first unproved judgment**, rather than a
new attachment theorem. The source can construct the address, protection
origin and complete invocation expression. The inspected source/core rules
do not supply the original owner/view kernel's contribution typing and slot
association at that expression. No source counterexample or semantic
alternative is established.

This attempt does not rerun the complete operand derivation, enumerate toy
profiles, inspect production implementation or consult Oracle. It checks
whether the existing constructor, checking and typed transport rules can
provide the missing dependent premise. Their typing/checking conclusions
concern a computation or a supplied packet, whereas the requested conclusion
concerns an original source-owned signature incidence.

## Baseline, authority and hypotheses

The primary pinned the baseline above and the following decisions: one
source-generated shared contract; stable beta/Slots identity; one original
`xi=(nu,K,D)`; admission independent of pending Q; no Oracle authority;
and the exact nested-block meaning already selected by the user.

Governing sections read directly:

- [Inferred call views](../design/2026-10-05-inferred-function-call-views.md)
  §§1–5: the source/public/internal separation, shared contract and original
  scope, Q-independent formation, and open exact construction judgments.
- [Directional protection](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
  §§2–4: own-upper protection, no lower backflow, and the separation of
  protection witnesses from contribution membership and receipt.
- [Nested source meaning](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
  §§1–3: sequential binding, inert return of step and the same outer f capture.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2–3.2, §6.1, §§8–10: independent primitive/owner/view inputs; supplied
  decorated source; constructor images; coverage distinct from the retained
  non-coverage kernel and production Option 2 extras.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §§2–3, §6's interface/parameter/structural subsections, §7's Function-entry
  subsection, §9's entry subsection: symbolic
  interfaces and complete invocation; supplied typed contracts remain inputs.
- [Typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md)
  §6's introduction/transport subsections: profiles supplied by elaboration;
  indexed packet images preserve original incidences and their predicates.

Reviewed research inputs are the
[complete operand construction](2026-10-06-attach-call-contribution-construction.md)
§§2–6, [licensing factorization](2026-10-06-original-signature-licensing-construction.md)
from its explicit hypotheses through first unclosed leaf,
[source Call construction](2026-10-06-source-call-generation-construction.md)
§§3–5 and §7, and [constructor inversion](2026-10-06-original-signature-constructor-derivation.md)
from its Call obligations through leaf retention. Their reviewed status is an
input fact, not independent review of this note.

Fix C as `my apply f = { my step x = f x; step }`, the original binder tree,
and one candidate whole row X. X contains xi, U, actual providers, environment,
world/current configuration, continuation and retained obligations. X need
not be satisfiable or admitted. Local witnesses stay beneath the original
rigid dependencies. H consists of the approved core correspondence, lexical
resolution, ordinary symbolic constructors, unannotated seed and same-root
seed-at-exposure witness. Interpreting execution additionally retains the
independent decorated primitive/provider/entry contracts.

Under H the predecessor constructs:

```text
beta = (d_f,R)
p0 = (beta,call.effect) = outEff(U)
e0 = (k,beta,u,sigma_x,p0)
ElimOrigin(c_fx,u,d_f,R,p0,p_out(c_fx))
NewProtection(e0)
J_f = ReturnImage(Name(d_f), original environment)
J_x = ReturnImage(Name(d_x), original environment)
j_call = rooted expression record for
    J_f >>= (lambda actual_f. ExecuteCallable_X(actual_f,Delay(J_x);U,e))
```

The predecessor retains actual entry, body, designated consumer, return and
all pending suffixes in j_call. J_x is the inner rebound Name return, not the
external carrier entering step. These statements do not produce an original
contribution-typed c0 or identify a signature slot s0 with p0.

## Backward derivation and the first missing judgment

The requested target has the licensing predecessor's incidence sort:

```text
Attach_C(X,e0,t0)       t0 = (beta,s0,p0,c0)
s0 : original static signature slot
c0 : original complete contribution witness/contract
```

Use the following notation only for the **missing proof obligation**:

```text
OriginalAssocType_X(beta,p0,j_call; s0,c0)
```

It asks for the original signature/owner/view interpretation to type c0 and
associate it and s0 with this source occurrence, typed position and complete
operand. The judgment retains the original scopes, complete invocation
dependencies and own-upper versus inherited provider/result tags. It is not
a definition of an existing kernel predicate, a new accepted clause or a
conjunction declared sufficient by this note. Whether the actual kernel uses
one judgment or several is a representation choice; the semantic obligation
must be supplied independently in either representation.

Backward construction reaches this unfinished tree:

```text
H
-------------------------------- reviewed source-prefix construction
a_call(X), e0, ElimOrigin, p0, j_call

??? source constructor over the same C, X and original dependencies
-------------------------------- missing original kernel interpretation
OriginalAssocType_X(beta,p0,j_call; s0,c0)

a_call(X)    OriginalAssocType_X(beta,p0,j_call; s0,c0)
-------------------------------- Attach-Call candidate, not established
Attach_C(X,e0,(beta,s0,p0,c0))
```

The missing middle judgment occurs before proving forward licensing or
exhaustive inversion. Source-owned s0 association and contribution typing are
coupled requirements of that entry; this proof does not assume that their
construction has an order, that one exposure owns exactly one entry, or that
an entry entails a complete Slots inventory. If attachment is relational,
the displayed s0,c0 are one local witness under X, without a functional-choice
claim.

The following possible last-rule routes fail at that specific premise:

| Available route | Conclusion available | Why the middle judgment remains |
| --- | --- | --- |
| Gen-Call-0 | Original contract/address and complete-elimination correspondence | It has no contribution-typing or original slot-table conclusion. |
| Dir-Protect | Protection at the original own-upper output | Protection is explicitly distinct from contribution membership and receipt. |
| Symbolic Call interface | Emit complete image inclusion and `TypedCallCert_Dec` obligations | Emission does not construct the supplied original kernel input retained by the certificate. |
| Solved decorated Call certificate | Interpret the complete call with supplied typed profile/receipt/correspondence premises | Inverting it recovers those supplied inputs; no displayed rule makes them the original source association. |
| Typed packet transport | Image an existing tagged incidence, preserving K,D and origin | Membership inversion recovers an input incidence; it cannot construct a missing own-beta input. |
| Source-allocation Call rule | Cover callee evaluation and complete receiver output | §6.1 retains the whole non-coverage kernel and does not type a new original signature contribution. |

This is a bounded last-rule analysis of the inspected routes. It is not an
impossibility theorem about future source constructors or the whole repository.
In particular, ordinary source elaboration could be extended with the missing
original clause, under the primary's authority process.

## Why fresh unknowns do not discharge the leaf

The positive constraint-generation result remains intact. A generator may
introduce dependent unknowns s,c and retain an original association constraint,
just as it introduces U before solving complete Call constraints:

```text
exists_original_scope(s,c).
    ExistingCallObligations(X)
  & OriginalAssocType_X(beta,p0,j_call; s,c)
```

This is a **candidate demand expression** until that predicate has an
independent interpretation and its source construction law is established.
Writing it does not prove witness existence, correctness of its interpretation,
or equality with independently interpreted original source solutions. Nor does
failure to prove an admitted X prevent generation of the expression. The open
leaf is consequently the interpretation and source introduction law, rather
than a demand to solve the Call first.

A constructor typing lemma for ordinary `Comp(E_c,A_c)` cannot alone replace
this contribution typing lemma: its conclusion checks a computation interface
on supplied typed inputs, and does not assign the original `(s,c)` coordinates.
An equation `c0=j_call` or `s0=p0` would bypass that distinction by assuming
the very correspondence sought. This note makes neither equation.

The licensing predecessor's theorem remains conditional on the independently
interpreted attachment and original licensing laws:

```text
A_sound:  Attach_C(X,e0,t) => Lic_C(X,t)
A_invert: Lic_C(X,t) => Attach_C(X,e0,t)
```

Neither implication is newly proved. The direct exposure singleton `{e0}` is
reused and supplies no closed inventory of original licensing last rules.

## Independence, discriminators and stop condition

No Oracle evidence or checker is used. The backward derivation shares H and
the decorated semantic inputs with its predecessors. It independently exposes
neither their source truth nor a complete admitted row. An executable checker
assuming OriginalAssocType's introduction rules would test those rules against
themselves; it would not prove their source interpretation.

Logical mutations identify proof failure conditions, without executed counts:

- Set c0 to an outward effect set: discards complete invocation, pending suffix
  and original contribution identity.
- Cast j_call to c0 without an interpretation lemma: fills the open sort and
  typing leaf by assumption.
- Use identity of p0 and s0 without a slot interpretation: fills the other
  association coordinate by representation convention.
- Import an inherited provider incidence and retag it own-beta: loses source
  provenance and can reverse the selected no-backflow direction.
- Create the association from Q success or independently chosen xi/world:
  violates Q independence or the original whole-row correlation.
- Treat emission of the association obligation as its proof: mistakes a
  generated residual demand for source validity.

A future independent kernel clause makes the local discriminator precise:
does its source derivation provide the original contribution-typed entry at
this j_call and p0, with its own source tags and same X? An entry licensed
without an originating attachment refutes A_invert; an attached unlicensed
entry refutes A_sound. No X,t realizing either discriminator was constructed.
There is no minimized language rejection witness or competing source meaning.

The licensing and complete-operand attempts already left this same premise
open. This attempt therefore stops here rather than supplying another Call
execution model or a larger arbitrary-profile search. The next different
method is to specify and audit the original owner/view contribution typing
clause itself, then attempt its local source constructor and inversion. That
clause must be independently interpreted; calling it OriginalAssocType alone
does not provide it.

## Checks, dependencies, resources and unverified scope

Read-only commands: `git rev-parse HEAD`, `git status --short`, bounded `cat`,
`sed -n`, `rg -n`, and Python SHA-256/byte comparisons against
`git show 1868c9bee71cf6759b7d85542ab7374d1078ab7d:<path>`. Initial aggregate
captures truncated; all decisive governing/contribution sections were reread
in bounded windows. No absence claim rests on a whole-repository search.

Fourteen direct dependencies matched the pinned bytes at the initial and
handoff checks: AGENTS; the three rules named by the
assignment; the six design documents linked above; and the four research
inputs linked above. Ancillary task/index reads located the current gate and
do not supply semantic premises. Their concurrent changes are not dependency
changes to this derivation.

All relative note links resolve. `git diff --no-index --check /dev/null` on
the note emitted no whitespace diagnostics (exit 1 denotes the added file).
HEAD remained the pinned baseline at handoff. Concurrent edits in two
yu-core shadow paths were observed and left untouched; neither is a premise.

No code, tests, builds, Oracle, checker, executable search, formatting, Git
mutation, child delegation or scratch output. Seeds/ranges, runtime mutations
and performance samples are inapplicable. One output path is consumed;
heavyweight process count is zero. No numeric CPU/RAM/wall-time limit was
supplied. CPU time, peak memory and elapsed time were not instrumented.

Unverified scope: the original association interpretation/introduction;
contribution typing; both licensing directions; complete Slots/profile,
nonemptiness and initial/history admission; general annotations, multiple uses
and recursion; principality and production Option A/2 conformance. No shared
task, index, theory, authority or question files were changed.

Recommended next action: have the primary obtain an independently interpreted
original owner/view contribution typing clause for the displayed middle
judgment, then assign its one-Call introduction/inversion proof.

## Commit packet

- Exact leased/changed path:
  `notes/progress/2026-10-06-attach-law-construction-attempt.md`.
- Baseline SHA: `1868c9bee71cf6759b7d85542ab7374d1078ab7d`.
- Changed dependency hashes: none at both fourteen-input byte checks.
- Review status: compiler-referee-reviewed bounded derivation attempt, no
  findings in scope; no closed attachment theorem or authority. Reviewer did
  not independently verify baseline byte equality or reported checks.
- Checks already run: exact source/rule reads; backward judgment/sort and
  same-X audit; initial/handoff fourteen-input pinned byte/hash comparisons;
  lease-path absence, relative-link integrity and note-local diff check.
- Proposed one-line research-checkpoint commit message:
  `research: isolate original contribution typing in Attach law`.
- Shared-record deltas intentionally left for primary/curator: optionally link
  this bounded attempt to the existing open `(s,c)` association; retain both
  licensing directions, complete profile/admission and production gates.
  No theorem-status promotion or new semantic choice is proposed.

Research writing stopped before independent review; primary retains
adjudication and integration ownership.
