# Recursive Name return: constructive origin judgment reduction

Date: 2026-10-06
Status: frozen unreviewed research-only derivation attempt; no gate closure
Gate/method: charter §22 origin classification; source derivation and necessary-premise extraction
Baseline: `bd441cc922e5bd244990f7c687fe42a245e04176`
Exclusive lease: this file only
Implementation authority: none

## Objective and result

Construct a provenance-bearing derivation for exactly

```yu
my f x = g
my g y = f
my h = f
```

with no use of `h`. The selected clauses derive Name and lambda interfaces
conditionally on a supplied recursive environment. They do not discharge that
environment into a recursive binding judgment. This is the earliest missing
premise; later generalization/use cannot supply its proof retrospectively.

The result is a necessary information contract for the missing source
judgment, specialized to the retained comparisons below. It separates source
introduction evidence from representation correspondence and from comparison
coverage. It is not a completed `Form/Generalize/MemberUse` derivation,
source acceptance result, or negative classification of `r0`, `rho_h`, or
`c_h`. No new semantic policy or user choice is established.

## Baseline, authority and dependencies

The primary fixes the semantic interpretation. Governing sections are charter
§§1–2,20,22–23; Authoritative source-result synthesis §4; integrated
`function-call-view-formation/q1` answer `a2`; and Authoritative inferred
Function call views §§1–2,5. Their relevant decisions are:

- F5 scheme shape is comparison material, not successor source meaning.
- Known Name interfaces are copied; known computation results retain their
  interface without an implicit pure wrapper.
- Source formation uses the relevant recursive component and one original
  jointly scoped assignment. Generalization/use preserve positions, annotation
  presence, scope, profiles and dependencies; admission is independent of `Q`.
- Request opening retains its witness and dependent packet fields. Hidden
  request binders and inference existentials are distinct.
- Every generated or derived comparison re-enters the introduced-existential
  guard. Levels belong to variables; constructors carry no level metadata.
  Complete comparison/extrusion coverage remains open.

The three prior notes are bounded inputs with their stated hypotheses, not
independent source-adequacy oracles. The primary's accepted current-task account
confirms their reviewed boundary; this producer does not independently review
them. The integrated receipt records a2 validation. No pending question is
consumed. `tasks/current.md`, `tasks/research-lab.md` and `notes/design/INDEX.md`
were locators/status context, not added semantic premises.

Direct frozen dependency SHA-256 values:

| Path | SHA-256 |
|---|---|
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/design/2026-10-02-source-result-synthesis-choice.md` | `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |
| `notes/progress/2026-10-06-rec-name-return-generalized-alias-source-bridge.md` | `d9911dc127a684c9a2a471d02e2513958de428cd1de5589d88bc3fb9ac85fc53` |
| `notes/progress/2026-10-06-rec-name-return-name-row-origin-transport-attempt.md` | `b7a6f86a625bb7e6047433da3512a7eda96833d0f57a124eae2d76c09295c10e` |
| `notes/progress/2026-10-06-rec-name-return-origin-rule-inventory.md` | `2f5ac6958addac1b108511493526426702b3b3ec210e90f6bd03221b77260282` |

These inputs matched the pinned baseline at inspection and final recheck.

## Actual derivation and first undischarged premise

Let `S={f,g}`. Use one provisional environment `Gamma_S` with
`Gamma_S(f)=I_f` and `Gamma_S(g)=I_g`, not separately chosen environments.
Let `P_x,P_y` denote supplied parameter interfaces; their formation is not
selected by the result-synthesis rule. The derivable fragment is:

```text
Gamma_S(g)=I_g                       Gamma_S(f)=I_f
------------------ Name             ------------------ Name
Synth(g)=I_g                        Synth(f)=I_f
-------------------------------     -------------------------------
Synth(lambda(P_x,g))                 Synth(lambda(P_y,f))
  = Fun(P_x,Result(I_g))               = Fun(P_y,Result(I_f))
```

Both bodies are Name returns, with no application to ordinary value `x` or
`y`. The approved `apply f x = f x` role-resolution example therefore supplies
no formal-role discriminator here. Nor does unused syntax prove that every
latent effect/profile/dependency field is empty.

To conclude a recursive binding formation, the fragment still needs a rule
relating `I_f,I_g` to the two definition interfaces under the same original
ledger and scope. Even setting
`I_f=Fun(P_x,Result(I_g))`, `I_g=Fun(P_y,Result(I_f))` would be a candidate
recursive-binding premise: §4 does not discharge provisional assumptions or
select recursive equality, subtyping, or a solution carrier. A2 requires a
shared solution but expressly leaves its generating judgment open.

Thus the missing edge is already

```text
two conditional body derivations
            ?
Gamma_outer |- Form(S) => (D_S, J_S)
```

and not merely a choice of a label on the later allocated `rho_h`.

If a justified `Generalize` and `MemberUse` supplied `Gamma_h(f)=I_(f,h)`,
§4 would derive `Synth(f at u_h)=I_(f,h)`. Under exactly this Name step, no
new source binder identity is introduced. This established local rule
consequence is conditional on the supplied interface; it does not classify
events in the missing preceding judgments or separately allocated rows.

## Minimum information required of the missing judgment

The following is a specification of proof inputs necessary for this origin
claim, not adopted typing rules or a mandated data structure:

```text
Gamma_outer; lexical scope
  |- Form(S); Generalize(S); MemberUse(f,u_h)
  => (D, I_(f,h), J, introduction evidence, realization evidence)
```

Its information may be encoded differently. It must nevertheless answer the
following four questions before a sound classification/preservation claim can
be obtained.

1. **What source derivation discharges recursion?** `D` must justify the
   simultaneous environment used above. `J` retains the original correlated
   `nu,K,D`, interfaces, source positions, annotation presence, paths/Flow and
   owner/receiver evidence where present. A projection or independently
   assembled port solution is insufficient. A concrete empty ledger is not
   inferred from this bare syntax.
2. **Which source step introduces a guarded variable?** For each relevant
   variable, introduction evidence identifies a source typing step or a
   justified absence of such a step, its lexical scope, and its §22 level if
   introduced. A negative certificate requires coverage of formation,
   generalization and member-use, not just the Name-copy step. Request witness
   identity, if present, travels with dependent fields under §20. An inference
   existential cannot be classified solely by the absence of an operation.
3. **What does each representation object realize?** Evidence relates `r0`,
   its use representative `rho_h`, `c_h`, and `R_h` to the relevant source
   endpoints/binders and dependent history. `r_f` stays distinct. This relation
   need not be a bijection or preserve F5's presentation. Generalization may
   change representation, but must justify the origin/scope correspondence of
   preserved, generalized and recursive dependencies; its partition is not
   selected here. Subtyping between rows is not identity of represented
   source binders.
4. **Which guarded obligation does each actual comparison carry?** A
   comparison certificate must retain its source dependency and original
   joint assignment through generation, bound restoration, alias replay,
   transitivity and any variable/extrusion steps that occur. It must explain
   which variable comparisons implement §22 after the ordinary structural
   rules. Source introduction level is not automatically allocation level or
   lexical depth. No level may be attached to `P0`, `Top`, or a Function head.

Necessity derivation: question 1 is the premise needed to use the conditional
body derivations as a binding result; question 2 distinguishes whether §22 is
applicable; question 3 transfers that distinction to the particular live
objects under discussion; question 4 is required because §22 explicitly
includes derived comparisons and §23 delegates enforcement to variable and
extrusion comparisons. These are distinct missing premises. A boolean
`not-introduced(rho_h)` alone answers neither the other rows' classification
nor preservation of an introduced variable retained as a dependency.

This is a necessary-premise reduction, not a theorem that any arbitrary record
containing these fields is sound. Each field must come from a justified source
judgment and its correspondence proof. Encoding the answers in a checker would
only check consistency of the supplied answers.

## Exact comparison obligations retained

Use the prior accepted production map, without re-auditing compiler code:

```text
c_h   = occurrence value row at u_h
R_h   = h definition root
r_f   = f definition root
rho_h = use row substituted for legacy recursive binder r0
L_h   = P0(Top-, P0(Top-, rho_h+))
```

The original direct edge and four incoming/replay shapes remain separate:

| Comparison | Provenance that the missing judgment must explain |
|---|---|
| `c_h <: R_h` | Name expression to its own definition root; origins/dependencies of both rows |
| `L_h <: rho_h` | Restored recursive lower side; correspondence of `r0`, its bound and `rho_h` |
| `rho_h <: Top-` | Restored upper side; actual variable comparison/extrusion treatment without giving `Top` a level |
| `L_h <: c_h` | Incoming member interface to this occurrence; shared substitution and complete caller assignment |
| `L_h <: R_h` | Replay using `L_h <: c_h` and `c_h <: R_h`; guard re-entry before committing this derived obligation |

In the reviewed finite unused-alias production envelope there is no
Function/Function decomposition and no derived `rho_h <: v`. This note adds
neither. Nevertheless, the exact handling of a structural bound versus a
variable is an unproved variable/extrusion coverage obligation. In particular,
the table is not authorization to check every Cartesian pair of nested
variables in `L_h` and another endpoint: that candidate coverage rule is not
selected by §§22–23. Nor may a row comparison skip the guard merely because
its other operand has a constructor head.

Conditional implication only: if the missing source judgment supplies complete
origin/realization evidence, and a separately justified §22/23 implementation
accounts for each actual comparison and every derived step, then classifications
and guard outcomes certified by those premises transport to this alias. This
does not establish those premises or permission law `(L)`. Requiring them is
not a source rejection rule.

## Stopping condition and next action

The earlier attempts already left source origin unresolved. This attempt stops
at the source discharge premise rather than supplying another origin-free
graph completion. No selected clause in the bounded governing set discharges
`Gamma_S`, introduces a successor recursive binder, or supplies member-use
introduction evidence. Absence from this set is not an exhaustive assertion
about every historical file.

No semantic counterexample is claimed. The assignment's falsifier is met in
the limited sense that an indispensable premise is absent from the selected
clauses. It does not prove that the user must choose a new language meaning:
the selected formation direction expressly leaves these rules as the next
design/proof obligation. Introducing blanket guarding/exemption, an ordinary
lookup opening, or a new recursive acceptance restriction would add semantics;
this note supplies none of them.

Recommended next action: have the primary adjudicate the exact missing recursive
environment-discharge judgment under the existing formation gate, including
introduction evidence, before another origin-classification experiment. Keep
variable/extrusion coverage as a separate dependency rather than completing
it by an assumed nested-support guard.

## Checks, resources, coverage and limitations

Read the three required rules in full, the exact governing sections, integrated
a2/receipt and relevant prior-note sections. Commands were bounded `cat`,
`sed`, `rg`, `git rev-parse HEAD`, scoped
`git diff --name-only BASE -- <dependency paths>`, `sha256sum`, and final
leased-file scope/whitespace inspection. Dependencies matched the baseline.
An initial aggregate prior-note capture and a locator search were truncated;
sections used above were subsequently read narrowly. No exhaustive repository
search was attempted.

There is no executable oracle, seed/range, enumeration, or executed mutation
campaign. Authority clauses are independent of any proposed checker, but this
derivation shares their supplied-interface premise and the prior accepted
production trace's finite-envelope assumptions. Formation, representation
correspondence and variable/extrusion coverage remain unproved. No own or jointly
authored output is independently certified.

No tests, builds, probes, compiler or `cfg(test)` edits, manifests, lockfiles,
formatters, Git mutations, child agents or interactive questions. At most five
lightweight read processes were batched concurrently; heavyweight process count
was zero. CPU/RAM peaks and total wall time were not instrumented. The packet
supplied a qualitative small-static-read budget, not numerical limits. The sole
written output is this leased note.

Unverified scope includes recursive source acceptance, exact formation and
generalization/use rules, source-to-row origin realization, principal inference,
production denotation/admission, full `(L)`, failure ownership, `h`
generalization/publication, alias uses, applications, annotations, additional
aliases and mixed member/outer boundaries. Dependency changes, hidden source
openings, discarded joint scopes or unproved structural coverage invalidate
any attempted promotion of this conditional result.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-rec-name-return-origin-constructive-next.md`.
- Baseline SHA: `bd441cc922e5bd244990f7c687fe42a245e04176`.
- Changed dependency hashes: none; frozen hashes are listed above.
- Claim/review status: frozen unreviewed research-only necessary-premise
  reduction and partial derivation; no independent certification, source
  theorem closure or implementation authority.
- Checks already run: governing-section inspection, baseline/dependency equality,
  dependency hashing, exact leased-file scope and whitespace inspection;
  no executable checks.
- Proposed one-line research-checkpoint commit message:
  `research: reduce recursive Name origin derivation to source discharge`.
- Shared-record deltas intentionally left for the primary/curator: record that
  recursive environment discharge is the earliest missing derivation premise;
  retain separate source-introduction, live-realization and variable/extrusion
  coverage obligations, with the direct edge and all four incoming/replay
  shapes. No task, index, authority, theory map or question bundle was edited.

Writes stopped before submission; this artifact is frozen for review.
