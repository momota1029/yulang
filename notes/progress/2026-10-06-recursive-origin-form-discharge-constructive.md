# Recursive origin formation: the missing discharge rule

Date: 2026-10-06
Status: frozen unreviewed research-only partial derivation and bounded rule audit
Gate/method: recursive source environment discharge; last-rule inversion
Baseline: `ba35b1b1341fe70f4445675e0d4c5d664c7c4875`
Exclusive lease: this file only
Implementation authority: none

## Objective, result and claim class

Attempt to discharge the provisional environment for the selected source:

```yu
my f x = g
my g y = f
my h = f
```

`h` is unused. The method is static backward derivation: identify the required
conclusion, invert the selected rules, and stop when no inspected rule supplies
that conclusion. No new graph model or origin propagation checker is supplied.

The result is a bounded derivation obstruction, not source rejection or theorem
closure. The available Name/lambda/Result rules derive two definition interfaces
under assumptions about `f,g`; none discharges those assumptions into a recursive
`Form(S)` judgment. Even granting all parameter-origin premises does not fill
that rule hole. Without that grant, an origin-bearing proof additionally lacks
classification of the fresh parameter endpoints. These are distinct frontiers;
discharge is the first missing conclusion rule on this chosen derivation spine,
not a claim about a unique first hole in every possible proof ordering.

## Baseline and exact governing sections

The primary selected the interpretation. The direct governing clauses are:

- [Result synthesis §4](../design/2026-10-02-source-result-synthesis-choice.md):
  Name copies a supplied interface; lambda constructs `Fun(P,Result(I))`;
  ordinary Value results obtain a pure computation wrapper and known
  Computation results retain their interface. Sections 3 and 5 retain
  correlated profiles/`K,D` and leave recursive checking/generalization open.
- [Charter §§1–2,20–24](../design/2026-09-29-scc-intrusion-redesign-charter.md):
  successor meaning is not F5 scheme shape; request opening retains its joint
  witness; ordinary unannotated parameters have fresh inferred Value endpoints;
  every derived comparison re-enters the existential guard; only variables
  carry levels; ordinary unannotated literals have Pure role. The charter's
  overall Reviewed status does not promote its unselected proposals; the named
  user-selected amendments govern their stated scopes.
- [Inferred Function call views §§1.1–2,5](../design/2026-10-05-inferred-function-call-views.md):
  relevant recursive components supply one shared source relationship and one
  original jointly scoped `nu,K,D`; positions, annotation presence and scope
  survive generalization/use; admission is independent of comparison `Q`.
  Exact generation judgments remain open. Integrated
  `function-call-view-formation/q1` answer `a2` and its receipt confirm this
  selected direction, without supplying completed rules.
- [Experimental transport, scope and bounded gate](../design/2026-10-04-intrusion-experimental-transport.md):
  source identities, member bounds and roots are inputs; transporting evidence
  does not certify its validity.
- [Collection foundation, Deferred semantic gates](../design/2026-09-20-constraint-collection-scc-foundation-draft.md):
  recursive Function skeletons, freshening and generalization variables are
  deferred. Charter §2 also bounds the inherited F4 authority to its
  Integer/resolved-Name scope.

The two starting research notes are dependencies, not new source rules:
[constructive reduction](2026-10-06-rec-name-return-origin-constructive-next.md)
and [reviewed authority closure](2026-10-06-recursive-name-origin-authority-closure.md).
Their supplied-origin conservation, finite-copy limit and retained guard seam
are preserved. This producer does not independently certify those notes.
`tasks/current.md`, `tasks/research-lab.md` and `notes/design/INDEX.md` were
locators/status context only. No unintegrated question was consumed.

Direct dependency SHA-256 values at the pinned baseline:

| Path | SHA-256 |
|---|---|
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/design/2026-10-02-source-result-synthesis-choice.md` | `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-04-intrusion-experimental-transport.md` | `b9eeaa4c014e98f0e2790208030a6cccf48e6efcfb05c2d46effd27caff25c96` |
| `notes/design/2026-09-20-constraint-collection-scc-foundation-draft.md` | `37a2799288db0081cf3f32c7f6860c376ff0b2ce3249397cd9c23c7a89fedeaa` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |
| `notes/progress/2026-10-06-rec-name-return-origin-constructive-next.md` | `98c5214a39c57201c5d93506a10e18de9672f4f0b9951ee88ddd124fd12b5827` |
| `notes/progress/2026-10-06-recursive-name-origin-authority-closure.md` | `4ce4ce98c4c5f2091c820d90f95c0855addba2564f79d53e59cc7d0cb2b65a31` |

These dependencies matched their pinned bytes when inspected and at submission.

## Partial derivation with hypotheses exposed

Write `S={f,g}` and fix resolved names and lexical scopes. Hypothesis H1 supplies
one provisional environment
`Gamma_S=Gamma_outer[f:I_f,g:I_g]`, with supplied interfaces `I_f,I_g` retaining
their source positions and original joint dependencies. H1 is an assumption
for body synthesis; it is not evidence that recursion has already formed.

Charter §21 selects distinct fresh inferred endpoints `A_x,A_y` for the two
ordinary parameters and their interfaces `P_x=Value(A_x)`, `P_y=Value(A_y)`.
The selection does not certify `Ex(A_x,l)` or its negation, nor any introduction
level. Hypothesis H2, when needed for a fully origin-bearing partial tree,
supplies such evidence and its correspondence. H2 is explicitly unproved.
Charter §24 selects the ordinary literal role independently of these endpoint
classifications. No body application invokes the special `apply f x = f x`
formal-role-resolution example.

Let `Gamma_x=Gamma_S[x:P_x]`, `Gamma_y=Gamma_S[y:P_y]`. The selected synthesis
fragment, with environment dependence displayed, is:

```text
Gamma_x(g)=I_g                          Gamma_y(f)=I_f
---------------- Name                 ---------------- Name
Gamma_x |- Synth(g)=I_g                Gamma_y |- Synth(f)=I_f
-------------------------------       -------------------------------
Gamma_S |- Synth(lambda x.g)           Gamma_S |- Synth(lambda y.f)
             = Fun(P_x,Result(I_g))                 = Fun(P_y,Result(I_f))
```

These equations abbreviate the selected source-position-preserving rules.
They do not select a recursive equality carrier, solve role/effect structure,
or prove endpoint allocation is a §22 introduction. Result wrapping forwards
supplied origins; it supplies no recursion binder or package opening.

The next required conclusion would have the shape

```text
Gamma_outer |- Form(S) => (source derivation D_S, joint assignment J_S)
```

`Form,D_S,J_S` are proof placeholders for the demanded source judgment and
evidence, not adopted language syntax or compiler fields. Both conditional
lambda derivations still rely on `Gamma_S`; ordinary implication does not
erase H1. The derivation stops here.

## Last-rule inversion and the smallest residual

Consider the bounded set of explicit source rules just inspected. A finite
derivation of the demanded conclusion would require a final rule whose
conclusion supplies recursive component formation and discharges the member
assumptions. Inspect its possible last step:

| Selected clause | Why it does not conclude this judgment |
|---|---|
| Name | Its premise already supplies `Gamma(x)`; it concludes expression synthesis. |
| Lambda/Result | It concludes an expression interface under the body environment; it specifies no recursive member-consistency/discharge premise. |
| Parameter selection and ordinary Pure role | They select entry/role and fresh endpoints; they do not validate simultaneous recursive assumptions. |
| Request opening | It opens an already supplied request package; this envelope contains no request-opening event. |
| §22/23 guard discipline | It constrains actual comparisons; it neither generates this source component nor proves its provisional environment valid. |
| Shared call-view direction | It demands source generation and one joint assignment; §§2,5 explicitly retain the generating judgment as a proof gate. |
| SCC scheduling or experimental transport | Applicable lifecycle/transport infrastructure assumes source semantic inputs; its scope excludes recursive Function formation. |

Thus this inspected rule fragment cannot supply the last rule. This is a
syntactic bounded observation about the explicit clauses, not a completeness
theorem for Yulang's historical documents or an argument that the selected
formation direction is inconsistent.

The smallest residual within the assigned derivation is the two-member SCC
before the alias. Removing the suffix `my h = f` from this local proof
obligation leaves the same missing discharge conclusion: neither conditional
body depends on that alias. This proof-obligation reduction is not a semantic
counterexample, source accept/reject experiment, or claim that future formation
ignores relevant uses. A future component-generation rule may consult those
uses, as the approved direction allows. No single-member or changed-source
probe was run.

Writing
`I_f=Fun(P_x,Result(I_g))`, `I_g=Fun(P_y,Result(I_f))`
would add a candidate recursive compatibility premise. Neither equality,
directed subtyping, least/greatest fixed-point selection nor a recursive binder
introduction follows from the selected synthesis equations. A solution to
candidate equations would still need an admissible source recursion rule and
origin proof. The finite-copy conservation result cannot discharge H1: copy
cycles do not create grounding events, and that result deliberately selects
no least recursive origin semantics.

## What would unblock this derivation

The next evidence must supply or derive a recursive source rule whose conclusion
has the demanded shape, under the existing formation direction. Its proof must
identify how the two definition interfaces validate the same provisional
environment, how provisional assumptions cease to be assumptions, and how the
original jointly scoped assignment survives. It must also ground the relevant
endpoint/binder events, including their §22 classification and introduction
levels, or justify absence of such introductions. Merely recording fields
named `origin` and `scope` is not that derivation.

This necessary information contract selects no specific equality/subtyping
premise, origin policy, recursive representation, value restriction or new
rejection. The primary must adjudicate whether such a rule follows from an
existing in-scope source contract or needs further approved specification.
I do not proceed to Generalize/MemberUse while its prerequisite is absent.

The retained seam remains unchanged: later evidence must relate the source
events to `r0,rho_h,c_h,R_h`, retain the direct `c_h <: R_h` and all four
incoming/replay shapes, and re-enter §22 on every actual derived comparison.
At current variable levels one, the direct variable-pair veto is conditional
on `Ex(c_h,l)` or `Ex(R_h,l)` with `l>=1`; current level alone does not supply
that premise. Structural comparisons still require separate variable/extrusion
coverage. Formation evidence alone closes neither coverage nor permission `(L)`.

## Checks, independence, resources and limitations

Commands: bounded `cat`, `sed`, `rg`, `git show BASE:path`, `git rev-parse HEAD`,
a read-only Python SHA-256/baseline-equality pass, and final leased-file scope
and whitespace inspection. Initial aggregate output was truncated; the rules,
selected source clauses and used prior-note sections were reread narrowly.
No exhaustive repository or historical-document search was attempted.

This static audit has no executable oracle, random seeds, enumeration ranges
or mutation runs. Its rule evidence is independently supplied by the authority
documents; the partial derivation shares H1 and, when origin-bearing, H2.
It does not independently validate those assumptions. Failure conditions are
an omitted applicable source recursion rule, a changed dependency, or treating
the bounded clause inventory as a complete source calculus. A checker supplied
with a hypothetical discharge rule would establish only consequences of that
rule, not its authority or source adequacy.

No tests, probes, builds, compiler/`cfg(test)` edits, formatters, Git mutations,
child agents or interactive questions. At most four lightweight read processes
were batched; heavyweight process count was zero. CPU/RAM peaks and total wall
time were uninstrumented; the packet specified static work without a numerical
compute limit. The sole write is the leased note.

Unverified: recursive source acceptance, source constraint generation,
parameter/generalization/use introduction policy, source-to-row realization,
§23 coverage, principality, production adequacy, full permission `(L)`, lifecycle,
alias uses, annotations, applications, handlers and mixed outer/member scopes.
No independent review of this artifact is claimed.

Recommended next action: obtain the exact recursive discharge rule and its
introduction evidence under the existing formation gate, rather than another
copy-graph or allocated-row classification experiment.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-recursive-origin-form-discharge-constructive.md`.
- Baseline SHA: `ba35b1b1341fe70f4445675e0d4c5d664c7c4875`.
- Changed dependency hashes: none; direct hashes are listed above.
- Review status: frozen unreviewed research-only partial derivation and bounded
  rule audit; no theorem closure, source rejection or implementation authority.
- Checks already run: selected rule/receipt inspection, pinned dependency hashes
  and current-byte equality, exact leased-path scope and whitespace inspection;
  no executable checks.
- Proposed one-line research-checkpoint commit message:
  `research: isolate recursive Form discharge rule and origin leaf gaps`.
- Shared-record deltas intentionally left for primary/curator: record last-rule
  absence only within this inspected fragment; distinguish the Form discharge
  hole from unclassified fresh parameter endpoints; retain Generalize/MemberUse,
  row realization and guard coverage as downstream obligations. No task, index,
  authority, theory map or question bundle was edited.

Writes stopped before submission; this artifact is frozen for review.
