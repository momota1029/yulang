# Exact formal/Call introduction: independent witness cut

Date: 2026-10-06
Baseline: `c8a673342b5697db11427dfdb8204da1c075cf74`
Branch: `research/simple-sub-intrusion`
Status: producer-authored research; independent review unclaimed; frozen on submission
Claim class: bounded authority audit and conditional witness derivation; exact obstruction
Lease: this file only
Scope: `I-formal` / `I-call-rest` for the selected captured-step component
Semantic and implementation authority: none

## 1. Objective and result

Attempt the original-profile converse using an introduction predicate independent
of the proposed origin grammar. Current authority supplies a positive predicate
for a source Function elimination, but supplies no complete original static-profile
introduction judgment from which to invert an arbitrary original profile atom.
The remaining local premise is **witness reflection at the supplied profile
operand**, preserving its original position, source contribution, scope and joint
assignment. Internal exhaustiveness of the candidate grammar does not supply it.

This attempt therefore stops at the same semantic cut as the previous attempts.
It does not close P, construct a source-valid extra position, prove semantic
underdetermination, or establish a need for a new user decision. The refinement
below is an acceptance criterion for a future proof: the bridge need only reflect
the exact component's original introduction witnesses; it need not identify the
entire original language grammar with the candidate grammar.

## 2. Authority and hypotheses

Read at the pinned revision:

- [Inferred call views](../design/2026-10-05-inferred-function-call-views.md)
  §§1.1–5; [approved q1/a2](../../questions/2026-10-05-function-call-view-formation/approved-answer.md)
  and its [receipt](../../questions/2026-10-05-function-call-view-formation/receipt.md).
- [Nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
  §§1–4; [source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2–3/10; [typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §6; [typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md) §6.
- The six assigned P artifacts listed in §6 and the positive
  [Call construction](2026-10-06-source-call-generation-construction.md) §§3–4.

The selected finite tree is fixed, without reinterpretation:

```text
C = lambda(f,
      bind(step,
        result(lambda(x,c = call(result(name f),result(name x)))),
        result(name step)))
beta = (d_f,R_f); p0 = (beta,call.effect)
```

**Hsource (selected meaning):** lexical identities, sequential Bind, final
return of `step`, retained capture of the same outer `f`, and no annotation.
**Hseed (established bounded research):** Gen-Call-0 emits one shared complete
`F_c` and `ElimOrigin(c,u_f,d_f,R_f,p0,p_out(c))` before satisfiability.
**Htransport (conditional machinery):** every transport used has its independently
typed correspondence and retains indexed origins and the whole `xi=(nu,K,D)`.
**Hrest (conditional, outside this local attempt):** an original applicability
witness can be traced through genuine preserving steps to an original
component-owned first introduction. This is not established by defining a
generated footprint, and no proof of general `I-exhaust` is claimed here.

Preserve full protection/no annotation grant at applicable positions; the
same-root provisional/refined formal relationship; actual callable roles;
callback-literal B; Q-independent admission; and soundness/principality gates.
There is no added hypothesis excluding a dependent result schema.

## 3. Predicate that can be grounded independently

Define a proof-relevant **positive** predicate:

```text
ElimIntro(C,d_f,R_f,p,o;xi) iff
  o is a Gen-Call-0 certificate for a resolved Call occurrence e in C,
  with its callee resolving to d_f on shared R_f,
  and its conclusion is ElimOrigin(e,...,p,p_out(e)).
```

The reference is the independently retained source Function-elimination
constructor, not either candidate grammar's accumulator or transition table.
It establishes an immediate complete-invocation observation address, including
entry/body/designated consumer, without selecting solved result shape or Q.
It does not define `Applicable_original`.

For this exact tree, source resolution yields `e=c`; the constructor conclusion
yields `p=p0`. Thus:

```text
ElimIntro(C,d_f,R_f,p,o;xi) => p=p0.
ElimIntro(C,d_f,R_f,p0,o0;xi) is supplied by Hseed.
```

This is inversion of the positive constructor, an established bounded input
specialized to the fixed tree. It is not a new original-profile theorem.

An independent **complete original** predicate would instead require a genuine
source-formation proof:

```text
OrigFirst(C,d_f,R_f,p,kappa;xi)
```

Here `kappa` must prove first formation of the original profile atom, with its
source contribution and original scope. This is an interface requirement, not
a definition by `ElimIntro`, candidate birth output, type paths, or supplied
profile membership. The governing sections do not supply its complete rules.

## 4. The exact local missing premise and conditional derivation

The smallest useful bridge at this seam is:

```text
Reflect_local:
  OrigFirst(C,d_f,R_f,p,kappa;xi)
  => exists o. ElimIntro(C,d_f,R_f,p,o;xi)
               and Link_original(kappa,o; same contribution,scope,xi).
```

`Link_original` requires a genuine source incidence/contribution certificate.
It is not equality of effect endpoints or an invented identification of all
contribution witnesses with `o0`. Distinct original contributions remain distinct.
The position-only projection of this premise suffices for singleton inventory;
full contribution correspondence requires the displayed witness link as well.

**Conditional derivation.** Take an original applicability witness. Under Hrest,
invert its preserving steps to `OrigFirst` at the original profile operand.
Apply Reflect_local, then §3's positive inversion to obtain `p=p0` and the
corresponding source-elimination certificate. The original witness and ledger
remain attached throughout. Hseed supplies the positive direction. No candidate
grammar is used in these steps. The open premises are Hrest and Reflect_local;
this is a conditional argument, not proof of either premise.

At the assigned two leaves, Reflect_local would require:

- **I-formal:** a proof that this implicit formal's component-owned profile
  introductions reflect to certified component uses, rather than independent
  implicit profile schemas.
- **I-call-rest:** a proof that an original introduction at this exact Call's
  contract reflects to its complete-invocation origin, rather than an additional
  result-contract origin. Inherited result packets retain their own certificates.

These statements are unproved obligations. Neither is adopted as language policy.
They are narrower than asserting that every original source rule is literally
a row of the candidate grammar; they still contain the essential unproved
source-origin locality premise. This is not claimed as a reduction of that
semantic uncertainty.

## 5. Why current authority cannot fill the premise

The attempted witness conversion has three precisely located cuts:

| Governing section | Constructed or assumed object | Missing premise |
| --- | --- | --- |
| Typed-core §6, parameter generation | `Gamma(f)=Value(A_f)` and fixed entry/rebind skeleton; nested paths retain admitted premises | Original implicit contract's profile-atom production/inversion |
| Typed-core §6, application | `Computation(E_c,A_c)`, complete invocation constraint and existing typed path/contract obligations | First formation of every original atom of those obligations |
| Typed-boundary §6, boundary introduction | Fresh dynamic `b=(receiver,slot,Gamma,endpoints)` with **supplied** signature profile Gamma | Source proof producing Gamma before dynamic introduction |

Source-contract §§2–3 interpret already decorated whole tuples and account for
emitted execution/membership/admission clauses. They explicitly supply original
paths, owners, receipts and roles in §3.1. Their constructor-image proof cannot
turn a profile operand into its own independent producer. Inferred-call-view
§5 expressly leaves profile generation and uniqueness/principality open.

Consequently the exact failed operation is converting a legitimate original
profile operand's atom certificate into an ElimIntro certificate at the same
source contribution and scope. The needed original proof object has no complete
rule basis in these sections. A symbolic schema at `A_c` could satisfy preservation
once supplied; that supplies neither its source license nor its exclusion.

The previous constructor inversion and the candidate's internal inversion both
leave this operand untouched. This lane stops before choosing “formal adds no
schema” or “Call adds only p0.” Another supplied-transition checker or consumer
count would assume Reflect_local. No repeated toy probe was run.

## 6. Dependency snapshot and checks

All inputs below were read from the pinned commit and matched live bytes at the
dependency check. SHA-256:

```text
ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd  rules/research-lab.md
9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29  rules/design-authority.md
e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e  rules/git-concurrency.md
8c617ceb978dfa26ce12f4f71ecc8ece22ffd8f1cf1982125b33142f645ae1c0  rules/question-board.md
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1  notes/design/2026-10-05-inferred-function-call-views.md
750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0  notes/design/2026-10-06-nested-block-function-source-realization-addendum.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186  notes/design/2026-10-05-source-contracts-and-common-allowance.md
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e  notes/design/2026-10-02-typed-computation-core-elaboration.md
1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb  notes/design/2026-10-02-typed-boundary-realization-draft.md
1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536  questions/2026-10-05-function-call-view-formation/approved-answer.md
6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0  questions/2026-10-05-function-call-view-formation/receipt.md
6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073  notes/progress/2026-10-06-source-call-generation-construction.md
8b8b1d49e587835d65c4c6a13a0fc476b07bc58282ac5c58e782b4e5fd5b6a4b  notes/progress/2026-10-06-formal-profile-formation-rule-attempt.md
c5ec22bab3b082de6c460aff3b6775fe9aa0f0624659748e9c5b2feb2d08d8c9  notes/progress/2026-10-06-profile-original-introduction-construction.md
abbef6d58c5e5691e84ed85fb85038a9805a3a237e19769bdae3dce9da60bf05  notes/progress/2026-10-06-profile-extra-origin-falsification.md
9038064ea04430c19cf83986c58fd97136285a8aaff6feef612550805f63914c  notes/progress/2026-10-06-profile-origin-candidate-rule.md
72ee64aae60e787a45ca5bd18f7f8d0be4dde785bf5bb569b4b837bf9c9fe8c1  notes/progress/2026-10-06-profile-origin-rule-candidate-attack.md
8c9127b41764a25e374a636edf342fb5b2c4165ecae4e35bfcd3b63cb105a42f  notes/progress/2026-10-06-profile-position-producer-crosswalk.md
```

Commands/results: read-only `git rev-parse HEAD`, `git branch --show-current`,
`git status --short`, `git show <baseline>:<path>`, bounded `rg`/`sed` reads;
standard-library Python checked all eighteen dependency hashes and live equality
(passed). Initial combined captures were truncated; substantive governing sections
and assigned P artifacts were subsequently read in bounded captures. Task/index
reads were locators, not a complete shared-record audit. No whole-repository
semantic search is claimed. Narrow output whitespace/link/dependency checks are
reported in the submission packet after writing.

## 7. Independence, limits and recommended action

No Oracle material supplies a source premise; historical Oracle SHA is unused.
There is no executable oracle or experiment. The predicate shares the retained
positive Call constructor and approved source interpretation with prior work;
it is independent of the candidate grammar, not independently empirically validated.
A checker implementing the candidate transitions would prove their consistency,
not Reflect_local. Seeds/ranges and executed mutations are inapplicable. The
conceptual test is replacing a supplied Gamma atom with an independently derived
source-origin certificate; this attempted proof cannot perform that conversion.

Coverage: one selected tree, the two assigned introduction leaves, and the exact
listed sections. No extra-source program, altered annotation, broader recursive
component, source-valid counterexample or full grammar search was attempted.
Reflection fails if a genuine extra original formal/result origin exists; the
conditional argument fails without Hrest or a valid contribution-preserving link.
Static singleton would still not prove every-original-solution lifting, ordinary
D-origin completeness, original contribution normalization, admission A, typed
capture/receipt/lifetime, source acceptance, soundness or all-view principality.

Resources: lightweight reads/metadata processes only; at most three short reads
batched, zero builds/tests/Oracle runs/heavy processes/children. No numerical CPU,
RAM or wall-time budget was supplied. CPU time, peak RSS and authoring elapsed
time are uninstrumented. No Git mutation, compiler/test edit or shared-record
write occurred. No hypothesis or user-selected meaning was changed.

Recommended next action: have the primary adjudicate the exact original
profile-operand witness interface. Accept a local source proof only if it
constructs/inverts OrigFirst independently and supplies Reflect_local; otherwise
record the blocker rather than commission another preservation/candidate probe.
Adopting a new source-origin clause requires the separate design gate.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-profile-intro-constructive-next.md`.
- Baseline SHA: `c8a673342b5697db11427dfdb8204da1c075cf74`.
- Changed dependency hashes: none observed in the eighteen-input snapshot;
  primary must revalidate before integration.
- Review status: producer-authored bounded audit/conditional derivation;
  independent review unclaimed; original P and all downstream gates remain open.
- Checks already run: targeted pinned-section reads and eighteen baseline/live
  byte/hash checks; narrow final output checks supplied with the handoff;
  no tests/builds/Oracle invocation.
- Proposed one-line checkpoint commit message:
  `research: isolate independent original-profile witness reflection premise`.
- Shared-record deltas left to primary/curator: record the missing independent
  original static-profile proof object and local witness-reflection criterion;
  retain I-formal/I-call-rest/I-exhaust and P open. No automatic task/index/theory,
  authority or question-board change is proposed.
- Writes stop before submission; primary owns review and Git integration.
