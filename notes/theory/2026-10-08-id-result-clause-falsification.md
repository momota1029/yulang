# Identity result clauses: full-membership saturation attack

Status: Draft research checkpoint; frozen on submission; independent review pending.
Claim class: conditional fixed-point lemma and minimized logical countermodel.
No source-admitted counterexample, contract recertification, gate closure, or
production authorization is claimed.

## Objective, baseline and method

Independently attack the implication that different diagonal and complete-value
result predicates for `forall q.q -> q` necessarily give different complete
observations. The method is a documentary derivation over the candidate's
positive membership grammar, followed by a two-tuple countermodel to that
implication. It is not a second implementation of a supplied source machine.

Pinned local baseline: `f416d14cbacd3ce643ccda1591e7855c3f834a5c`.
The full SHA was read from the local Git metadata without running Git.
The sole leased output is this note. No other worker's output was edited.

Governing locators supplied by the primary:

- `questions/2026-10-08-successor-generalize-root-policy/question.md` q1;
  `approved-answer.md` a1, decision items 2–5; `receipt.md`.
- `notes/design/2026-10-05-source-contracts-and-common-allowance.md`
  §§2.2, 3.3, 3.7, 5.3.
- `notes/design/2026-10-05-inferred-function-call-views.md` §§1–5.
- `notes/design/2026-10-02-typed-computation-core-elaboration.md` §§6/9.
- Committed candidate
  `notes/theory/2026-10-08-id-arrow-decoder-candidate.md` §§3–6,
  especially its membership equations at lines 160–177, result predicates at
  lines 184–219, and actual-root query obligations at lines 224–252.

The primary's narrowed authority reminder is: §2.2 retains independent
`DescMem`; §3.3 admits histories independently of `Direct`; §3.7 uses complete
guarded `W/Z` abstraction and a one-way `Le` proves containment; §5.3 compares
actual submitted roots with admission `Eq` and membership `Le`. These pins do
not supply concrete result licenses or abstraction rules.

Source-section/approval captures were truncated. The locators above remain
dependency pins, not a claim that this worker independently reread every
governing passage. The mathematical result below depends explicitly on the
candidate equations. Dirty shared records and unintegrated upstream-only
Generalize material supply no premises; ordinary F5 supplies no premises.

## Conditional saturation lemma

Fix the original scoped assignment `xi`, complete caller inputs, consumer,
paths, and interface. Let `U` consist of whole tuples
`y = (h,O,w;xi)`; do not quotient providers or apply final projection yet.
The explicit hypotheses are:

1. Both variants use this same universe and the same independently admitted
   histories `A`. This includes initial, response, resumption and every
   admission-live future-provider challenge.
2. The complete final guard `G`, descriptor predicate, and exhaustive positive
   `W/Z` grammar are identical under the fixed original incidence map. The
   descriptor conjunct is present in `G`. These are hypotheses about complete
   interpretations, not consequences of the scheme spelling.
3. The diagonal base `Bd` is contained in the complete-value base `Bv`.
   Identity is licensed by the latter. No other source license is inferred.
4. Membership is the candidate's least positive closure, with finite
   derivations:

   ```text
   Ti(S) = { y | G(y) and
                  (Bi(y) or Z(y) or exists x,z. S(x) and W(x,y,z)) }
   Xi = least fixed point Ti                    i in {d,v}.
   Mi(y) = Xi(y) and DescMem_i(y).
   ```

Under hypotheses 1–4,

```text
Xd = Xv  iff  { y | G(y) and Bv(y) } is contained in Xd.
```

Proof: `Bd <= Bv` makes `Td(S) <= Tv(S)`, hence `Xd <= Xv`.
If every guarded complete-value base tuple is already in `Xd`, then the
fixed-point equation for `Xd` shows `Tv(Xd) <= Xd`: the new base branch adds
nothing, and the shared `Z/W/G` branches are already closed. Leastness gives
`Xv <= Xd`. Conversely every guarded `Bv` tuple belongs to `Xv`, so equality
implies the displayed containment. This is a conditional mathematical proof;
it does not prove that hypotheses 1–4 describe either actual decoded root.

Equal `X` and equal descriptor predicates imply equal full `M`. Hypothesis 1
then gives equal independently admitted domains; the same final projection and
same caller conjunction give equal resulting observation families. The
descriptor/guard premise cannot be replaced by one-way guard inclusion for
this equality conclusion.

## Smallest nonempty-base countermodel

Use two distinct whole tuples `d,e` at the same `h0,xi0`, caller inputs,
consumer and interface. In their intended candidate reading, `d` returns the
input package and `e` returns a different package under typed transport. For
this logical model, set

```text
U       = {d,e}
A       = {h0}                 shared, independently stipulated
G       = DescMem = true       on both tuples
Bd      = {d}
Bv      = {d,e}
Z       = {e}
W       = {(d,d,z0)}            a nonempty positive preservation rule.
```

The first closure stage gives `Xd = {d,e} = Xv`; the `W` rule adds nothing.
Consequently `Md = Mv`, despite `Bd != Bv`. `Z` does not consult the result
predicate or query success. Even with an injective final projection, the
observations are equal. No quotient or hidden provider identifier is needed
to erase the difference.

An alternative logical saturation mechanism takes `Z` empty and
`W = {(d,e,z0)}`. Then `Xd` reaches `e` at the second stage, again equalling
`Xv`. These are two hand calculations illustrating one lemma, not two probes
or two independently grounded source models. They make no claim that either
grammar is the selected complete Option 2 grammar.

Two tuples are minimal for this attack when the diagonal identity base is
nonempty and a distinct guarded complete-value result exists. Removing `e`
removes base inequality. Removing its `Z` supply in the first model, or its
`W` derivation in the alternative, makes the full closures differ. Rejecting
`e` in the final shared guard also erases the distinction, by filtering it
before either closure can admit it.

This is a countermodel to the proposed logical inference from base difference
to full difference. It is not a source-admitted witness: `A`, the package
license, the descriptor law and `Z/W` were stipulated. It establishes neither
that the contracts admit this concrete instantiation nor that they exclude
it. A checker fed these stipulations would validate only the same arithmetic.

## Precise source discriminator blocker

The candidate itself calls the unequal returned-provider pair a conditional
rule discriminator, and says that no provider/license package was constructed
(candidate lines 204–219). To turn it into a discriminator with fixed callers
requires all of the following at once:

1. A concretely licensed complete-value result package under the same `q`,
   original assignment, authority and dependencies, with an independently
   valid final descriptor/guard judgment.
2. A complete admission certificate for the shared histories, including every
   returned or abstract provider's future challenges. A new returned provider
   can change `Reach/Future`, so membership positivity alone proves no domain
   equality.
3. A proof that the candidate extra tuple is absent from the diagonal root's
   **entire** `W/Z` closure, rather than merely absent from its source base.
4. A surviving difference after original witness quantification, the fixed
   caller conjunction and final projection. Distinct raw provider IDs alone
   establish none of these judgments.

Thus repeated `q`, two values with matching type labels, or a source call to
identity with two possible raw values supplies no witness by itself. The
source identity returning its input does not determine every permitted
production abstraction observation.

The exact blocker is missing simultaneous package licensing, admission
correspondence, and non-saturation evidence for the complete selected
abstraction grammar. The two-tuple lemma resolves a logical shortcut but
leaves that source premise untouched. No larger equivalent finite probe is
recommended.

Equal denotations also do not prove equal `Direct` derivability: §5.3/candidate
§5 requires checked certificates at the actual submitted roots, and no
certificate-search completeness theorem is supplied. A purported distinction
between available proofs needs its own actual-root argument; it cannot be
asserted from the unequal result clauses. Conversely, a genuine projected
membership difference would still require a formed required view and the
ordinary resolution-conformance obligations before a query consequence.

## Independence, coverage and resource record

There is no executable oracle. The saturation proof shares only the explicitly
assumed positive equations with its target and attacks the logical implication
between base and complete membership. The source licensing, domain and
descriptor judgments are deliberately unproved hypotheses. This worker is an
independent attack producer relative to the committed candidate, not an
independent reviewer of this new note.

Coverage: two finite whole tuples and a general conditional least-fixed-point
argument. No source/provider enumeration occurred. Seeds and ranges: none.
Named mutations were calculated by hand; none were executed. Omitted scope:
actual complete `KernelArrow/Val_q/W/Z/G`, source realizability, exact approval
recertification, future-provider domain construction, compiler correspondence,
captures, recursion, arbitrary annotations, imports, principality and proof
search completeness.

Commands: two serial `python3` documentary reader invocations. The first read
rules, locators and candidate but over-read task/index material; its output
was truncated. The primary explicitly authorized one bounded recovery reader
for direct rules, approval files, exact selected source sections, candidate
and SHA-256 computation. That capture also truncated. No further reader was
launched. No unobserved passage is treated as independently verified evidence.

Both readers exited successfully with recorded tool wall time about 0.1 s
each. Maximum simultaneous local reader processes: one. The original
one-process-total allowance was extended by the primary for the one recovery
reader; total invocations: two. No builds, tests, executable probes, Git
commands/mutations, formatters, children, scratch outputs or shared writes.
CPU time, peak RAM and total reasoning wall time were not instrumented.

Fully visible rule digests:

| Dependency | SHA-256 |
| --- | --- |
| `rules/design-authority.md` | `925f1c5cd4ca6ce7306b1375eb9c1a699a83d3491efba21b50271e176eee5ba5` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `rules/question-board.md` | `8c617ceb978dfa26ce12f4f71ecc8ece22ffd8f1cf1982125b33142f645ae1c0` |

Other computed dependency digests were not retained in the visible truncated
capture. Baseline-file equality and dependency changes were not independently
established in this lane. The primary must recheck the direct dependency
snapshot before integration; this note does not certify a moving worktree.

Recommended next action: construct one licensed off-diagonal full package at
fixed caller/interface and prove its independently admitted history plus its
absence from the diagonal complete closure, before presenting a result-law
choice as an observable source decision.

## Commit packet

- Exact leased path:
  `notes/theory/2026-10-08-id-result-clause-falsification.md`.
- Baseline SHA: `f416d14cbacd3ce643ccda1591e7855c3f834a5c`.
- Dependency hashes changed: unknown; primary recheck required. Visible rule
  digests are above; unseen source/approval digests are not claimed verified.
- Claim/review status: frozen Draft conditional saturation lemma and logical
  countermodel; independent review pending; no source witness or gate closure.
- Checks already run: two documentary reads, full local HEAD metadata read,
  source-locator extraction, SHA-256 computation with capture limitations,
  hand derivation of the closures. No tests/builds/probes/Git.
- Proposed checkpoint message:
  `research: show complete id membership can erase result-clause differences`.
- Shared-record deltas left for primary/curator: record that base inequality
  alone cannot justify an observable choice; retain complete-grammar
  non-saturation, package licensing, independent admission and actual-root
  certificate obligations. No edits to task, index, authority or questions.

Writing stops before submission for frozen review.
