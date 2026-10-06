# Multi-use role aggregation: a discriminator needs a constructor

Date: 2026-10-06
Baseline: `f1fc1a6eb700b1406d6bedebb46aec7cad082774`
Status: frozen, unreviewed research-only characterization
Scope: adversarial analysis of aggregation at one inferred higher-order formal;
no source rule, accepted-program counterexample, or implementation authority

## Objective, method, and dependencies

Determine whether the selected premises distinguish one eligible value-call
refining a shared formal, an all-use eligibility condition, and joint retention
of role alternatives. Method: hand-derived implication comparison and source
rule inversion. This does not repeat the predecessor's binary joint-relation
restriction witness or use a compiler/Oracle as a semantics reference.

Semantic inputs were read from the pinned commit above:

- `notes/design/2026-10-05-inferred-function-call-views.md`, §§1–5, including
  §1.1's distinction between source annotations, public schemes, and internal
  inference views;
- `questions/2026-10-05-function-call-view-formation/approved-answer.md`, exact
  approved q1/a2;
- `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md`,
  §§1–4;
- `notes/design/2026-10-05-source-contracts-and-common-allowance.md`, §§2–3,10;
- `notes/progress/2026-10-06-source-formal-relation-mixed-use-falsification.md`;
- `notes/progress/2026-10-06-qind-source-generation-judgment-candidate.md`.

The formation answer selects the protected Handler seed and ordinary-value
refinement in its stated example. It does not select a reusable per-use rule
for a component with additional calls. The nested addendum fixes only its exact
captured-function candidate. Its §3 explicitly excludes other brace meanings.
No claim about a second braced argument is licensed here. The nested approved
answer was included in the combined pinned read, but its central capture was
truncated and the recovery filter did not capture its body; the exact addendum
is the inspected source for that selected interpretation. This is an inspection
limitation, not a substitution of legacy behavior or an additional premise.

Operational inputs: `rules/research-lab.md`, `rules/design-authority.md`, and
`rules/git-concurrency.md`; task/index locator reads add no semantic hypothesis.
The producer changes only this leased note. Shared records and question bundles
remain primary-owned.

## Established boundary and opaque premises

The selected source direction requires a shared role-indexed contract, stable
source identities, one original joint `xi=(nu,K,D)`, and admission independent
of `Q`. An actual supplied callable keeps its role and entry. The protected
Handler seed is an internal inference view, not that actual callable's role.

Source-contracts §2.1 gives conjunction and union of whole-tuple relations
*once their clauses are supplied*. Section 3 requires accounting for every
source constructor. Neither supplies the missing source-formal role clause.
In particular, conjoining all call obligations does not mean that all calls
must supply the same role-refinement evidence. An existential trigger can
coexist with conjunction of every independently generated call obligation.

Let `U_C` be the nonempty relevant static use inventory of formal `d_f` in
source component `C`. Let `Omega_C` be its original admissible joint fibers,
and `Phi_C(xi)` its completed source constraint predicate. These are opaque
source-generated premises, not outputs constructed by this note. Write
`E(C,c,xi)` for eligible ordinary-value evidence and `NH(C,xi)` for the inferred
formal/use non-Handler conclusion. This notation assigns no new runtime
carrier and says nothing about the supplied callable's actual role/entry.
Eligibility may depend on the complete component and whole fiber; it is not
inferred solely from an argument's spelling or entry tag.

## Conditional implication comparison

Two possible *sufficient* refinement clauses are:

```text
Any:  forall xi in Omega_C.
        Phi_C(xi) and (exists c in U_C. E(C,c,xi)) => NH(C,xi)

All:  forall xi in Omega_C.
        Phi_C(xi) and (forall c in U_C. E(C,c,xi)) => NH(C,xi)
```

These are candidate assumptions, not selected Yulang rules.

**Conditional theorem.** For nonempty `U_C`, `Any` entails `All`.
Proof: choose an element of `U_C`; universal eligibility supplies existential
eligibility at the same `xi`, so `Any` yields `NH`. No coordinate is freshened,
hidden, independently selected, or recombined. For a singleton inventory,
the two antecedents are equivalent. Thus the approved singleton outcome
cannot discriminate these quantifiers, even if both candidate clauses are
assumed to apply to that singleton.

For two uses `c_v,c_o`, stipulate at one fixed original fiber:

```text
Phi_C(xi), E(C,c_v,xi), not E(C,c_o,xi).
```

Then `Any` requires `NH(C,xi)`. The antecedent of `All` is false, so `All`
requires no conclusion at this fiber. It does **not** require `not NH`, rejection,
or removal of the fiber. A completion in which another independently licensed
clause yields `NH` satisfies both candidates. A completion that retains both
role alternatives may satisfy `All`. Therefore an all-use sufficient rule and
joint retention are not disjoint semantic alternatives.

Even strengthening the all-use proposal to an exclusive trigger would require
specifying what failure of that trigger means. Joint retention describes the
representation/preservation of a relation; it is not by itself an inference
rule that negates `NH`. It can also be an intermediate state before an `Any`
rule introduces a source-justified constraint. The selected requirement to
retain the relation across admissible fibers forbids selecting a convenient
assignment during generation; it does not forbid independently justified
constraints from eliminating provisional seed alternatives.

This is a minimized logical discriminator for a missing implication, not a
three-model source counterexample. Two uses are necessary to separate the
existential and universal antecedents on a nonempty inventory. No increase in
the number of roles, effects, recursive nodes, or runtime events fixes the
missing conclusion on the failed antecedent.

## Source-shaped pair and why it remains conditional

The smallest relevant lexical records have two distinct call occurrences
sharing one resolved formal:

```text
c_v = Apply(Use(d_f), Use(d_x))
c_o = Apply(Use(d_f), e_o)
```

Their surface sketches are `f x` and `f <opaque argument>`, where the latter
is metanotation, not proposed Yulang syntax. The first occurrence resembles
the approved ordinary-value use. The second has no supplied source derivation.
The approved single-use result does not itself transport eligibility of the
first occurrence to this enlarged component. The displayed eligibility
assignment is therefore an explicit conditional premise.

Replacing the opaque argument with a second ordinary name gives the syntactic
pair `f x` / `f y`, but the supplied rules do not establish contrasting
eligibility for those occurrences. Replacing it with `{x}` would assume a
brace interpretation outside the nested addendum's exact scope. Neither
replacement yields a verified source discriminator. No complete two-call
program, source acceptance, or typed-call relation is claimed.

Static uses include latent calls; they are not a list of runtime entries.
Repeatedly invoking the returned `step` in the approved nested candidate
creates multiple dynamic histories of the same source call occurrence. It
does not create the second static use needed for this quantifier comparison.
Receipt instantiation at an entry event uses an admitted satisfying whole
`xi`; it cannot decide the static aggregation policy or generate the relation.

## Exact blocker and useful next clause

The missing constructor is the source-formal inferred-callable relation clause
identified as clause 4 of the generation-judgment candidate. To settle this
question, that clause must state:

1. the relevant static use inventory and eligibility judgment, including
   whether eligibility is component/fiber dependent;
2. whether eligible evidence at one use entails `NH` throughout the shared
   completed relation, or requires a premise about other relevant uses;
3. the consequence when that premise fails, and whether role alternatives are
   provisional, completed, or resolved by other source constraints;
4. how every use's call obligations remain active on the same original
   `(nu,K,D)`, with unchanged actual callable roles and Q-independent admission.

The primitive conjunction/union machinery can express different answers;
its availability does not select one. No valid countermodel to all completed
Yulang source rules is asserted: those constructor premises have not been
supplied, and this note has not realized the opaque two-use input as a typed
source component. The bounded result is that the inspected obligations and
singleton outcome do not provide the reusable constructor or the three-way
discriminator. A general rule crossing that boundary remains a user/design
choice; further equivalent toy relations would not resolve it.

## Evidence quality, checks, resources, and omissions

Oracle independence: no Oracle, legacy output, compiler result, execution
trace, or model checker was used. The document audit grounds the scope
boundaries; the implication proof is elementary logic under explicitly
supplied predicates. Its reference and candidate share `U_C`, `Omega_C`,
`Phi_C`, `E`, and `NH`; they do not independently validate those source
predicates. Encoding them in a checker would prove only the conditional logic.

Analytic mutations: interpreting `All`'s failed antecedent as `not NH` adds an
unselected converse; equating joint retention with permanent ambiguity adds
an unselected completion rule; omitting `c_o` after a trigger drops a required
source obligation; combining per-use fibers violates original joint scope;
counting dynamic entries as new static uses changes the quantifier domain;
using `Q` to supply missing eligibility violates formation independence.
No executable mutation suite was run.

Commands/checks: mandatory policy `cat`; pinned `git ls-tree` locator;
Python task/index/filename locator; combined pinned `git show`; one additional
bounded Python/`git show` section extraction expressly authorized by primary
after output truncation; leased-path `apply_patch` creation. Five top-level
read commands, serial; the final read launches one child Git reader. The
initial combined source capture was centrally truncated; the bounded recovery
read recovered the needed nested and source-contract sections. No build,
test, runtime probe, formatter, Git mutation, child agent, or interactive
question. Hand coverage: singleton implication equivalence and the two-use
mixed-eligibility antecedent. Seeds/ranges are inapplicable. CPU, peak RSS,
and total wall time were not measured; no heavyweight process ran.

Unverified: source licensing/typing of a second use, source generation of the
eligibility assignment, recursive relevance closure, principal/unique final
contracts, full admissible fiber construction, seed-to-final interpretation,
slot/profile/receipt generation, capture attachment, production membership,
source adequacy, and B-equivalent implementation. Live dependency equality
and independent review belong to the primary; no additional reads were made
after the authorized budget. Writes stop at submission of this frozen note.

Recommended next action: obtain or derive the clause deciding whether the
approved Value argument inference is a reusable per-use constructor, including
its component-dependent eligibility and failed-trigger consequence, before
choosing a multi-use policy or constructing another probe.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-role-aggregation-falsification.md`.
- Baseline SHA: `f1fc1a6eb700b1406d6bedebb46aec7cad082774`.
- Dependency hashes changed: none changed by this producer; semantic reads
  use immutable `baseline:path` objects. Live dependency hashes were not
  rechecked; the primary must check them before integration.
- Review status: frozen, unreviewed, research-only conditional characterization;
  no independent certification or source/theorem gate closure.
- Checks already run: pinned governing-section audit and hand implication
  derivation; no builds/tests/executable checks. Exact leased-path creation
  reported by `apply_patch`; no post-write process was added to the read budget.
- Proposed commit message: `research: separate role aggregation from joint alternative retention`.
- Shared-record deltas left to primary/curator: record the reusable per-use
  constructor as open; distinguish all-use sufficient inference from its
  unspecified failure consequence and from relational retention. Link this
  note if accepted; do not mark source generation or principality closed.
  Tasks, theory maps, design index, queue, and question bundles were not edited.
