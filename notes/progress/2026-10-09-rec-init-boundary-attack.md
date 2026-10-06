# REC_INIT: the first read of a member without an initial provider

Baseline: `95307a281981cc4d2461b4f20e44d27a5f6b806a`
Status: frozen compiler-referee-reviewed research-only conditional derivation
Gate/method: REC_INIT; source-clause audit and earliest-publication argument
Exclusive write lease: this note only
Semantic/implementation authority: none

## Objective and result

Reduce non-constructor-guarded initialization to its first concrete obligation,
without repeating REC-DESC's membership attack on an already constructed
closure. The minimum candidate is a singleton declaration whose initializer is
its own resolved Name. Its decorated initializer is `result(name f)` under a
provisional `Gamma(f)=Value(R_f)`. The surface mnemonic is:

```yu
my f = f
```

This is a **conditional source candidate**, not an established supported
successor program, accepted-source counterexample, or contradictory language
meaning. Existing binding-body Name syntax and Name/Result formation ground
its constituents; the inspected clauses do not select the successor runtime
initialization/admissibility rule for their recursive combination.

Under the explicit strict-initialization hypotheses in §3, there is no finite
successful first provider publication. The derivation identifies the missing
read-before-initialization clause. It proves neither that the actual source
diverges nor that it is rejected. An implementation of those hypothetical
rules would only reproduce this conditional theorem.

## Governing sections and retained results

| Source | Exact usable premise and boundary |
| --- | --- |
| [DAG REC-K, REC-INIT, RAW-SOURCE](../theory/successor-proof-obligations.md) | K closes the selected guarded mutual-provider knot. REC_INIT is OPEN-SEMANTIC and needs included initializer forms/order/world access; RAW_SOURCE retains a precisely declared source envelope and independent judgments. The DAG is a locator, not semantic authority. |
| [Charter §2](../design/2026-09-29-scc-intrusion-redesign-charter.md) | F4 infrastructure is retained only within its Integer/resolved-Name scope. Its open internal inference roots and all-member visibility barrier concern inference/publication; they do not define initialized runtime values. |
| Charter §§3–4 and §12 | Supported source forms and guarded/unguarded fixtures remain research obligations. Finite recursive graph representation does not select a runtime initialization rule. |
| Charter §§16–17 | Inert computation introduction, whole-argument reification, same-receiver Value entry, and no additional latent force are selected. They do not turn an unavailable Name into a delayed initializer. |
| [F4 header and §1](../design/2026-09-21-oracle-aligned-f4-int-scheme-scc-draft.md) | Authoritative binding-body Integer/resolved-Name inference scope explicitly excludes Core IR. An unconstrained inference root generalizes to Never within that scope; this is not a source value or a runtime read rule. No Oracle execution or inference output is used here. |
| [Result synthesis §4](../design/2026-10-02-source-result-synthesis-choice.md) | Authoritative Name preserves `Gamma(f)` and `Result(Value(R_f))=Comp(empty,R_f)`. Synthesis executes nothing and supplies no provider at `R_f`. |
| [Typed core §§2–4](../design/2026-10-02-typed-computation-core-elaboration.md) | Draft derivation-core translation: `V[name f]=lookup(f)`, `X[result(d)]=Return(V[d])`; code labels are preallocated before traversing children. The realization theorem separately requires initial relatedness. No lookup rule forces. |
| Typed core §6, structural rules and final qualification | Ordinary local Bind consumes an RHS result when its enclosing computation executes; forward references reuse registered declaration endpoints. The table is relative to lexical interfaces and explicitly leaves recursive-binding inference/lifecycle open. It is not a recursive declaration initialization rule. |
| [Ordinary computation §§2–3](../design/2026-10-02-ordinary-computation-semantics-package.md) | Draft ordinary machine retains lexical references and current state. Its Return/Request bind and invocation re-entry rules concern existing carriers/closures and pending source suffixes. No rule in these inspected sections supplies the value of an uninitialized recursive member. |
| [Reviewed K construction §§3.2–3.3,6](2026-10-06-recursive-source-validation-construction.md), [review §2](2026-10-06-source-constructor-review.md) | The selected `my f x = g; my g y = f` constructs actual immutable closures without member validation. Bare alias initialization, effectful initialization and arbitrary recursive local Bind are expressly excluded. |
| [REC-DESC Name attack, last-rule boundary](2026-10-07-rec-desc-captured-name-lookup-stop.md) | Given actual `eta_f(g)=v_g`, descriptor lookup adequacy is still open. This note stops earlier: no actual provider has been obtained. It supplies no REC-DESC or member-discharge result. |

These Draft core/machine clauses are used as declared hypotheses of a bounded
derivation, not promoted to blanket source authority. No selected effect,
entry, result-synthesis, recursive descriptor, or generalization meaning is
reopened.

## Conditional derivation with exact hypotheses

The selected formation law gives, relative to the provisional environment:

```text
Gamma(f)=Value(R_f)
Synth(name f)=Value(R_f)
Result(Synth(name f))=Comp(empty,R_f)
V[name f]=lookup(f)
X[result(name f)]=Return(lookup(f)).
```

`Return(lookup(f))` describes the data lookup required to obtain the returned
value; it is not permission to return an unresolved code label as a value.
The symbol `R_f` supplies an interface position, not that value. This formation
derivation neither establishes nor assumes `DescMem(R_f,v)`.

Consider the following candidate initialization hypotheses:

- **H1, inclusion/resolution:** this recursive singleton is included; its
  initializer's Name resolves to that same member. Its initializer is the
  ordinary Value-result derivation just displayed. This inclusion and
  recursive registration are not proved for the successor raw-source envelope.
- **H2, initial availability:** preallocation/registering `f` supplies identity
  and code only. Initially no actual value is available at that member, and no
  imported/provider value is installed there by a separate rule.
- **H3, first publication:** initialization makes a value available at `f`
  only after that initializer has returned a value. It creates no value before
  evaluating this bare Name initializer.
- **H4, ordinary successful read:** a successful `lookup(f)` returns a value
  already available at that same member. Reading an unavailable member does
  not itself manufacture or install one. This is a candidate premise; the
  exact unavailable-read behavior is the missing source clause.

“Available” and “publication” are proof predicates, not a proposed mutable
cell, production representation, or conflation with scheme publication.

**Conditional theorem.** Under H1–H4, no finite execution successfully
performs the first provider publication at `f`.

**Proof.** Suppose a finite execution has a first publication event `p`.
By H3 its initializer has previously returned a value. The displayed
Name/Result initializer can return that value only after a successful read of
`f`. By H4, that read requires a value already available at `f`. H2 excludes
an initial value and a separate provider source; therefore some publication
at `f` must precede the read. This contradicts the choice of `p` as first.
The same reasoning excludes an immediately successful first read. QED.

This is a finite-success impossibility **under these candidate premises**.
It classifies neither infinite behavior nor errors. In particular it does not
select an error, divergence, stuck state, bottom value, least/greatest fixed
point, or rejection boundary for Yulang.

The first discriminating obligation is consequently:

```text
Resolve(name f)=f + allocated identity/code(f) + no available provider(f)
  -- evaluate this initializer's Name --> ?
```

If the intended source rule initiates/re-enters an unfinished initializer on
this read, its own progress/admissibility and current-world obligations must
be supplied. Ordinary invocation re-entry in §3 is not that rule: it already
has a Closure/carrier and a saved invocation suffix. Under H3–H4, adding
re-entry without a value-producing base event still cannot yield a finite
first publication by the proof above. No re-entry policy is adopted here.

## Minimality and failure conditions

The witness uses one recursive member, one resolved Name and no Call, Force,
operation, handler, annotation, local brace, mutable source store or imported
provider. Removing the member leaves no initialization target; removing the
Name self-edge removes this cyclic availability obligation. The earlier
reviewed two-alias exclusion can therefore be reduced structurally to one
self-edge, conditional on singleton inclusion. This is minimal in this
member/Name-count envelope, not a theorem about shortest accepted programs.

Replacing the bare initializer with the source closure constructor changes
H3's relevant case: a closure is furnished inertly before its body Name is
read, as K proves. Supplying an independently justified initial provider
invalidates H2. Allowing the read itself to furnish a provider invalidates
H4. Rejecting/excluding the source invalidates H1. Any of those conditions
blocks use of the theorem; a solved scheme, preallocated label or invocation
re-entry wrapper alone does not establish such a condition.

These are logical premise mutations, not executable mutation results.
There were no random seeds, enumeration ranges, runtime observations or
checker passes. No repeated toy probes were performed.

## Minimum independent clause and remaining scope

The inspected sources do not establish H1–H4 jointly. The precise blocker is
the missing **recursive declaration initialization/admissibility clause** for
the singleton Name RHS: does the source envelope include it; what value
availability exists before its RHS is consumed; and what transition or
admissibility consequence does the first unavailable self-read have?
If it is included, that clause must construct the actual provider or specify
the unsuccessful behavior and preserve original lexical ownership/current
world on any pending or re-entered execution. If excluded, the exclusion must
be an explicit supported-input judgment rather than inferred from K's scope.

This is the minimum clause needed for this witness, not a proposed complete
policy for effectful, mutually dependent or local recursive initializers.
Its resolution may be derivation from an existing independently governing
source clause; the audit does not prove that a new user decision is necessary.

Oracle independence is strict: no Oracle source was executed or used as a
semantic oracle; no compiler output, acceptance fixture, scheme shape or test
result supplies H1–H4. The derivation shares the displayed Name/Result
translation and H1–H4 with any checker one might write. Such a checker would
establish only consistency with those assumptions. Source adequacy requires
an independent justification of the initializer/read rule first.

Unverified: raw-source recursive singleton admission, complete recursive
initialization rules, actual providers for this candidate, effects during
initialization, re-entry/world preservation, member descriptor/admission,
generalization, RAW_SOURCE inversion, and production conformance. No gate is
closed and no accepted-source counterexample is claimed.

Recommended next action: the primary should locate or obtain the narrow
independent source clause for this singleton initializer, then check its
initial-relatedness/provider obligation against typed core §4 before enlarging
the initializer family or running a model of guessed rules.

## Freeze and verification

Only the leased note was written. Reads used `rg`, bounded section inspection,
read-only `git rev-parse`, `git show` and path-scoped status. Direct-dependency
SHA-256 and baseline-byte equality were checked; note-local links/newline/
whitespace and final dependency equality are the final bookkeeping checks.
No compiler edit, checker, test, build, Git mutation, delegation or question
was performed. Independent review is pending; the producer's audit is not
independent review.

Resource use: no heavyweight process, no executable semantic search, at most
four concurrent lightweight file-reading shell processes. CPU/RSS and total
wall time were not measured; no numeric resource budget was supplied. The
output budget is this single bounded note. The failure condition for freezing
is a changed direct dependency or an overlapping lease, not unrelated branch
movement.

### Frozen direct dependencies

All entries matched the pinned baseline bytes on the initial pass. The final
producer report records any delta and the frozen artifact hash; this note
does not embed its own changing hash. Task/index reads were navigation only.

| Path | Baseline SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/theory/successor-proof-obligations.md` | `18bfa4e5bb461616ca17a0c9a1492f75ff7fca2f6231a13b3d68e0a3335136dc` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/design/2026-09-21-oracle-aligned-f4-int-scheme-scc-draft.md` | `7ec6ae3b8ea4048d0407388b23665092a121a3720f8658055dfb5e1046a09c25` |
| `notes/design/2026-10-02-source-result-synthesis-choice.md` | `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-ordinary-computation-semantics-package.md` | `ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917` |
| `notes/progress/2026-10-06-recursive-source-validation-construction.md` | `630c73123239be97e2fb4466d84b5e2dccaeb535450ddce2ec063f1d67226407` |
| `notes/progress/2026-10-06-source-constructor-review.md` | `62313bd06aed238c5693c1334b6c402859fe8267dfec8db221fec7901b9064b6` |
| `notes/progress/2026-10-07-rec-desc-captured-name-lookup-stop.md` | `40fd2b16e4cd8b82aee03deae06c14684a7c078cffbcd8b69dc0dd931e9aeae0` |

Commit packet:

- Exact leased path: `notes/progress/2026-10-09-rec-init-boundary-attack.md`.
- Baseline SHA: `95307a281981cc4d2461b4f20e44d27a5f6b806a`.
- Dependency changes: none on initial check; final recheck in producer report.
- Claim/review: conditional earliest-publication theorem and bounded source
  blocker; compiler-referee PASS on SHA-256
  `4ff3285e7d460d0bd875d9dbbe5e11caa862190a927338c735e9fa3d67573fba`;
  frozen research-only, no gate closure.
- Checks: direct baseline fingerprints/bytes, narrow source inspection, local
  link and whitespace checks; no tests/builds/executable semantic experiments.
- Proposed message: `research: isolate recursive initializer first-read obligation`.
- Shared-record deltas intentionally left for primary/curator: link this
  conditional witness from REC_INIT without status promotion; record the
  initializer/read clause as the next premise. Leave REC_K, REC_DESC,
  MEMBER_DISCHARGE and RAW_SOURCE unchanged; no tasks/theory/index edits here.
