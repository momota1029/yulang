# Original association: a uniform-witness discriminator

Date: 2026-10-07
Baseline: `5ab30adc94d9fd70aad37525fc0f73d4ff024833`
Status: frozen research-only artifact; compiler-referee review passed with a minor precision repair
Exclusive lease: this note only
Method: conditional relational model separation by quantifier order
Claim class: minimized countermodel to a candidate coverage implication
Semantic and implementation authority: none

## Objective and result

Test whether pointwise original-incidence coverage of a complete source Call
family supplies the uniform contribution witness sought by ORIGINAL_ASSOC.
The candidate pooled and factored kernels below agree on aggregate coverage
but disagree on that existential witness. The relational discriminator is
valid under its explicit candidate assumptions. Neither kernel is certified
as an independently interpreted original Yulang kernel.

No source semantics is adopted. This is not an original-association
counterexample. ORIGINAL_ASSOC remains open. The precise additional premise
to investigate is whether original contribution typing requires uniform
coverage of the same complete invocation family, or permits coverage by
alternative-indexed contributions whose aggregate covers that family.

The method does not repeat constructor elimination, primitive-leaf inversion,
slot-label reencoding, or Frozen Oracle archaeology. It examines the order of
the contribution witness and complete-observation quantifiers.

## Baseline, authority and retained facts

The governing sources are:

- [Inferred Function call views](../design/2026-10-05-inferred-function-call-views.md)
  §§1–5 and the integrated
  [function-call-view-formation/q1 a2](../../questions/2026-10-05-function-call-view-formation/approved-answer.md):
  source-derived shared contracts, stable static identity, distinct source,
  public and internal layers, scoped seed/refinement and Q independence.
- [Nested-block interpretation](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
  §§1–3: the sequential binding, inert final return and same outer capture.
- [Directional protection](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
  §§2–4: original upper-output protection without provider/lower backflow.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2.1–2.2, 3.1–3.5: independently interpreted kernel inputs, active original
  incidences, whole-tuple alternatives, complete Call content and separate
  admission/local descriptor-typing premises. These are conditional research
  clauses, not newly approved source rules.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §9: the complete invocation retains actual entry, body, designated consumer,
  native return delimiters and pending suffix.
- [ORIGINAL_ASSOC](../theory/successor-proof-obligations.md#original-assoc):
  inhabited original source-owned fiber over the complete invocation, with all
  original witnesses retained.

The four predecessor artifacts are the
[constructor attempt](2026-10-07-original-association-constructor-derivation-attempt.md),
[source/kernel audit](2026-10-07-original-association-source-kernel-audit.md),
[primitive-boundary inversion attack](2026-10-07-original-association-inversion-attack.md)
and [original-fiber audit](2026-10-07-successor-source-association-falsification.md).
The original assignment used nonexistent filenames containing
`source-association-inversion-attack` and `source-association-falsification`;
the last two links are their located counterparts.

The selected source stays fixed:

```text
my apply f = { my step x = f x; step }

call(result(name d_f), result(name d_x))
```

The second line is the previously minimized five-node proof cut, not a new
source program. Its environment retains the approved enclosing capture.
Both candidates share resolved declarations/definitions/uses, the symbolic
whole Call, ordinary argument, actual provider role/entry, original
owner/receiver/receipt facts, environment, scopes and the record
`xi=(nu,K,D)`. They share `beta`, original upper `p0`, seed/exposure provenance
and the distinct lower/provider provenance. No fact is constructed from type
shape, an ID, a completed solution or pending comparison Q.

Sharing these records does not certify satisfaction of every original
constraint: an undisplayed original kernel clause in K or D could require
uniform coverage and invalidate the factored candidate. Shared concrete
records must not be confused with established shared original semantics.

## Explicit candidate assumptions and models

The following assumptions define a relational fragment for this attack;
none is an adopted contribution-generation rule.

`C_alt`: an independently supplied provider relation has two distinguishable
original whole-tuple alternatives. Its complete receiver-invocation family
is `F = F_L union F_R`. Each alternative retains complete entry, body,
consumer, return and pending-suffix coordinates. This is a union of complete
relational alternatives, not a union of outward effect support rows. The
candidate declaration/provider alternatives are identical in both models.

`C_inventory`: for this candidate fragment only, the entire supplied original
incidence domain is `I(X)=I_L disjoint-union I_R`, with `I_L` and `I_R`
nonempty and their source-clause provenance matching the respective
alternatives. There are no additional incidences outside those two classes in
this candidate fragment. This parameterizes an exhaustive candidate inventory;
it does not derive a slot count for the selected source or allocate one slot
per execution, use or observation.

`C_contract`: each s has an incident contract record c_s and an ownership,
typing, scope and dependency witness w_s. Contract records have an explicit
complete-observation denotation. They are different sorts from static slots,
typed p0 and the rooted expression j_call. The fragment permits an
alternative-indexed complete subfamily as a contract denotation.

`C_active`: aggregate membership at the shared contract root is the union
of these active original incident contract predicates. Descriptor typing is
shared on all aggregate observations. Observation lookup can select an
already present whole-tuple alternative; it does not independently combine
port witnesses or change xi.

Keep every `(t_s,w_s)`, where `t_s=(beta,s,p0,c_s)`, in both candidates.
Only the interpretation of the contract predicates differs:

| Candidate | Contract denotation | Aggregate relation |
| --- | --- | --- |
| Pooled | Every c_s covers F | F |
| Factored | c_s covers F_L for s in S_L and F_R for s in S_R | F |

For a concrete relational witness choose two distinguishable complete
observations `O_L,O_R` with `F_L={O_L}`, `F_R={O_R}`. Each observation can be
read as an abstract full invocation record with the common typed entry,
receipt, consumer and return structure and a different original provider
alternative. This finite witness does not construct admitted source traces,
requests, raw resumptions or full challenge domains. General F_L/F_R may
instead contain all original pending and completed observations of their
alternatives; the argument needs exclusive observations in each side.

Source-derived beta/upper identity, role refinement, upper protection and
no-backflow can be interpreted identically throughout this fragment.
Unannotated seed and ordinary-value refinement keep the same shared root;
the actual provider role is preserved. Formation is independent of Q.
All source-indexed records can undergo one coherent whole-tuple renaming.
No annotation removal or dynamic grant is inferred. These observations check
compatibility with the selected directions within this fragment; they do
not prove source adequacy, callback-literal B-equivalence or validity of its
candidate contribution interpretation.

## Derivation and minimized discriminator

Let `Covers(t,w,O)` mean that O satisfies the interpreted incident contract,
with its original ownership, stage/view, scope and dependencies retained.
Compare:

```text
Pointwise:
  forall O in F. exists (t,w) in I(X). Covers(t,w,O)

Uniform:
  exists (t,w) in I(X). forall O in F. Covers(t,w,O)
```

Under C_alt/C_inventory/C_contract/C_active, every `(t,w) in I(X)` belongs to
exactly one of `I_L` or `I_R`, and both candidates satisfy Pointwise. Pooled
satisfies Uniform because every incident denotation covers F. Factored fails
Uniform: an incidence from `I_L` excludes O_R and an incidence from `I_R`
excludes O_L; the candidate incidence domain is exhausted by these two classes.

This preserves all witnesses. It neither chooses a representative incidence
nor identifies `s=c=p0`, `c=j_call`, or a static slot with a receiver boundary.
The relation I is candidate model notation, not a certified interpretation
of I_orig. If the original typed association demands one complete uniform
contract, Uniform is a necessary extensional condition for the target fiber;
it does not exhaust the original typing conditions.

The two-observation witness is minimal for refuting this implication.
For a one-observation family `{O}`, Pointwise supplies a witness covering its
whole family. An empty family has no nontrivial observation discriminator
and additionally depends on whether I is inhabited. The construction uses
the smallest nonempty observation domain where witnesses can vary; it makes
no minimality claim about Yulang source programs or original slot inventories.

## Why this is not a certified original-kernel separation

FVIEW §2 selects source formation and stable identity but explicitly leaves
the exact constructing judgments open. Source-contracts §2.2 requires active
original predicates and independently interpreted DescMem; §§3.2/3.5 retain
complete Call content and use local typing premises. These clauses do not
derive the quantifier exchange from the supplied aggregate relation.

They also do not certify C_contract or C_active as interpretations of the
original owner/view/signature kernel. In particular, complete observations
inside a contract do not establish that it is a complete contribution
contract for every alternative of the same original invocation. Calling an
alternative-indexed subfamily an original complete contract would assume
the unresolved typing law.

If original contribution typing requires each associated c_s to cover every
alternative of this complete invocation, factored fails that exact typing
premise. If an independently grounded original rule permits alternative-indexed
contracts with aggregate coverage, this pair could become a valid separation
of the proposed uniform-witness implication. Neither rule was established
by the assigned source sections. Pooled is also unverified as an original
kernel: coverage alone does not supply original licensing or contribution
typing. No exact approved condition has been shown to reject factored, and
no claim that it satisfies all original kernel premises is made.

This is the precise blocker. A checker implementing C_contract/C_active would
only replay the candidate premise. A larger finite domain or another kernel
truth-table would not independently validate that premise, so the lane stops
after this discriminator.

## Independence, coverage, checks and resources

No Frozen Oracle, executable semantic oracle or compiler implementation was
used. The reference is the pinned text of the governing clauses. The two
candidates share source/core and whole-invocation assumptions but differ in
an explicitly candidate contract interpretation. This producer report is not
independent review, and two implementations of these assumptions would not
prove their source authority.

Coverage is one fixed source/core proof cut and the two-observation conditional
relation argument. No parsed-source search, all-world enumeration or admitted
source row was constructed. Seeds/ranges, executable mutations, search shards
and performance samples are not applicable. The conceptual mutation is
whole-family versus alternative-family contract coverage; it was not executed.

Commands used: bounded cat/sed/rg reads, read-only `git rev-parse HEAD`, and
Python SHA-256/byte comparison with read-only `git show <baseline>:<path>`.
Early combined captures truncated; decisive governing and predecessor sections
were reread in bounded windows. All fourteen inputs below matched pinned
baseline bytes before writing and at handoff. Note-local inspection checks
links, trailing whitespace and the exact leased diff; these are artifact
integrity checks, not semantic tests.

One output lease, zero compiler/cfg(test) edits, tests, builds, checkers,
formatters, Git mutations, questions or children. Lightweight read batches
used at most five concurrent commands; no heavyweight process ran. No numeric
CPU/RAM/wall-time budget was supplied. Aggregate CPU time, peak RSS and elapsed
wall time were not instrumented.

Unverified: C_alt/C_inventory as original inputs for this source, independent
complete original contribution typing, the full original K/D kernel,
association/licensing, complete profiles and admission, general sources,
annotations/recursion, principality, source adequacy and production conformance.
No required gate is closed by this note.

Recommended next action: inspect the original contribution-typing clauses
specifically for uniform coverage versus alternative-indexed aggregate
coverage. Return a proof of the uniformity law or an independently typed
factorization witness before running any larger model probe.

## Frozen dependencies

SHA-256 values below pin the fourteen compared inputs. Rules and the theory
map are operating/target locators; the source sections above supply the
semantic premises. No dependency hash changed relative to the baseline.

| Path | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/theory/successor-proof-obligations.md` | `18bfa4e5bb461616ca17a0c9a1492f75ff7fca2f6231a13b3d68e0a3335136dc` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/progress/2026-10-07-original-association-constructor-derivation-attempt.md` | `bfd197a094a6fa3e813325a40c361687ed609ad45aa89af9908f58ce240b5435` |
| `notes/progress/2026-10-07-original-association-source-kernel-audit.md` | `509e9af6be0ae3b3560f1fd7ca8e9c06572bb65e1351b114b0e2e5e13061b202` |
| `notes/progress/2026-10-07-original-association-inversion-attack.md` | `c8aa0c87d078cdc2d1976bbe00e925f33177c761ae9cb196ce3d3ae79cf84a83` |
| `notes/progress/2026-10-07-successor-source-association-falsification.md` | `09a4aee423985c03f1365574e1d4572e67cc6b2f3f3c25fa747b711bbe304738` |

## Commit packet

- Exact leased/changed path:
  `notes/progress/2026-10-07-original-association-uniform-witness-discriminator.md`.
- Baseline SHA: `5ab30adc94d9fd70aad37525fc0f73d4ff024833`.
- Changed dependency hashes: none; fourteen input byte comparisons match.
- Claim/review status: research-only conditional relational discriminator;
  compiler-referee review found one minor domain-exhaustiveness precision issue,
  repaired below; no source semantics adopted, original counterexample or
  ORIGINAL_ASSOC closure.
- Checks already run: governing-section/predecessor reads, candidate premise
  and quantifier derivation inspection, initial/final pinned-byte comparisons,
  exact-note link/whitespace/hash and leased diff inspection. No runtime tests.
- Proposed one-line checkpoint message:
  `research: isolate uniform witness premise in original association`.
- Shared-record deltas left for primary/curator: optionally record the
  pointwise/uniform distinction under ORIGINAL_ASSOC, with original
  contribution typing still the blocker. No task/index/authority promotion,
  language decision, question-board bundle or production change is proposed.

An independent compiler-referee review confirmed the pointwise/uniform
discriminator and its non-authoritative scope. Its minor finding required the
candidate incidence domain to be stated exhaustive; `C_inventory` now defines
`I(X)=I_L disjoint-union I_R` for this candidate fragment and the failed
uniform quantifier descends over that complete domain. The repair adds no
Yulang slot-count or original-kernel claim. Whole source semantics, dependency
byte certification, production behavior and original contribution typing
remain unverified.
