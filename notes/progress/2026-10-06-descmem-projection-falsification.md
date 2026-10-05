# Production Function projection attack: oracle and envelope obstruction

Date: 2026-10-06
Status: independently reviewed bounded research checkpoint; production gate open
Method: adversarial finite-domain audit, stopped before executable enumeration
Baseline: `4b8896bdad558431f09f1221661a10a1c8271469`
Lease: this note and `tools/research_descmem_projection_falsification.py`

## Objective and claim class

Test endpoint-only/portwise membership, dropping argument-side `d+`, flattening
nested effect positions, and comparison-dependent admission at one original
`xi=(nu,K,D)` fiber, using the pinned quiet/capturing returned-provider pair.
The assignment requires an independently source-grounded production oracle
and explicitly says to stop if none is available. That prerequisite fails.
No checker was created or run. This is a precise blocker and bounded audit of
the proposed falsifiers, not a source counterexample, a definition of
`DescMem_A`, or a completed production theorem.

The approved Option A fixes the original complete `Rel_C` basis and joint
typed constraints. Option 2 permits independently licensed production members
beyond `P_ref`. Neither approval supplies the missing descriptor-membership
or punctured-context admission clauses. In particular, absence from `P_ref`
is not a production rejection oracle.

## Governing premises and dependency boundary

The primary corrected an invalid transcribed baseline before any write. Only
the corrected baseline above is used. The primary confirmed the committed,
unchanged question-board handoffs and integration receipts.

- `questions/2026-10-05-production-function-denotation/approved-answer.md`,
  exact approved decisions 1–5: Option A, Option 2, joint constraints,
  comparison-independent admission, and unfinished concrete rules.
- `notes/progress/2026-10-05-production-function-denotation-followup.md`,
  Accepted scope, Direct derivation attempt, Next proof attack, Paired
  latent-provider derivation probe, and Constant-provider certificate
  refinement: these are headings rather than numbered sections in this file.
- `notes/design/2026-10-05-source-contracts-and-common-allowance.md`
  §§2.2, 3.3–3.7: active membership is an interpretation hypothesis;
  constructor typing must supply its descriptor conjunct; `H_G(R)` is only a
  sufficient abstraction shape and is not selected production semantics.
- `notes/design/2026-10-02-typed-computation-core-elaboration.md` §§6, 8, 9:
  source role/entry generation, conditional fixed-domain guarantee weakening,
  and the joint argument/complete-invocation/body distinction.
- `notes/design/2026-10-04-source-generated-callback-structural-theorems.md`
  §§2.1–2.4, 3: decorated finite immutable source envelope, distinct `d-`,
  `d+`, `b+` occurrences, and independent source admission.
- `notes/design/2026-10-04-source-indexed-callback-realization.md` §§3–4:
  reference constructor transitions, one whole-observation projection, and
  query-independent reference domains.

All direct governing paths checked against the corrected baseline were
unchanged. Unrelated live edits were not consumed. Draft/conditional source
constructions remain conditional; their review does not make arbitrary
production endpoint interpretation established.

## Minimized finite obligation table

Use exactly two returned providers: quiet `Q`, and `E` whose body invokes the
captured `op`. Use a pure supplied `Q` in the pinned outer call and a pure
Unit carrier in the one later invocation. Keep original scope, receiver,
receipt, body/result consumer, request witness and continuation in the full
state. The optional request is the single captured operation. Assume the
decorated source typing and separate admission certificates required by
Theorem C; in particular, the quiet provider's use at the common `G` requires
the conditional certificate identified in the pinned follow-up.

`s0` is the outer call state, `s1(p)` the state after returning provider `p`,
and `s2(p)` its one admitted future invocation. Ordinary Value entry forces
each pure carrier, rebinds, and enters the appropriate body. In the quiet
lane the body returns Unit. In the capturing lane the body exposes the
original `op` request and its original raw continuation. No response or
resumption is enumerated. These are reductions of the source/reference
rules above, not newly chosen production transitions.

| Provider / state | Argument-origin request contribution `d+` | Body request | Source/reference observation | Production `DescMem_A` verdict |
| --- | --- | --- | --- | --- |
| `Q`, outer `s0 -> s1(Q)` | empty | none | return latent provider | underived |
| `E`, outer `s0 -> s1(E)` | empty | none | return latent provider | underived |
| `Q`, future `s1(Q) -> s2(Q)` | empty | none | return Unit | underived |
| `E`, future `s1(E) -> s2(E)` | empty | original `op` | request with retained witness/continuation | underived |

The two candidate information projections are (1) the printed outer four-port
skeleton, identical on both lanes, and (2) the unpositioned set of exposed
operation names across the inspected history. The second separates quiet
from capturing after future use, but has no field distinguishing argument
from body contribution or outer from latent invocation. A production
accept/reject algorithm using either projection has not been specified.

The table is an obligation map, not an executable membership model. It has
four observation rows, two providers, one future invocation per lane, at most
one operation request per history, and no random seeds. Every row is included;
there is no incomplete search hidden behind a passing count.

## Mutation outcomes and exact failure conditions

| Mutation | Discriminating outcome in this envelope | Exact unresolved premise |
| --- | --- | --- |
| Endpoint-only membership | The outer skeleton loses the future request distinction, but no production membership mismatch can be assigned | Independent joint `DescMem_A` rule, including constructor typing and licensing of conservative members; different reference histories alone do not prove different production verdicts |
| Product of port marginals | This pinned pair supplies no separate discriminator for the product: its latent `op` distinction may remain in the port marginals | A distinct correlated-tuple witness would be needed to show that multiplying the marginals introduces a tuple absent from the joint relation, followed by an independently derived production membership verdict |
| Remove argument-side `d+` | No request discriminator: `d+` is empty in all four rows | Need a separately certified effectful incoming carrier, beyond the pure carrier used here; reclassifying the captured body request as `d+` would be false |
| Flatten nested effect positions | Unpositioned support erases location, but still separates these two histories by `op` presence | Need a specified position-sensitive satisfaction rule and a candidate that uses the flattened support; absence of a field alone is not a proved accept/reject mismatch |
| Admission depends on pending comparison `Q_pending` | Directly violates the accepted independence requirement if its result actually changes with `Q_pending` | No independent production `A_A` is available for an acceptance table; this mutation is already ruled out by the decision, not discovered by finite execution |

The smallest counterexample to dropping `d+` cannot be extracted from this
pure-carrier pair: deleting an empty request contribution changes no request
in the table. Typed-core §9 already explains how a certified incoming carrier
that requests before returning would discriminate that source-execution
shortcut. Repeating that existing reference reduction would not establish
production membership and is outside this lane's useful next experiment.

For endpoint-only membership, using `P_ref` as the expected result would
silently impose the rejected source-constructor completeness requirement.
For flattened positions, assigning a row-union guarantee would silently
select a rule that typed-core §9 explicitly leaves as a complete relational
image. For admission, defining it by success of the target comparison would
build the forbidden circular premise into the checker. These are distinct
failure conditions; none is repaired by a larger enumeration of the same
two providers.

## Oracle independence and stopping point

There is an independent documentary reference for source execution: the
constructor equations precede the candidate shortcuts. A checker transcribing
those equations could check consistency and catch a source-execution mutant.
It would share the supplied decorated typing, operation contract, profiles,
admission certificates and original `xi`. It would not independently validate
those source premises or derive the production constructor-typing bridge.

No inspected source defines the required production verdict on these tuples.
Source-contracts §2.2 explicitly takes `DescMem` as independently interpreted;
§3.5 assumes local descriptor typing lemmas; typed-core §8 assumes an original
complete certificate; reference realization §§3–4 defines `P_ref`, not the
Option A production predicate. Thus substituting the reference generator as
oracle would leave the assigned premise untouched. The explicit stop
condition applies before the first executable attempt.

No impossibility of expression in existing `Rel_C`, `K,D` or evidence is
claimed. The missing object is a derived predicate, not a demonstrated need
for a new carrier or language choice.

## Checks, resources and recommended action

Checks already run: read the three required rules in full; inspect the named
governing sections; inspect both committed integration receipts;
`git diff 4b8896bdad558431f09f1221661a10a1c8271469 --` on the six initially
named governing artifacts returned empty; compute direct dependency SHA-256
hashes. No Git mutations, builds, formatting, tests, executable probes or
measurements were run. Lightweight executable budget consumed: 0 of 1.
CPU/RAM and total wall time were not measured. Shell reads were small; no
heavyweight process was launched.

Unverified: production `DescMem_A` and `A_A`, production acceptance, recursive
or repeated latent use, responses/resumptions, ambient handler images,
effectful argument carriers, principal schemes and unrestricted Option 2
extras. No compiler path or Oracle fixture was tested.

Recommended next action: derive one comparison-independent joint descriptor
satisfaction clause and constructor-typing lemma for the returned `G`, from
the original typing/evidence kernel. Only after that premise is available
should a finite membership attack allocate concrete oracle verdicts.

## Dependency snapshot (SHA-256)

| Path | Hash |
| --- | --- |
| `questions/2026-10-05-production-function-denotation/approved-answer.md` | `7e7f3c717b16a70fc754c930a1654666c8b61a89a4861fca27b0ae3fa5f1890a` |
| `questions/2026-10-05-production-function-denotation/receipt.md` | `8654359c41d2bf4871904d017d0282155d8763496986a3254405a1220318708b` |
| `questions/2026-10-05-production-function-bound-membership/approved-answer.md` | `d9ddea04a44d2307cf587bc4ae9b2a1c50d062c4077306a5bf9ea9da00eca179` |
| `questions/2026-10-05-production-function-bound-membership/receipt.md` | `f69a924b52e0cfb198df62a33e7e5c358ee1d0799ecf7c16cf32b9f8cb2f7e98` |
| `notes/progress/2026-10-05-production-function-denotation-followup.md` | `c625dd2b9bf73afc250d3d51cc7a04937aaad9881cf9c5def20e74082cd8509a` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` | `568bb4649ba278519f3ad01af2091dd1baaca42850cd19e3b5734b3c47c2eefe` |
| `notes/design/2026-10-04-source-indexed-callback-realization.md` | `76874a219ac86068027b1f08a5bc27a12d93a0169a52cebd896a6ff6f2c6b671` |

## Commit packet

- Exact lease: `notes/progress/2026-10-06-descmem-projection-falsification.md`
  and `tools/research_descmem_projection_falsification.py`.
- Changed path: only the leased note; the checker path was intentionally unused.
- Baseline: `4b8896bdad558431f09f1221661a10a1c8271469`.
- Changed dependency hashes: none observed; snapshot above.
- Review status: independently reviewed; the initial minor finding separating
  endpoint-only membership from port-marginal products was repaired and
  delta-reviewed. This remains a research-only blocker, not gate completion.
- Checks: source/receipt inspection, baseline governing diff, dependency hashes;
  no executable run because the independent production oracle is absent.
- Proposed commit: `Record production projection oracle and envelope blocker`.
- Deferred shared deltas: primary/curator may link this blocker and record that
  the pinned pure-carrier pair does not discriminate dropped `d+`; no theorem,
  design-index, task, authority or question-board path was modified here.
