# REC-DESC constructive proof attempt: first constructor cut

Date: 2026-10-07
Baseline: `3cf6bb70b7514e6a17a3d3adb8fce0f4e7676c38`
Branch assigned: `research/simple-sub-intrusion`
Status: frozen, compiler-referee-reviewed research-only premise localization
Method: backward proof construction against the pinned clause inventory
Gates: REC-DESC, with DESC_CLAUSES / ADMISSION_CLAUSES / SEM_JOINT dependencies
Exclusive lease: this file only
Semantic and implementation authority: none added

## Objective and result

Attempt an actual constructor-by-constructor finite-reflection derivation,
using the retained finite source graph rather than another abstract compactness
schema. The first required inference cannot be instantiated: the supplied
independent `DescMem` judgment has no exhaustive displayed introduction/inversion
package from which its failure selects a particular ordinary descriptor clause,
with that clause's original operands and binder order. Source contracts §2.2
deliberately keeps that judgment independent; §3.5 takes its local constructor
typing lemmas as input.

This is a bounded characterization of the assigned sources and an explicit
proof-search stop. It proves neither finite reflection nor nonderivability in
the repository. No admitted Yulang counterexample was constructed. The new
contribution is the dependency cut between three concrete finiteness arguments
and the demanded negative descriptor inference. The previously supplied root,
Return and witness-fiber results remain dependencies; their conditional proofs
and logical falsifiers are not reconstructed here.

## Baseline, governing sections and claim classes

All semantic reads used pinned `git show 3cf6bb70b:<path>` blobs. Index/task
records were inspected only for navigation. The following scopes govern:

| Input | Exact scope and usable status |
| --- | --- |
| Source contracts §§2.1–2.2 | Generic finite relation graph and independently active joint `M_E`, `A_E`, `DescMem`; reviewed conditional package, concrete clauses Draft |
| Source contracts §§3.1–3.5 | Finite immutable source envelope, emitted constructor incidences, four independent admission cases, certified transport, conditional C-realization |
| Typed core §4 | Conditional executable simulation of a supplied finite typed derivation graph, including finite future uses and raw resumptions |
| Typed core §6 | Selected parameter roles and result normalization; generated source skeleton relative to supplied lexical/declaration and typing premises |
| Typed core §9 | Complete invocation, pending suffix and typed interaction directions; no finite presentation of arbitrary caller behavior |
| Ordinary computation §§2–5 | Draft ordinary state-threaded operational package; retained selected behavior, not exhaustive independent descriptor clauses |
| Recursive synthesis §4 / DAG FH | Conditional induction over finite admitted interaction derivations, pointwise at one old scoped assignment |
| DAG DESC_CLAUSES / ADMISSION_CLAUSES / SEM_JOINT / REC-DESC | Explicit open clause formation, common interpretation and finite-reflection obligations |
| Reflection localization / observation bridge / root-Return attempt / adversarial note | Retained conditional transport, immediate/root distinctions and witness-fiber obstruction; no premise promoted by this attempt |

The committed approved denotation answer `production-function-denotation-answer/d1`,
decisions 1–5, selects Option A's independently constrained complete typed
observations and separate admission. The membership answer
`production-function-bound-membership-answer/d1`, decisions 1–4, retains
Option 2's licensed conservative extras without universal source-constructor
evidence. The inlet answer `production-function-inlet-context-domain-answer/d1`,
decisions 1–5, includes all independently compatible punctured caller contexts
at the original interface and `(nu,K,D)`, including future/noncurrent uses.
They do not approve completed descriptor/admission clauses or implementation.

Established results below means only retained results within their stated
conditional scope. Candidate assumptions are explicitly identified inputs to
an attempted proof, not selected language rules. This artifact adds no
conditional compactness theorem and no independently reviewed result.

## Fixed proof obligation and hypotheses

Fix the actual provider knot, original descriptor `R`, actual provider `v`,
original binder tree and one original scoped `(xi,w)`, where `xi=(nu,K,D)`.
The static premise `S` must be independently proved and retain descriptor,
role, entry, ownership, scope and captured-lookup adequacy. No complete member
validation, successful Q result or reassignment of an old coordinate is an
input. FH is available only under its actual independent initial-W,
pointwise transition/member-check and exhaustive-admission premises.

The target is the pinned reflection implication:

```text
S(xi,w) and not DescMem(R,v;xi,w)
  => some independently admitted finite d with not L(d;xi,w).
```

`L` must be exactly FH's complete joint local judgment. If it contains an
existential event extension, its failure negates that entire existential:
one history whose every authorized compatible extension fails. Old `w`,
operation binders and overlapping event witnesses keep their original scope.
A failed individual proof or a failed selected extension is insufficient.

The needed first inference is ordinary descriptor **failure inversion**:
from the displayed failed `DescMem`, select a failed actual clause instance,
preserving any surrounding universal/existential binders. Its enumeration
must include immediate/root conditions, returned latent handles, carrier and
consumer obligations, and future eliminations where those belong to this
descriptor. This describes the required rule interface; it introduces no
clause, new predicate interpretation or semantic factorization.

None of the assigned sources supplies that exhaustive interface. Therefore
there is no actual clause instance on which to start the promised
clause-by-clause induction. Subsequent coverage, local readout, finite rank and
witness-coherence questions are downstream of this first cut.

## Constructor construction and the exact dependency cut

The smallest relevant returned-provider occurrence is the already retained
`result(name g)`. Its constructive source route is concrete:

1. With supplied `Gamma(g)=Value(R_g)`, typed core §6's Name row generates
   the data lookup and `Normalize(Value(R_g),name g)=result(name g)`.
   This establishes the source/result skeleton. It does not prove semantic
   adequacy of that captured lookup from Gamma identity alone.
2. Conditionally on the original typed lookup/relatedness premise identifying
   `eta_f(g)=v_g`, the Result inventory in source contracts §3.2 preserves
   that same returned descriptor/provider and current configuration:
   `Return(v_g,C_ret)`.
3. Ordinary computation §2 and source contracts §3.2 give
   `Return(v_g,C_ret) >>= Suffix = Suffix(v_g,C_ret)`.
   This fixes the actual handle and current state for an existing suffix.
4. To turn this emitted observation into complete constrained membership,
   source contracts §2.2 still requires the independent `DescMem` conjunct
   on the same whole tuple and `w`. C-realization §3.5 explicitly invokes
   the local descriptor typing lemma to supply that conjunct.

Consequently invoking §3.5 to prove that very local descriptor typing lemma
would put the sought lemma into the invocation's hypotheses. The source-rule
prefix through step 3 is available conditionally; step 4 is an independently
missing constructor premise. This is a metatheorem input/output cut, not a
new Result typing rule. No complete provider membership is obtained from the
source prefix, and no negative descriptor inversion follows from it.

The continuation operands also remain fixed before that cut. If an earlier
entry Force exposed `Request(q,C,k_arg)`, typed core §9 and source contracts
§3.2 retain `k_arg(response,current_state) >>= Suffix`, with rebind/body/
invocation-return in the original order. Raw resumption uses that current
resumed state and the original request witness; it does not restart receipt
or entry. A later new call of the actually returned `v_g` has its own ordinary
invocation. Inert Return provides neither such a call nor a substituted handle.
Ordinary §§3–5 retain current active authority rather than reviving an exited
receiver/handler. These operational facts determine the operands a future
descriptor clause must use; they do not supply its readout or admission proof.

## Why the available finite constructions do not discharge the cut

| Concrete construction | What its induction/rank proves | Missing connection to failed `DescMem` |
| --- | --- | --- |
| Source contracts §2.1, positive recursive reference clauses | Positive relation membership has a finite derivation using registered roots | No exhaustive ordinary descriptor complement rules or failure rank are supplied |
| C-realization §3.5 | An existing finite source-base membership derivation translates using same scopes and witness, given local descriptor typing | Local descriptor typing is a premise; translation cannot independently derive that premise or invert its failure |
| Typed core §4 code-label construction | A supplied finite typed graph yields finite shared code without recursive expansion; supplied executions/histories simulate | Administrative finite code does not bound the descriptor's semantic witness domains or generate arbitrary clients |
| Typed core §9 two-bit worklist | Each propagated direction has a finite typed root-path witness | Direction/path coverage gives no descriptor satisfaction/failure readout or complete caller-domain construction |
| FH §4 finite interaction induction | Supplied pointwise local checks hold on each independently admitted finite derivation | It does not show that a descriptor failure occurs at one such local check |

In particular, source contracts §3.1 expressly permits arbitrarily many and
arbitrarily long finite future interactions. Finite source code is not a finite
challenge set. §2.1's phrase “least relations generated by finite derivations”
specifies how positive `E` derivations are obtained. It does not supply a least
relation for ordinary descriptor failures, a finite bad-prefix law for complete
observations, or compactness of compatible existential witness fibers.
Applying that convention to `DescMem` would require an independently justified
descriptor rule/correspondence package; §2.2 supplies neither.

No compactness theorem can currently be instantiated: there is no specified
descriptor clause/witness space with the needed independent interpretation
and binder order. The stronger coherent-extension route suggested by the
adversarial note also cannot be instantiated without those actual clauses.
This attempt stops at their formation/inversion interface; it does not assume
a topology, finite witness alphabet, greatest fixed point or source-image
definition to pass the cut.

Root coverage remains precise: FH's zero-size case establishes W and has no
interaction check. An additional root condition must be independently read
from S/W or an actually validated zero-step judgment. Returning `v_g` cannot
replace that root obligation. Option 2 further prevents restricting the
production clause inventory to source-generated observations. No new bounds,
admission restrictions or observable language meanings are selected.

## Checks, coverage, resources and exclusions

An independent compiler-referee review found no blocking or major issue. It
confirmed the `DescMem`/C-realization premise cut, preservation of the original
assignment and handles, and the exact existential-negation requirement. The
review is limited to this proposed clause-by-clause proof method; it does not
show every possible finite-reflection proof must begin with failure inversion,
verify baseline blobs or hashes, or establish repository-wide clause absence.

Checks already run: full reads of `rules/research-lab.md`,
`rules/design-authority.md`, `rules/git-concurrency.md`; question-board rule
and committed approved-answer reads; bounded pinned-section `git show` reads;
`rg` path/heading discovery; SHA-256 and byte equality of the direct semantic
dependencies against baseline, current HEAD and working files. Broad output
captures that truncated were replaced by narrow operative-section reads.
The repository has no `spec/` directory at this baseline; no substitute spec
was invented. Failed locator reads are not evidence of semantic absence.

No tests, builds, checker, Oracle execution, Git mutation, child dispatch,
temporary research file or shared-record edit occurred. Seeds, numeric search
ranges, mutations and benchmark samples are inapplicable: this was one
constructive proof-search packet, not an enumeration or toy experiment.
There is no executable reference oracle, so oracle independence is not an
execution claim. The operational prefix and demanded descriptor theorem
share the pinned source premises; no supplied-transition checker is claimed
to validate those source rules independently.

Resource use: serial lightweight read/hash/write tooling; zero heavy processes
or builds. No numeric CPU/RAM/wall-time cap was supplied beyond bounded
research/no-build restrictions. Tool calls finished within 0.2 seconds each;
aggregate wall time, CPU time and peak RSS were not measured. No timeout,
killed run or partial computational search occurred. Repository-wide clause
absence, arbitrary source elaboration, semantic lookup adequacy, all-world
inhabitance, complete carrier/world membership, `M_E`, simultaneous member
discharge, principality and production conformance remain unverified.

Failure conditions for a future repair: selecting a descriptor interpretation
by source image or query success; treating Gamma/ID equality as lookup typing;
moving existential witnesses across old binders; returning a replacement
handle; resetting resumed state; dropping/replaying the pending suffix;
reviving expired authority; omitting independent root conditions; or using
source-base constructor evidence to exclude Option 2 extras. Any such repair
would fail this assigned proof obligation rather than close it.

Recommended next action: supply one independently specified exhaustive
returned-Function descriptor rule and its failure inversion at the original
binder order, with separate admission/readout operands. Then attempt its
actual constructor case. Do not expand toy probes while that same first
inference remains unsupplied.

## Frozen direct dependencies

All inputs below matched baseline, current HEAD and working files before this
note was written. No changed dependency hash was observed.

| Path | SHA-256 |
| --- | --- |
| `notes/theory/successor-proof-obligations.md` | `18bfa4e5bb461616ca17a0c9a1492f75ff7fca2f6231a13b3d68e0a3335136dc` |
| `notes/progress/2026-10-07-rec-desc-finite-reflection-localization.md` | `1ba67b64fe17d9cac3d558e25d11007db5f73761d7b80fd15e35aeca90fd18bc` |
| `notes/progress/2026-10-07-rec-desc-observation-finite-bridge.md` | `c1a89ab082e1e4560ac493a79260487668fe43cdead50d610224e4ef772e0183` |
| `notes/progress/2026-10-07-rec-desc-root-return-clause-attempt.md` | `3ee501a6611358777c4f1be99ba12794b9e0299f5c30404185f29d54d6e87637` |
| `notes/progress/2026-10-07-rec-desc-finite-reflection-adversarial.md` | `63b70f17794e0b8f21ef9079a0abaa05a75961b99cad0275c6d4d3f6179069c8` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-ordinary-computation-semantics-package.md` | `ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917` |
| `notes/progress/2026-10-07-successor-recursive-synthesis.md` | `e34a568946f5c1946c01828aae34e890747477ee8c272775408438acd95aa43f` |
| `questions/2026-10-05-production-function-denotation/approved-answer.md` | `7e7f3c717b16a70fc754c930a1654666c8b61a89a4861fca27b0ae3fa5f1890a` |
| `questions/2026-10-05-production-function-bound-membership/approved-answer.md` | `d9ddea04a44d2307cf587bc4ae9b2a1c50d062c4077306a5bf9ea9da00eca179` |
| `questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md` | `9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3` |

## Commit packet

- Exact changed paths: this note and `tasks/current.md` (primary status synchronization).
- Baseline: `3cf6bb70b7514e6a17a3d3adb8fce0f4e7676c38`.
- Changed dependency hashes: none observed; direct input hashes above.
- Claim/review status: bounded constructive premise localization, compiler-referee-reviewed, research-only; no finite-reflection proof, closed gate or production authority.
- Checks already run: pinned operative-section reads; direct dependency SHA-256/byte equality; narrow artifact readback and scope inspection. No tests/builds/probes. Primary owns final dependency revalidation and exact integration scope.
- Proposed one-line research-checkpoint commit message: `research: locate first recursive descriptor constructor cut`.
- Shared-record synchronization: `tasks/current.md` now records the reviewed constructor cut. DESC_CLAUSES, ADMISSION_CLAUSES, SEM_JOINT and REC-DESC remain open. No authority, theory map or question bundle was edited.

The research artifact is frozen after review; any theorem or semantic change requires a separately grounded source clause.
