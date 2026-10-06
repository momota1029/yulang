# Original association: assembly existence versus witness preservation

Date: 2026-10-09
Baseline: `df1b80af6ad3c40cc08feea28acea0def65b30aa`
Status: frozen spec-audited research-only adversarial derivation
Gate/method: ORIGINAL_ASSOC; finite witness-level separation, with LIC_INVERT as the preservation consequence
Exclusive lease: this file only
Semantic and implementation authority: none

## Objective and result

Attack the [candidate contract](2026-10-08-original-call-kernel-contract-candidate.md)'s
conditional assembly lemma without repeating the prior pointwise/uniform
discriminator. The tested issue is whether complete-family witness existence
also licenses replacing the original witness relation by assembly outputs.

**Result:** the conditional lemma is valid under its stated assembly premise.
It does not establish witness-exhaustive representation or licensing inversion.
A one-observation, two-witness abstract presentation satisfies its assembly,
incidence and uniform-coverage premises while an assembly-image replacement
loses one licensed original witness. The candidate makes no such replacement;
this is a counterexample to an additional preservation implication, not a
counterexample to the candidate lemma, approved Option 2, or the original
Yulang kernel. No blocking defect in the candidate was established.

## Governing scope and retained results

Exact sources: [FVIEW](../design/2026-10-05-inferred-function-call-views.md)
§§2/5; [source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
§§2.1/3.5/6.1, with §3.7 read for the explicit Option 2 presentation; the
integrated [Option 2 answer](../../questions/2026-10-05-production-function-bound-membership/approved-answer.md)
q1/d1; and the DAG's
[ORIGINAL_ASSOC](../theory/successor-proof-obligations.md#original-assoc),
[LIC_FORWARD](../theory/successor-proof-obligations.md#lic-forward),
[LIC_INVERT](../theory/successor-proof-obligations.md#lic-invert).
The DAG locates targets; it does not define a new witness sort or source rule.

The selected nested `apply/step` source, directional upper-output protection,
actual callable roles/entries, original static slots, scopes and one shared
`xi=(nu,K,D)` remain fixed. This note proposes no interpretation of their
unselected slot/contribution judgments. FVIEW does not equate a static slot
with an activation. Option 2 permits licensed conservative observations without
source-constructor witnesses; it does not permit arbitrary port-compatible
observations or select a concrete production grammar.

The candidate's embedded architect/compiler-referee record is the available
review context. Its original assembly/coverage premise is explicitly unproved.
Those reviews are not independent review of this artifact. The
[earlier discriminator](2026-10-07-original-association-uniform-witness-discriminator.md)
already separates pointwise from uniform coverage using disjoint observation
subfamilies. The
[later adversarial cut](2026-10-08-original-call-association-adversarial-cut.md)
records why enlarging that model leaves original contribution typing untouched.
The witness below instead gives both original witnesses identical full
coverage: no quantifier exchange fails.

## Explicit hypotheses and minimized witness

The following are **candidate abstract hypotheses**, not established original
kernel facts. They fix a finite presentation permitted by the generic relation
grammar, conditional on its independent primitive contracts.

1. Fix one original coordinate tuple
   `q=(X,beta,p0,u,scopes,xi)` and one independently admitted challenge. All
   providers, dependencies, stage/view incidences and descriptor constraints
   belong to one whole tuple `y*`. Neither `Q` nor a solved shape is used.
2. Let the whole-observation projection be `z*=Pi(y*)` and the complete family
   for this abstract fragment be `F={z*}`. Association witnesses are separate
   from the observation they cover. Their distinction is not erased from the
   kernel even though their observed tuple is the same.
3. Let the source-observation base be empty, `R=empty`, and let two independently
   supplied primitive evidence alternatives `Z0` and `Z1` both denote `y*`,
   with distinct retained local relation witnesses `w0,w1`. Set `G={y*}` and
   `W=empty`. Thus the §3.7 presentation has the finite union of two guarded
   conservative leaves and `H_G(R)={y*}`. No source execution is an admission
   or membership premise of either leaf. Descriptor typing, authority and the
   admitted challenge are hypotheses, not consequences of this tiny grammar.
4. Suppose the independently interpreted original kernel has exactly two
   distinct licensed incidences `I_orig(q)={a0,a1}`, retaining `w0,w1`, and
   both are typed at `q`. Both cover the same **complete** family:

   | Original witness | Incident at q | Covers z* | Original license |
   | --- | --- | --- | --- |
   | a0, retaining w0 | yes | yes | L0 |
   | a1, retaining w1 | yes | yes | L1 |

5. Suppose the supplied schema fragment has one coherent licensed schema `T0`
   realizing `a0`, and its original assembly is `A(T0)=a0`. It retains every
   required coordinate and proves coverage from that arm. No hypothesis says
   this schema fragment represents every original license.

Step 3 is an illustrative Option 2 presentation, not a certification that
this particular empty source base or its conservative leaf is the execution
or production membership of the selected Call. Its only purpose is to keep
the witness-loss attack compatible with the allowance of unanchored extras.
Distinct local evidence is an explicit premise; if the eventual original
kernel identifies these witnesses, this particular separation does not apply.

**Derivation.** The factored formula holds using `T0` and `a0`. Assembly returns
the same `a0` incident at `q`. Uniform coverage holds; indeed both `a0` and `a1`
cover every member of `F`. Consequently the candidate's conditional conclusion
is true. However, replacing the original kernel by
`I_assembled={A(T0)}={a0}` removes `a1` and its `L1/w1` origin. Membership after
projection and complete-family coverage remain identical. An inverse ranging
only over `I_assembled` cannot account for every original licensing witness.

This refutes only the implication

```text
factored coverage + original assembly + uniform existence
    => exhaustive original-witness preservation by assembly-image replacement.
```

It does not refute the candidate's displayed implication. The candidate keeps
`I_orig` unchanged, says every legitimate arm remains available, and separately
requires exhaustive P4 licensing inversion. An existential construction need
not enumerate or replace its domain.

**Minimality.** Two distinct original witnesses are necessary to lose an
alternative while retaining a witness to existential coverage. One observation
is the smallest nonempty family; both witnesses cover it, so the effect is
independent of the previous two-observation quantifier separation. An empty
family can exhibit witness loss too, but would add vacuity without strengthening
this result. No minimality is claimed for Yulang programs, slot counts or the
eventual original kernel.

## Premise audit: emptiness, incidence and conservative contributions

- **Empty family:** `F=empty, I_orig=empty` satisfies pointwise and an empty-arm
  factored coverage formula, but fails uniform existence. It fails the
  candidate's explicit premise that original assembly constructs an original
  `a_T`, including when there are no arms. The candidate already states this
  existential requirement. This is a boundary check, not a new countermodel.
- **Incidence:** constructing a covering tuple at a different scope, slot or
  joint assignment violates the candidate's explicit incidence-preservation
  premise. Pointwise incidence alone cannot justify that assembly premise.
  No independently licensed original instance of this failure was found.
- **Conservative contributions:** source-contracts §3.5 preserves a primitive's
  same local relation witness, including independently certified conservative
  alternatives in that source base. Full production extras require §3.7's
  separate grammar/accounting. Neither scope requires every conservative
  observation to be an executed source event. Replacing a full witness relation
  by one source-only or canonical assembly image would require another proof.
- **Allowances:** §6.1 covers both Bind allowances and complete Call receiver
  output even when constituents are not reached. A witness based only on
  reached execution would fail that conditional validity rule. The candidate
  expressly retains complete contributions; this attack supplies no counterexample
  to its accounting.

For a future representation theorem, require a witness-level correspondence
whose inverse reaches every original licensing arm and preserves its local
witness, coordinates and contribution dependencies. Surjectivity of the single
assembly map is not inherently necessary: the original witnesses could remain
as separate retained evidence, or a certified representation could preserve
them inside an assembled witness. What is insufficient is equality after `Pi`
or existential coverage alone. This is a proof obligation, not a selected new
language rule or a demand that all original witnesses be canonical or uniform.

## Independence, limitations and stopping point

Claim classes: the displayed separation is a conditional finite mathematical
counterexample; the current candidate's assembly implication is a conditional
theorem relative to its stated premise; compatibility with the selected Call's
actual original kernel is unverified. The governing decisions are established
only in their published scope. No gate, source association, exhaustive licensing
inverse or production conformance is established by this note.

No Oracle, executable semantic reference, checker, search, mutation run, test
or build was used. Oracle independence is therefore absence of Oracle evidence,
not independent validation of original rules. Shared assumptions are the
primary's fixed source meaning and the text's generic relation grammar. The
primitive `Z`, evidence distinction, typed original incidences, complete-family
interpretation and assembly are candidate inputs. Implementing those inputs
in a checker would only establish consistency relative to them.

The conceptual mutation is `I_orig -> image(A)` with unchanged coverage and
projection. Failure conditions are a proof-irrelevant original kernel, an
already exhaustive certified representation of both local witnesses, or a
violation of the independent hard envelope by `y*`; each prevents this abstract
witness from being an original counterexample. No random seeds, numeric ranges,
search shards or repetitions apply. An attempted global absence claim, complete
source typing, recursive/generalized source licensing, full original kernel
interpretation and production behavior are omitted.

The decisive blocker to a genuine original counterexample remains the
independent kernel's witness/evidence and contribution rules. The prior
pointwise discriminator and this different preservation discriminator cannot
supply those rules. Stop here rather than produce a larger equivalent probe.

Recommended next action: retain the candidate as conditional, and ask the
original-kernel rule producer to supply an exhaustive witness-preserving
licensing correspondence alongside any proposed assembly interpretation.

## Commands, resources and frozen inputs

Commands/checks: bounded `cat`, `sed -n`, `rg` reads; read-only
`git rev-parse HEAD` and exact leased-path `git status`; Python SHA-256 and
byte equality against `git show <baseline>:<path>`. All fourteen dependencies
below matched baseline bytes. Initial mixed captures truncated; decisive
candidate, source-contract and predecessor windows were read separately.
Final verification rechecks dependencies and note-local whitespace/links.
These are artifact-integrity checks, not semantic testing.

One leased note, no other write output, no Git mutation, no child, no compiler
or test edits. At most four lightweight read processes were batched; no
heavyweight process ran. No numeric CPU, memory or wall-time budget was supplied.
Aggregate CPU time, peak RSS and elapsed wall time were not instrumented.
There is no incomplete enumeration or timed-out calculation.

| Direct frozen dependency | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `rules/question-board.md` | `8c617ceb978dfa26ce12f4f71ecc8ece22ffd8f1cf1982125b33142f645ae1c0` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/theory/successor-proof-obligations.md` | `18bfa4e5bb461616ca17a0c9a1492f75ff7fca2f6231a13b3d68e0a3335136dc` |
| `notes/progress/2026-10-08-original-call-kernel-contract-candidate.md` | `b401a3331ab96eb2668fd7d9bb7ec9488482c0550570f24ab3c29e071320246f` |
| `notes/progress/2026-10-07-original-association-uniform-witness-discriminator.md` | `8489cf7dff6cdd2d04ba25f6995bd1450592f68f2e6dc3c9c1ceaa36c0bd9161` |
| `notes/progress/2026-10-08-original-call-association-adversarial-cut.md` | `5f64bec692c2d6ee8c951405a290c0d94c7c21556c067666c740c84abbd7367d` |
| `questions/2026-10-05-production-function-bound-membership/question.md` | `9e3db61cfae6b08401fe5d49c7b14f9ac7ade1c206389e835b9a82cb30d9bbe8` |
| `questions/2026-10-05-production-function-bound-membership/answer-draft.md` | `bafa387d69ffb7e570384be82a979ea74588568d93b1752eba2fdced43aa5cee` |
| `questions/2026-10-05-production-function-bound-membership/approved-answer.md` | `d9ddea04a44d2307cf587bc4ae9b2a1c50d062c4077306a5bf9ea9da00eca179` |
| `questions/2026-10-05-production-function-bound-membership/receipt.md` | `f69a924b52e0cfb198df62a33e7e5c358ee1d0799ecf7c16cf32b9f8cb2f7e98` |

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-09-original-association-uniform-witness-falsifier.md`.
- Baseline SHA: `df1b80af6ad3c40cc08feea28acea0def65b30aa`.
- Changed dependency hashes: none; fourteen direct input comparisons match.
- Claim/review status: frozen conditional preservation discriminator;
  spec_auditor PASS on SHA-256
  `1e5620baf614bb4c05d05eaa83d5397574fccae7102a77a4e23fe6d05e7ee02d`;
  no original-kernel falsifier or gate closure.
- Checks already run: exact governing and predecessor sections, committed
  Option 2 bundle byte equality, dependency hashes, leased-note integrity.
  No semantic checker, tests or builds.
- Proposed one-line research-checkpoint commit message:
  `research: separate original assembly existence from witness preservation`.
- Shared-record deltas intentionally left for primary/curator: optionally
  attach this preservation boundary to ORIGINAL_ASSOC/LIC_INVERT; retain their
  open status and existing uniform target. No task/index/authority, question
  bundle, grammar, compiler or test change is proposed.
