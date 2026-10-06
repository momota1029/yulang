# Original formal-profile introduction: finite inversion stop

Date: 2026-10-06
Status: Unreviewed research; bounded derivation obstruction and conditional transport ancestry; no semantic or implementation authority
Baseline: `bb45955082ad885ea63687908b8cf852912c99ed`
Lease: this file only
Method: finite derivation inversion; no executable model or Oracle execution

## 1. Objective and result

Attempt `I-formal` / `N-formal` from the independently specified original
source rules for the selected component:

```text
my apply f = { my step x = f x; step }
```

The attempt stops at the **original formal profile supplied by source elaboration
to the decorated transport rules**.
The pinned sources do not specify a rule deriving that input from the resolved
formal declaration/definition component, or an exhaustive set of alternatives
for such a rule. Consequently no finite original-rule inversion establishes
`N-formal`, and no original-rule derivation refutes it. This is a precise
missing-rule result within the inspected dependencies, not an assertion that
the language permits an extra original position.

The positive Call construction is retained. Its generated `p0` does not define
the inventory that the original formal rule must independently derive.
`N-call` and `N-other` are separate obligations and are not investigated here.

## 2. Fixed dependencies and claim classes

The exact governing sections are:

- [Inferred call views §§2–5](../design/2026-10-05-inferred-function-call-views.md#2-source-formation-direction): shared source contract, stable original identity/scope, one joint `xi`, provisional full protection, same-root ordinary-value refinement, and explicitly open formation judgments.
- [Source contracts §§2–3,10](../design/2026-10-05-source-contracts-and-common-allowance.md#2-an-independently-interpreted-constrained-presentation): conditional interpretation and emission over supplied decorated inputs, finite derivations, and whole-coordinate scheme certificates.
- [Typed-boundary §6](../design/2026-10-02-typed-boundary-realization-draft.md#6-common-typed-view-transport): profiles supplied by source elaboration; indexed relational images preserve input witnesses and tags.
- [Formation attempt §§3–6](2026-10-06-formal-profile-formation-rule-attempt.md#3-formation-interface-before-choosing-missing-rules): candidate formation interface, unknown `I-formal`, conditional completeness and exact `N-formal` premise.
- [P/A review §4](2026-10-06-source-generation-pa-review.md#4-smallest-remaining-source-introduction-clause): the original first-introduction converse remains unproved.

The [nested-source addendum §2](../design/2026-10-06-nested-block-function-source-realization-addendum.md#2-selected-source-meaning)
fixes the source tree below. The [Call construction §§3–4](2026-10-06-source-call-generation-construction.md#3-exact-input-roots-and-whole-argument-distinction)
supplies the positive static address/origin. These dependencies preserve the
accepted selection 2 and source meaning; this note makes no alternative choice.

**Established dependency results:** same source identities and captured root;
positive static Call seed; decorated typed transport algebra.
**Conditional result here:** ancestry for a finite chain of those supplied
transport steps, as proved below.
**Candidate assumptions:** any exhaustive original formal-introduction rule
table, including one that would establish `N-formal`.
**Bounded characterization:** the precise inversion cut in these ten pinned
dependencies. No theorem about the complete original source relation is proved.

## 3. Exact hypotheses and available inversion

Fix the resolved finite component `C`, original scope tree `sigma`, shared
formal root `R_f`, `beta=(d_f,R_f)`, and one whole `xi=(nu,K,D)`. The approved
tree is:

```text
lambda(f,
  bind(step,
    result(lambda(x, call(result(name f), result(name x)))),
    result(name step)))
```

`name f` resolves to the outer formal. The final `step` returns that captured
function without invoking it. No source annotation is present for `f`.
Neither a solved Function shape nor pending `Q` success is an input.

Write `Pi_f` for the original formal signature profile. This is a placeholder
for the independently derived profile, not a definition of its inventory.
Typed-boundary §6 calls the supplied signature profile `Gamma`. Distinguish
that profile from the lexical environment and from an activated boundary.

The precise available transport inversion is:

```text
chi_out = union_i (M_i)_* chi_i
chi_out(p',b)  =>  exists i,p. chi_i(p,b) and M_i(p,p').
```

Hypotheses for iterating it: a finite packet derivation contains only these
indexed transport steps; each correspondence and input profile is supplied
by the decorated source derivation; source tags, original identities and
the common `xi` are retained. Contributions and original introduction
certificates are tracked alongside profile membership, rather than recovered
from boundary-ID equality.

**Conditional ancestry derivation.** At the final image choose its indexed
input witness. Repeating at every preceding image decreases the number of
transport steps in the finite derivation. It terminates at an input profile
witness with the same original source tag and boundary references. This
constructs a path and source ancestry; it does not construct that terminal
input profile. Scope-renaming steps can be crossed only with the separately
supplied whole-coordinate certificates of source-contract §3.4.

If the terminal witness is a supplied formal profile `Pi_f`, this inversion
has no further introduction premise to inspect. Typed-boundary §6 explicitly
states that signature profiles are supplied by source elaboration and that
deriving them from syntax remains a gate. Its fresh dynamic boundary record
contains this supplied profile; the record's introduction cannot classify
the static original positions inside it.

Thus the transport spine has the following partial inversion shape, **not a
new source typing rule**:

```text
output witness
  -> matching tagged input witness through each supplied image
  -> original formal-profile witness in Pi_f
  -> [no specified original I-formal rule to invert]
```

This does not prove that every raw-source step is an image. The input-profile
cut already prevents the formal-introduction proof before that separate
exhaustiveness question would become useful.

## 4. Why the other specified premises do not cross the cut

Source-contract §3.1 explicitly starts with supplied actual roles, entry,
typed paths, owners, receipts and the original shared tuple. Its §3.2 Lambda
clause retains body, consumer and captured roots. These are local emission
obligations over decorated inputs; they provide no original unannotated
formal-profile introduction rule. C-realization §3.5 assumes the exhaustive
conformance certificate and local interpretations. Inverting that conditional
theorem imports those assumptions; it cannot prove the missing raw-source
formal rule.

Inferred-call-view §2 requires the declarations/definitions/uses/component to
form one shared contract and preserves its slot inventory. Section 5 expressly
requires future judgments constructing that inventory. A shared root determines
identity, not which original introductions belong to it.

No annotation gives full protection and no annotation grant **at applicable
positions**. The protection policy quantifies over an applicability domain;
it does not classify that domain. Ordinary-value refinement keeps the same
inferred root and actual provider role/entry. No supplied rule says that this
refinement eliminates a formal introduction or enumerates its origins.

The known `Intro-Call-0` gives an original positive witness at
`p0=(beta,call.effect)` with `ElimOrigin(c,u_f,d_f,R_f,p0,p_out(c))`.
An arbitrary original witness from `Pi_f` has not thereby been shown to
originate at that Call. Replacing `Pi_f` by the generator's `{p0}` would remove
the very original premise under investigation.

## 5. Exact missing rule and stop condition

The next needed object is an independently grounded original judgment of
this interface shape:

```text
resolved original formal declaration/definition component C,d_f;
original scope sigma, shared root R_f, no source annotation;
independently specified component declaration/use premises at the same xi
    -> Pi_f and its original first-introduction/contribution certificates
```

This is an obligation interface, not an adopted rule. Its actual clauses must
say whether the implicit formal binder only groups component-origin witnesses
or can introduce its own original contribution, and supply the premises for
each alternative. They must state what counts as an original local formal
origin versus a retained independently inherited packet. A complete list of
original clauses and a well-founded finite derivation convention are needed
to invert every formal-introduction derivation.

An assumption that the list is exhausted by grouping would be the exact
additional premise needed for `N-formal`; it is not established by the existing
source relation. A refutation instead needs an original rule deriving a
formal-origin witness outside that grouping. No such rule was found in the
bounded inputs. Providing an extra latent path or a well-typed decoration
does not supply that source derivation.

The assigned stop condition is reached. No larger transport probe, execution
of a checker whose rules supply this premise, or Oracle experiment would
prove the unsupplied original formal rule. The next action is to have the
primary obtain or propose the exact local original formal-introduction
clauses with source justification, then return their frozen table for finite
inversion. A clause selecting a new meaning requires the primary's authority
process before it becomes a source-rule premise.

## 6. Independence, coverage, checks and resources

No Oracle semantics, execution or candidate-generator rule defines the
original relation. There is no independent executable oracle here. Shared
assumptions are the approved source meaning and the decorated relation/typed
transport hypotheses named above. The result is logical dependency analysis,
not differential consistency or source-semantics validation.

Coverage is the one approved finite component and the specified sections of
the ten dependencies below. No source-certified minimized counterexample,
random seed/range, enumeration, mutation campaign, test or build was produced.
General recursion, multiple formal uses, annotations/import formal rules,
Call-result completeness, raw-source transport completeness, contribution
semantics, full-view seed refinement, admission, principality and production
conformance remain unverified. Inherited provider/result packets are not
discarded or relabeled.

Failure conditions: a separately specified original formal rule absent from
this bounded input invalidates the missing-rule characterization; a rule that
does not preserve origin tags invalidates the ancestry argument; infinite
derivations need a separate termination argument. Dependency changes require
rechecking this note against the changed rule. These are proof boundaries,
not compiler failure predictions.

Commands used: read-only `git rev-parse HEAD` / `git status --short`; targeted
`rg`, `cat`, `sed` and `git show bb4595508:<path>`; Python SHA-256 and byte
equality against pinned blobs; leased-path link/whitespace and dependency
rechecks. No Git mutation occurred. At most four short read-only shell
processes ran concurrently; no heavy process, build, probe or search job ran.
CPU, RAM and total wall time were not instrumented; no numeric per-job budget
was supplied beyond the read-only/no-build/no-execution assignment.

All ten dependencies matched the baseline bytes at the initial hash check:

| Dependency | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/progress/2026-10-06-formal-profile-formation-rule-attempt.md` | `8b8b1d49e587835d65c4c6a13a0fc476b07bc58282ac5c58e782b4e5fd5b6a4b` |
| `notes/progress/2026-10-06-source-generation-pa-review.md` | `9f51c91fbaa9976022fed10d4b3fd9ab7eb1ae2027192bb9d5823f5a2d0fef2a` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-i-formal-inversion-attempt.md`.
- Baseline: `bb45955082ad885ea63687908b8cf852912c99ed`.
- Changed dependency hashes: none observed; direct hashes recorded above.
- Claim/review status: unreviewed bounded inversion obstruction; conditional transport ancestry; `I-formal` and `N-formal` remain open; no independent review claimed.
- Checks already run: pinned dependency bytes/hashes, targeted original-source reads, leased-note relative-link existence and whitespace check, final dependency recheck; no tests/builds/Oracle/probes.
- Proposed checkpoint message: `research: record original formal-profile inversion cut`.
- Shared-record deltas left for primary/curator: link the bounded formal-binder cut if useful; keep `N-formal` and the source-introduction table open; do not promote complete P, source adequacy, principality or production authority. No shared file was edited.
