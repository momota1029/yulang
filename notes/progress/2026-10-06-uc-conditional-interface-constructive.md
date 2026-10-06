# A conditional local interface for the unannotated formal use

Date: 2026-10-06
Baseline: `7b1665c125a1883d36c682ee5c76e3757cce3ebd`
Status: unreviewed research checkpoint; conditional derivation and rule-interface boundary
Method: constructive local rule inversion and whole-tuple erasure proof
Lease: this note only
Semantic / implementation authority: none

## 1. Objective, authority and result

For `my apply f x = f x`, determine what the selected sources actually
provide for the first active constraint `Delta_formal`, interpreted by `U_c`.
This attempt does not repeat the prior exact-candidate closure/Bind calculation,
an Oracle trace, or a falsifier. It isolates the relationship between a
source solution and its two internal inference presentations.

The authoritative decisions are inferred-call-views §§1.1–5 and integrated
`function-call-view-formation/q1`, approved answer `a2`, decisions 1–6.
They fix one shared inferred interface, a protected internal Handler seed,
ordinary-value refinement in this singleton pattern, preservation of actual
callable role/entry, and comparison-independent formation/admission. They
expressly leave exact generation rules open. Typed-core §§6,9 are reviewed
conditional Draft constructions. Source-contract §§2–3.5,10 are a reviewed
conditional package, requiring independently interpreted primitives and
decorated typing. Neither supplies the missing raw-source primitive.

**Result:** the sources constrain an admissible judgment signature and its
singleton postconditions; they do not entail a definition of `U_c`. Section 4
proves a precise conditional implication: an exact stage extension of an
independently defined original whole-tuple relation preserves every unchanged
downstream predicate, including a later query. The source relation, typed
coordinate interpretation, and exact stage extension are unsupplied premises.
This is not a derivation of `|-emit Delta_formal`.

## 2. Constructible local prefix

Fix the original component `C`, binder tree/scope `sigma`, formal identities
`d_f,d_x`, name occurrences `u_f,u_x`, and `c=Apply(u_f,u_x)`. The local
callee-use inventory is exactly `{c}`; both ordinary parameters are
unannotated. Assume the admitted ordinary parameter/name/application
constructors of typed-core §6. Their inversion yields

```text
resolve(u_f)=d_f                  Gamma(u_f)=Value(A_f)
resolve(u_x)=d_x                  Gamma(u_x)=Value(A_x)
Result(Gamma(u_x))=Comp(empty,A_x)
I(c)=Computation(E_c,A_c)
O_c=(d_f via u_f, Comp(empty,A_x) via u_x, E_c,A_c,c,sigma).
```

The same symbolic `A_f` is reused at the callee occurrence. The empty row
belongs to this ordinary name's result interface, including when `A_x` is
latent data. It supplies no empty-effect assertion about `f`'s result, no
generic incoming-carrier purity theorem, and no actual callable-role fact.
The application obligates a complete invocation, rather than identifying
`Comp(E_c,A_c)` with a closure's body result or summing outward support rows.
This prefix constructs references and obligations, not successful typing.

These are the same available local facts as minimal-clause §§3,5. Its §§6–7
separate original typed footprint and independent admission from this first
interpretation. The prior exact-candidate constructive attempt §§2–4 reaches
an independently interpreted primitive leaf. Its nested closure composition
does not provide an additional local seed/refinement rule.

## 3. The strongest admissible interface, with missing content visible

Write `Refs_c` for the fixed component, scope, resolved formal/use/call
identities, annotation absence, and obligation `O_c` from §2. Then the missing
emission rule has the interface

```text
Gamma_shape ; S ; C ; sigma ; Refs_c
  |-emit-at c Delta_formal(A_f,A_x,E_c,A_c; Refs_c)

[[Delta_formal]] = U_c(xi; H_seed,H_refined,J_arg,J_call; Refs_c,Actual)
xi=(nu,K,D), at the original scopes.
```

`H_seed,H_refined` are internal presentations of the *same* inferred formal
and its dependencies. `J_arg` is the whole carrier at this occurrence;
`J_call` is the complete invocation interface. `Actual` retains a supplied
callable's own role and entry, together with its original provider references;
it is not a new runtime carrier. This notation does not assert that these
typed view domains have already been generated. Their independent definition
is required before the predicate can be interpreted.

The authoritative singleton requires:

1. Annotation absence supplies the provisional Handler treatment with fully
   protected effects in `H_seed`, without asserting an empty row.
2. This occurrence's ordinary-value evidence determines `NonHandlerFormal`
   in `H_refined`, related to that seed on the shared `A_f` interface.
3. This determination changes no actual supplied callable role or entry.
   `NonHandlerFormal` is not silently replaced by an actual `Pure` tag.
4. Original endpoints, joint `nu,K,D`, dependencies and scopes are preserved.
   No independently chosen port witnesses may be combined.
5. `Q` supplies none of the predicate's source incidence, protection, typed
   paths, receipt/receiver facts, or authorities. Merely omitting `Q` from a
   printed signature is insufficient if a premise was itself obtained from Q.

These conditions do **not** define which complete correlated tuples satisfy
`U_c`, how the seed presents those tuples, or how refinement transforms that
presentation. They select no any/all/mixed aggregation for another component.
Even though those aggregations coincide on a singleton inventory, that fact
does not define its local predicate.

Keep the adjacent missing judgments separate:

| Judgment | Required independent content | What it cannot be replaced by |
| --- | --- | --- |
| `U_c` / `Delta_formal` | Active interpretation of the inferred formal's local use on a whole tuple | A role marker or a future-registration promise |
| `Foot_S(d_f,c,p;xi)` | Original source-to-typed effect-observation position/contribution map and receiving profile | Equal family names, all row support, all latent descendants, or the source label `c` |
| Initial/context admission | Independently typed punctured environment and whole-carrier histories, at original dependencies | Port compatibility, observed termination, or existence of an instance chosen to make Q succeed |

Once a footprint is supplied, annotation absence must protect its specified
contributions and supplies no concrete annotation grant. This obligation
does not generate the footprint's domain. The rule connecting protected seed
evidence to completed refined evidence remains part of the missing coupling;
this note selects no protection-discharge operator. There is no receipt or
active receiver merely because a static local constraint has been emitted.
At actual entry, the callable's own entry and admitted instance remain needed.
Known-context literal B remains unchanged.

## 4. A precise conditional preservation criterion

Here is a proof obligation on a proposed rule, rather than a definition by
the desired answer. Supply the following **candidate assumptions**:

* A typed coordinate schema `T_sigma` with independently interpreted view
  fields. A whole row `b` retains the original `xi`, scoped endpoint assignments,
  completed formal/use meaning, argument/invocation relation and actual
  provider role/entry. All semantic fields affecting later use remain in `b`.
* An independently defined relation `B_S subseteq T_sigma` of original local
  source solutions. Its interpretation must precede the candidate stage rule
  and Q. It is not defined as the candidate's output.
* A candidate staged relation `R_U` on `(b,H_seed,H_refined,w)` with an
  independently justified interpretation of `U_c`, matching the singleton
  conditions of §3 and local typing. `w` denotes metatheoretic derivation
  witnesses at their original scopes, not existential source types.

Define `erase(b,H_seed,H_refined,w)=b`. Only staging/derivation witnesses are
forgotten: the final inferred meaning, profiles, dependencies, actual provider
facts and original assignment are not independently projected or hidden.
In particular, a staged witness's views must refer to that row's `A_f,xi`;
there is no separate `xi_seed` or `xi_refined`.

**Conditional theorem (exact extension and downstream preservation).**
The equality `erase(R_U)=B_S` holds exactly when both clauses hold:

```text
coverage:  forall b in B_S. exists H_seed,H_refined,w.
             (b,H_seed,H_refined,w) in R_U

soundness: forall (b,H_seed,H_refined,w) in R_U. b in B_S.
```

When they hold, for every unchanged predicate `W` on retained whole rows,

```text
{b | exists H_seed,H_refined,w.
       R_U(b,H_seed,H_refined,w) and W(b)}
  = {b | B_S(b) and W(b)}.
```

**Proof.** For exact extension, soundness gives the left-to-right inclusion;
coverage gives the reverse inclusion, using one entire staged witness per
original whole row. Conversely, equality supplies those two inclusions and
therefore the two clauses. For downstream preservation, a staged row
satisfying `W(b)` erases to `b in B_S` by soundness, retaining the same `W`
witness. An original row satisfying `W(b)` has a staged extension by coverage,
and that extension retains every coordinate read by `W`. Both inclusions
follow. No port-by-port existential choices occur. QED.

Taking `W(b)=Q(b)` proves preservation of an unchanged later comparison
predicate **conditional on these premises**. Q need not be known when the
stage extension is formed. This yields no source rule from Q, and is not
normative B-equivalence for an optimization: B also requires principal
solutions, method/adapter choices and residual/evidence preservation.

The criterion is stricter than choosing any stage pair satisfying the selected
role/protection labels. Such a choice need not cover every original row or
exclude spurious correlated tuples. Conversely, deleting a provisional
presentation is not itself failure: it is permissible if another justified
stage presentation retains the original row. Thus preservation should be
tested on the original source relation, not on the number of provisional
candidate presentations. The result establishes no algorithm, principality,
uniqueness of stage presentations, or independent admission.

No source-rule proof has been hidden in the theorem. Its critical hypotheses
are precisely the independently defined `B_S` and the source-grounded stage
coupling in `R_U`. They cannot presently be instantiated from §2 alone.
Replacing `B_S` by `erase(R_U)` would make both obligations circular; defining
`R_U` by conjoining `B_S` only assumes its original source interpretation.

## 5. Limits, proof mutations and the precise blocker

This is one local constructive attempt, with no executable or finite-search
claim. It provides a conditional preservation obligation and an admissible
interface, rather than a new interpretation of `U_c`. The predecessor already
reached the same primitive boundary through closure composition; another toy
stage checker would leave that premise untouched. The precise blocker is the
independent whole-tuple meaning linking the protected internal seed and the
ordinary-value refinement to original local source solutions. A type tag,
role label, static identifier or operational `ExecuteCallable` expansion does
not supply that meaning.

Analytical mutations identify failure conditions; none was executed:

* Retain only one convenient original row: violates coverage when another
  source solution exists. The one-row successful case cannot prove coverage.
* Permit tuples meeting only the seed/refined labels: soundness is unproved
  for their complete endpoints/evidence, even when every label is permitted.
* Rechoose argument, call and profile witnesses separately: no staged witness
  over one `b` is supplied, so the reverse inclusion proof cannot proceed.
* Erase original `K,D`, final formal meaning or actual role/entry: `W` can
  inspect the removed field, invalidating the downstream proof's hypothesis.
* Define a missing typed path, footprint, admission or stage witness from Q:
  fails formation independence before the preservation theorem applies.
* Apply this occurrence's refinement to every Value-entry callable: exceeds
  the singleton inferred-formal scope and supplies no generic source theorem.

The proof and the previous composition share typed-core/source-contract
assumptions; they are not independent source-semantics evidence. No Oracle
executable, reference transition checker, production artifact or legacy trace
was used. A checker implementing the displayed coverage equations would test
its supplied relations only, not establish that `B_S` or `U_c` follows from
Yulang. Seeds/ranges: none. Coverage: the selected one-formal, one-call local
pattern only. Omitted: mixed/repeated uses, recursion, present annotations,
generalization/freshening, typed footprint construction, entry-history coverage,
capture transport, arbitrary adapters, full admission, Option A/Option 2
production extras, principal inference and implementation.

Recommended next action: have the primary obtain a source-grounded proposed
definition of the local stage-coupling predicate, with its original typed
coordinate domains, and review its coverage/soundness against an independently
specified original local relation. Supply footprint and admission separately;
do not request approval again for the already selected singleton outcome.

## 6. Dependencies, verification, resources and commit packet

All thirteen direct dependency files below matched their baseline blobs before
writing. The exact saved approved draft `a2` matched its embedded approved
content after trailing separator-newline normalization. The receipt identifies
integration commit `61a3651376166346a5baa03ec6679c310b0edbdb`. Routing reads of
`tasks/current.md` / design INDEX were locators, not new semantic premises.

| Path | SHA-256 |
| --- | --- |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `rules/question-board.md` | `8c617ceb978dfa26ce12f4f71ecc8ece22ffd8f1cf1982125b33142f645ae1c0` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/progress/2026-10-06-main-source-generation-minimal-clause.md` | `7b641ce7b54d1e8aa9a15ae233e7dcee0a7f2fdf51410158df69147dbc36bd38` |
| `notes/progress/2026-10-06-source-formal-relation-constructive-attempt.md` | `6b2f42ea99ffcb231e9fb73a048afba75dca050ad93706217806f904f1d93628` |
| `questions/2026-10-05-function-call-view-formation/question.md` | `f3915c64daeccf466115b74a895c2c937f2ec10c1872fc91ff220ed2b0cf7c5f` |
| `questions/2026-10-05-function-call-view-formation/answer-draft.md` | `585211d345ead07c8401576c84d216be858d3c7c81e8b412e8ba36a28460d35c` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |

Checks: read-only `git rev-parse HEAD`; required policy/source reads and scoped
`rg`/`sed`; Python SHA-256 and byte comparison with `git show BASE:path`;
saved-a2 comparison; direct proof of the two inclusions in §4. Combined reads
initially truncated output; decisive governing sections were reread narrowly.
No broad search completeness is claimed. Final dependency and leased-path
inspection is recorded in the producer's submission. No tests, builds, Oracle
execution, formatter, Git mutation or writes to shared records.

Process budget: lightweight source inspection and this one note only; zero
compiler/search processes. No CPU-intensive work or allocated seed shards.
Command captures were bounded, with no heavyweight concurrent process.
Exact agent wall time and peak RSS were not instrumented; no search timeout or
unfinished enumeration exists. The producer does not independently certify
this note. Writes stop before submission for frozen review.

Commit packet:

* Exact leased/changed path: `notes/progress/2026-10-06-uc-conditional-interface-constructive.md`.
* Baseline SHA: `7b1665c125a1883d36c682ee5c76e3757cce3ebd`.
* Dependency hash changes: none at preparation; recheck before integration.
* Claim / review status: unreviewed conditional research derivation and
  admissible interface; `U_c` generation and the main gate remain open.
* Checks already run: scoped source reads, baseline-byte/SHA-256 checks,
  a2-content equality, and mathematical inclusion derivation; final inspection
  in submission. No executable verification.
* Proposed commit message: `research: state conditional local formal-use extension criterion`.
* Shared-record deltas intentionally left for primary/curator: optionally link
  this criterion from `tasks/current.md`; retain the first open stage-coupling
  interpretation, separate typed footprint and independent admission, and
  the source/production boundary. No theory-status or authority promotion.
