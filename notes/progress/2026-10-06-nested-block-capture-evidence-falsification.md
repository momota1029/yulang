# Nested block capture: deferred activation and evidence obligations

Date: 2026-10-06
Status: Frozen, independently reviewed research-only conditional derivation and shortcut audit
Independent review: compiler_referee found no BLOCKING, major, or minor findings; activation transport and all-view adequacy remain open.
Baseline: `81ceae2804d66142245384db298b8dfb3d0813a8`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file only
Method: static derivation of a minimal activation prefix; premise inversion
Implementation authority: none

## Objective, result class and dependencies

Test whether the approved exact candidate
`my apply f = { my step x = f x; step }` supplies all-view typed-call and
evidence transport merely by retaining lexical `f`. Its selected sequential
binding, final function result and capture are fixed throughout this audit.

The new result is a **conditional activation-prefix lemma**: constructing and
returning `step` invokes neither `step` nor captured `f`. A receiver for the
later invocation of `f` therefore cannot be an invocation receiver preserved
from that construction prefix. This does not deny a static registered view
or a boundary at the earlier activation of `apply`.

The remaining shortcut exclusions are **bounded premise characterization**.
They are not counterexamples to Yulang semantics, production acceptance,
principality, or a complete source-registration rule. No language decision
is proposed. The existing source-registration and Hinst falsification notes
already exclude independent port witnesses and reconstruction from identity
or shape; those attacks are not rerun here.

Exact governing sources:

| Source and section | Status and use |
| --- | --- |
| Nested-block addendum §§1–4; integrated nested q1/a1 answer and receipt | Authoritative only for the exact source candidate and intended core correspondence; detailed typed-call/capture transport remains a premise. |
| Inferred Function call views §§1.1–2,5; integrated call-view q1/a2 answer and receipt | Authoritative direction: source formation, preserved static position/scope, distinct dynamic activation and joint `nu,K,D`; detailed producers remain open. |
| Callback-context delivery §§1–4 | Authoritative: B, actual callable role/entry preservation and static slot versus dynamic receiver distinction. Known instantiated `F_cb` is supplied. |
| Typed computation core §§2–3,6,9 | Draft reviewed conditional construction: supplied typed source paths, profiles and joint constraints; inert lambda/result; complete invocation activation/receipt/entry. No raw-source implementation authority. |
| Source-generated callback structural theorems §§2.1–2.6,3–4 | Reviewed conditional Theorem C over decorated immutable source graphs; closure roots persist, future admission uses original typed ports/current contexts, expired initial slots are not revived. |
| Source-indexed callback realization §§2–4 | Reviewed limited reference interpretation, with independently supplied local/provider/view evidence; separate production conformance. |
| Certified callback/constrained-use §§2.1–2.2,4,5.2 | Reviewed conditional certificates and exact all-view extension condition; complete tuples and latent dependencies must be preserved. |
| Pinned `tasks/current.md`, nested source gate and Hinst prerequisite | Navigation and gate status only. The live task file changed concurrently; its live changes were not used as new authority. |

Original rules were read in full. The two approval receipts and approved
answers were read; all their bytes match the pinned baseline. The archived
call-view a1 is not authority. No pending question bundle was consumed.

## Minimal conditional witness: the first later activation

Use the addendum's intended derivation, with the parameter interfaces made
explicit as `P_f=Value(F)` and `P_x=Value(A)` under typed-core §6:

```text
L = lambda(f,
      bind(step,
        result(lambda(x, call(result(name f), result(name x)))),
        result(name step)))
```

Hypotheses for the following reduction:

1. An independently typed context supplies an inert callable value `v` for
   `f`, a compatible decorated view and all complete-call premises. Its
   computation is `result(v)`; no argument effect, adapter or handler is
   needed for this witness.
2. A later independently typed provider supplies `result(a)` to returned
   `step`. The captured `f` call is admitted under its original typed route
   and the current decorated context, using one retained joint assignment.
3. The Draft core §§2–3,6,9 is used as conditional machinery, including its
   inert descriptor construction and actual invocation equations. This is
   not a claim that production HIR constructs these nodes.

Start an invocation of `L` on `result(v)`. Its actual receiver/receipt and
Value entry force that whole carrier and bind `f := v`. In its body, the
first child of `bind` is `result(lambda(...))`. Core §3 creates an inert
closure `s` whose environment retains that binder/root for `f`. It runs no
`X[body]` of `s`. The Return bind equation installs `step := s`; the suffix
`result(name step)` returns `s` without invocation. The enclosing invocation
then returns.

Let `N_step` and `N_f` count executions of the invocation constructors for
these particular source occurrences, excluding any invocations performed
inside an independently supplied provider. At this prefix endpoint:

```text
captured root(s,f) = original outer f root
N_step = 0
N_f = 0
```

For the supplied later call of `s`, complete invocation establishes the
current `step` receiver and receipt, forces `result(a)`, and binds `x := a`.
Only now does the body reach `call(result(name f),result(name x))`.
Lookup retrieves captured `v`; the complete call then establishes the
receiver/receipt for this invocation of `v`, rather than recovering such an
invocation from lambda creation. Immediately after reaching that inner call:

```text
captured root(s,f) = original outer f root
N_step = 1
N_f = 1
```

The proof is constructor inversion: the construction prefix contains only
lambda descriptor creation, result, lookup and bind. Its sole `call` node
is beneath the unexecuted local lambda body. The first later invocation
opens precisely that body. This proves the counts for the chosen pure
provider prefix; it asserts no behavior of `v` after its entry.

This witness needs one closure return and one later call. No second call,
request, response, resumption, recursion, annotation or effect family is
needed to expose the missing invocation receiver. Removing the later call
leaves only inert capture; moving the inner call into construction violates
the selected final-expression/capture meaning. No new surface candidate is
introduced: the providers are conditional proof inputs.

## Mutations and exact failure boundaries

| Candidate inference/mutation | Discriminating result |
| --- | --- |
| Lambda capture establishes the dynamic receiver for invoking `f` | The zero-invocation prefix above defeats this claim under the conditional core. Callback-context §3 separately says dynamic boundaries arise at activation. Static source registration during elaboration is permitted and is a different claim. |
| The later `f` receiver is the earlier `apply` receiver because both refer to captured `f` | Core §§3,9 distinguishes the activation of `apply`, activation of `step` and invocation of `v`. A receipt/profile at `apply` does not prove the receiver for the later `v` call. The exact source-to-boundary incidence rule remains missing; no storage layout is selected. |
| Capture keeps an expired earlier activation eligible at the later call | Theorem C §3 Future call/force and reference realization §3.2 already forbid revival of an expired initial slot/activation. Their application is conditional on the supplied decorated kernel and current-context certificate. Captured roots survive; preservation does not prove continued receiver activity. This is not a new authoritative general closure-lifetime rule. |
| Capturing the same value proves the full registered static view and its original profile | Addendum §3 and call-view §2 explicitly exclude construction of paths/receipt/authority from shape or comparison. Captured lexical identity discharges lookup/capture identity only. The source formation and original-profile incidence derivations must still be supplied; no conflicting same-original-profile model is asserted. |
| Preserve the printed Function ports at return, then reconstruct `nu,K,D` at the later call | Already excluded by call-view §2 and certified transformation §2.2: the retained relation must carry or recover the whole original scoped tuple, including latent/provider/admission dependencies. This note reuses that exclusion, without reproducing the prior independent-witness or hiding countermodels. |

Thus the constructive worker may establish root preservation through this
exact `bind`/return seam. It must not use root preservation to discharge
registration, activation incidence, current eligibility or complete evidence
transport. Correctly transporting an existing view/profile is compatible with
fresh dynamic activation; equality of all runtime receiver identities is not
the transport theorem being requested.

## Why the all-view implication still needs a premise

For a completed presentation `P` and an independently supplied public view
`V`, certified constrained-use §5.2 requires, in its original scoped sense:

```text
for every public assignment v:
  C_V(v) implies exists z.
    K_P^fresh(v,z) and Direct(R_P^fresh(v,z),R_V(v)).
```

The activation-prefix lemma supplies no `Direct` success and no extension
for all such `v` or `V`. Even a fully decorated witness for the single later
call above is insufficient to conclude this quantified entailment. Nor does
Theorem C apply merely from matching Function ports: it additionally requires
the specified linked source generator, local relations, independent admission
and complete whole-witness lift. The returned value may be handled by that
theorem when those hypotheses are supplied; the approved nested candidate
does not generate them by itself.

The precise remaining premise is a comparison-independent source certificate
linking the resolved captured occurrence and its retained original typed
view/profile to the actual later invocation/receipt at the current context,
preserving every jointly scoped source/latent/admission dependency. Separate
all-view endpoint adequacy/direct-query completeness is still required.
Neither a new supplied-transition model nor larger invocation counts would
test the missing source producer. This lane stops at that seam.

## Independence, checks, coverage and resources

No executable oracle or semantic checker was used. The activation-prefix
derivation consumes the reviewed Draft core's transition equations and
independently approved exact source meaning. It proves a consequence of
those premises, not their raw-source legitimacy. The mutation exclusions
consume the authoritative requirements and conditional theorem hypotheses;
there is no independent validation of this produced note or coauthored output.

Coverage is one supplied pure closure-return/first-call prefix and the five
named shortcuts. Mutations were reasoned about, not executed. Seeds, numeric
ranges and exhaustive/random search are inapplicable. No builds, tests,
probes, Cargo, formatter, Git mutation, child agents or shared-file writes.
Resource maxima: four concurrent lightweight read commands in one batch;
zero heavyweight processes. CPU, peak memory and total wall time were not
measured; no numerical budget was assigned. Output is exactly the leased note.

Commands used: bounded `rg`/`sed`/`cat` source reads, read-only `git rev-parse`,
`git status` for the leased path, pinned `git show` task excerpt and sequential
Python SHA-256/pinned-byte comparisons, then leased `apply_patch`. Some combined
reads were output-truncated; decisive core §§6,9, future-use admission and
certificate clauses were reread in bounded captures. No exhaustive repository
absence result is claimed. Dependency and lease checks precede final freeze.

Unverified: actual source acceptance/lowering; formation sufficiency and
provisional Handler discharge; annotation/profile construction; arbitrary
recursive/polymorphic/mutable/opaque/adapter/handler-image cases; later-effect
execution/routing; production Option 2 admission extras; complete membership,
containment, principality, all-view adequacy and solver implementation.

Recommended next action: derive the Q-independent source certificate for the
captured `f` occurrence at its first later invocation, with original static
profile transport and current receiver activation as separate premises.

## Dependency snapshot

SHA-256 of whole pinned files; all semantic inputs matched live bytes before
writing. `tasks/current.md` was navigation only and read again from the pinned
revision after detecting concurrent movement. Integration must revalidate.

| Path | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `questions/2026-10-05-nested-block-function-source-realization/approved-answer.md` | `04ee0dc089dc6ad19a184d31775a146c08b07f2f287099d2e5b54d7d1d5a643e` |
| `questions/2026-10-05-nested-block-function-source-realization/receipt.md` | `e5e59e176eb865a588b2843b18137571fe9c5b6f43bf1ca349bc60c9ad90f0ec` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-03-callback-context-delivery.md` | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` | `568bb4649ba278519f3ad01af2091dd1baaca42850cd19e3b5734b3c47c2eefe` |
| `notes/design/2026-10-04-source-indexed-callback-realization.md` | `76874a219ac86068027b1f08a5bc27a12d93a0169a52cebd896a6ff6f2c6b671` |
| `notes/design/2026-10-04-certified-callback-and-constrained-use.md` | `887bc7c0743d2f34608b46ccb8e5ee9b58ea4a39995b93a5aaced764295bae80` |
| `notes/progress/2026-10-06-source-registration-falsification.md` | `1efe0a779c5708a7eedf047c03cdc2764c07d75328bc055cc362d6cc8f58e292` |
| `notes/progress/2026-10-06-erow-hinst-falsification.md` | `5efc076b6c4ec404dd3253eafdb77ed4d86e263beb1487f3173dcfb5047f7317` |
| `tasks/current.md` (pinned navigation) | `b436bf28075f4089d02353115af11900dd66ec09328ccd9cd3c1961d86d89bfc` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-nested-block-capture-evidence-falsification.md`.
- Baseline SHA: `81ceae2804d66142245384db298b8dfb3d0813a8`.
- Changed semantic dependency hashes: none consumed; pinned snapshot above.
  Concurrent task-status movement is navigation-only and intentionally excluded.
- Review status: frozen unreviewed research-only conditional derivation and
  bounded shortcut audit; no independent review, full theorem closure,
  production conformance or implementation authority. Writing stops before
  submission for frozen review.
- Checks already run: governing/prior-result section reads, leased-path
  absence check, branch/HEAD reads, pinned/live semantic-input byte and SHA-256
  comparisons. No executable semantic checks, tests or builds.
- Proposed one-line commit message: `research: separate nested capture from later receiver activation`.
- Shared-record deltas left for primary/curator: record the zero-invocation
  capture prefix as conditional evidence and retain independent registration,
  later receiver/profile incidence, joint transport and all-view adequacy as
  open. No task/index/theory/authority/question file was modified.
