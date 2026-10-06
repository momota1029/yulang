# Exact captured-step source: search for an independently licensed extra origin

Date: 2026-10-06
Baseline: `167a5c2791abd8a5458554cf1ddbbb33f7f40b48`
Status: frozen research-only bounded characterization; independent review pending
Method: manual source-origin candidate elimination, exact tree only
Claim: no licensed counterexample found in the classified mechanisms; no singleton theorem
Semantic and implementation authority: none
Lease: this file only

## 1. Objective and result

Search for an independently introduced original applicable position
`p != p0` at the captured outer formal's `beta=(d_f,R_f)` in exactly
`my apply f = { my step x = f x; step }`. The requested witness needs a
source introduction derivation at this component, not merely a supplied
decorated profile, a transported view address, or a latent descriptor path.

No such witness was found among the twelve candidate mechanisms in §3.
Several mechanisms are licensed as execution, transport or inherited
evidence, but none supplies the requested new original introduction.
Two potential producers remain unproved: the implicit formal contract at
`d_f` (`I-formal`) and an additional source-owned result contract at the
existing Call `c` (`I-call-rest`). The present sources neither construct
their extra outputs nor prove their absence. Local source-introduction
inversion/exhaustiveness remains necessary as well.

This is a bounded classification, not a counterexample or a proof that
`Slots_original(beta)={p0}`. It does not establish incompatible complete
language meanings or a need for a new user decision. The naturality note's
optional extra clause is retained as an unlicensed hypothesis, not promoted
to a source-valid witness.

## 2. Authority, baseline and hypotheses

Authority is [inferred call views](../design/2026-10-05-inferred-function-call-views.md)
§§1–5 and the [exact nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–4. The accepted meaning fixes sequential local binding, final return of
the function value, lexical resolution to the same outer `f`, and later
capture of that `f`. The approved unannotated-formal direction fixes full
protection at applicable positions, no annotation removal permission, and
ordinary-value refinement on one inferred root while preserving actual
callable roles. Source annotations, public types and internal views remain
distinct. Type shape and pending `Q` create no source identity or authority.

Conditional mathematical inputs are [source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
§§2–3/10, [typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
§6, and [typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md)
§6. The [Call construction](2026-10-06-source-call-generation-construction.md)
§§3–7 supplies the positive `Gen-Call-0` slice. The
[normal form](2026-10-06-profile-source-normal-form-construction.md) §§3–6,
[adjacent-use falsification](2026-10-06-profile-adjacent-use-source-falsification.md),
and [substitution analysis](2026-10-06-profile-substitution-naturality-closure.md)
are prior research inputs. The [formation interface](2026-10-06-formal-profile-formation-rule-attempt.md)
§§3–5 names `I-formal/I-call-rest`; the [earlier failed induction](2026-10-06-profile-original-applicability-converse-construction.md)
is read to avoid repeating its singleton proof attempt. Their claim/review
statuses do not confer source authority or constitute review of this note.

The exact tree is:

```text
lambda(f,
  bind(step,
    result(lambda(x,
      c = call(result(name f), result(name x)))),
    result(name step)))
```

Retain these explicit hypotheses:

- **Hsource:** this selected tree and resolution, with no added annotation,
  call of `f`'s result, callback-position literal context or extra binding.
- **Hseed:** the accepted research constructor supplies the same
  `R_f,F_c,beta,p0=(beta,call.effect),ElimOrigin(c,...)`; its singleton output
  is the initial contribution only.
- **Htransport:** when a packet or execution is discussed, it has the
  independently typed correspondence/receipt required by typed-boundary
  §6. All `chi,K,D,L`, indexed sources and origins remain attached under
  one joint `xi=(nu,K,D)`. This audit constructs no runtime receipt.
- **Horigin:** “independently introduced here” requires its own original
  source-introduction witness. An inherited witness can carry the same
  static `beta` label from another use/activation; label inequality is not
  used to distinguish inherited evidence from a fresh introduction.

`Hsource` is selected meaning; `Hseed` is an established bounded research
dependency; `Htransport` is a conditional realization premise; `Horigin`
states the search criterion. No completeness premise is assumed.

## 3. Candidate forms in the fixed tree

These are candidate explanations of an extra position without changing the
source. They are not twelve different source programs. “Unproved producer”
means that neither its presence nor absence has been established.

| Candidate mechanism | Licensed fact and origin classification | Result for a new original `beta,p != p0` |
| --- | --- | --- |
| 1. Outer `f` formal's implicit contract, before its use | Typed core generates `Value(A_f)` and an entry/receipt skeleton. Inferred-call-view §2 requires the shared inferred contract. | **Unproved producer: I-formal.** Neither clause derives a complete original profile from the unannotated declaration. Ordinary Value entry does not exhaust nested signature contracts. |
| 2. Force of the external argument of `apply` at Value entry | This execution obtains the function datum bound to `f`; the incoming carrier and its packet remain actual inputs. | Entry observation belongs to that actual invocation. It is not a source call/force of `f`'s own latent result. No new original `beta` position follows. |
| 3. Force of the external argument of `step` at Value entry | The forced carrier yields `x` before its body. The inner argument of `c` is the already rebound Name-return computation `J_x`. | The external `step` carrier is not `J_x`. Counting its effects as a second `f` signature position merges different execution ports without a source-origin rule. |
| 4. Splitting `c` into callee entry, body and designated consumer positions | The Call constructor maps complete invocation to `p0`; these are constituent phases of that observation, with independently supplied actual provider rules. | More constituent events/phases do not produce another original source position. A rule introducing separate original phases would need source justification beyond the initial constructor. |
| 5. Actual `f` provider has a nested annotated/latent result profile | Decorated provider/result inputs can have arbitrary matching profiles. The returned view retains the actual result packet. | Licensed **inherited input**; no introduction by this component. A complete packet can have more entries than this component's generated footprint. |
| 6. Callee-signature result projection contributes another packet source | Typed-boundary §6 preserves this source separately from actual returned evidence, if matching result-profile information was independently supplied. | Projection preserves its input origin. If claimed to originate at this component's `beta`, the missing producer is **I-call-rest or I-formal**; projection does not supply it. |
| 7. Preattached dormant `result-root A_c` clause becomes nonempty when `A_c` is latent | The naturality countermodel shows how a supplied dependent clause preserves identity under grafting. | **Unproved producer.** A tag mentioning `c,d_f` is not a source-introduction derivation. Neither source validity nor impossibility follows from naturality. |
| 8. `A_c` is solved as Function/Thunk/recursive value with a latent effect path | Such a dependent descriptor can expose typed paths; Result/Normalize preserves the Value/Computation source tags. | A descriptor path is not an original introduction. Creating the origin because the head was solved violates inferred-call-view §2. A prior independently licensed schema returns to row 7. |
| 9. Capture of `f` into `step` introduces another boundary/profile | Selected capture preserves the same formal; typed capture moves its packet by the matching correspondence and can have a receiving-use receipt. | **Transport/ownership.** Receipt creates no boundary or profile; capture cannot allocate a second original source position by copying the view. |
| 10. Public result of `apply` exposes captured `f` as a field of returned `step` | The final Name returns the local closure. Private captured bindings remain available to its body. | Typed-boundary §6 does not expose private fields through public view transport. Equal public endpoint shape cannot turn private `f` into a new public original result position. |
| 11. The public call-effect position of local `step` is another position of `beta_f` | A future caller may impose/use `step`'s public callable interface; its body can execute `c`. | Public interface coordinates and `beta_f` are not identified by equality of effect endpoints. Later execution reuses `c`; supplying a new client profile is external evidence, not another origin in this exact tree. |
| 12. Alias/reference/generalization/re-entry yields a fresh original position | Name/Bind preserve provider roots; legal scheme actions preserve original source labels; repeated execution can allocate dynamic activations/events. | **Transport or dynamic identity.** Fresh view/activation/event identity is not a fresh original profile position. Full scheme/re-entry adequacy remains conditional, not proved here. |

The initial `p0` is licensed by Hseed but is not a successful extra candidate.
Annotation-owned extra positions and an explicit Call of `f`'s result are
outside Hsource; the adjacent-use note already studies those source changes.
They were not rerun or imported as counterexamples to this exact tree.

## 4. Derivation for the result-source discriminator

The most informative attempt is rows 5–8. It keeps the source fixed and
tests whether a nonempty returned profile proves an extra original origin.
Write the result packet equation with its two actual indexed sources:

```text
chi_result = M_actual*chi_actual_result
             union M_signature*chi_callee_result
```

If `chi_result(t,b)` holds, the indexed image supplies an input fact and a
matching path in one of these sources. The actual-result arm retains its
supplied original witness; it does not introduce one here. The signature arm
requires a prior fact at the matching result position. The mandatory seed
at `call.effect` is not mapped to `result.latent.effect` by result projection.
Thus a result-profile output is insufficient to distinguish an independently
introduced source contract from inherited evidence.

To make the signature arm a counterexample at this component, one needs:

```text
Resolved exact C,d_f,c; NoAnnotation(d_f); shared R_f,F_c,beta,xi
---------------------------------------------------------------- actual source introduction, not supplied
Intro_original(C,n,d_f,R_f,p,kappa;xi), p != p0
```

Here `n` must be a legitimate original declaration/use/Call contract origin,
and `kappa` must identify the independent constructor and governed
contribution. A result-dependent predicate can meet preservation laws once
supplied. Its lawful first generation is precisely what this display lacks.
The naturality model's one optional node therefore cannot fill the display.

This derivation is a conditional provenance classification under Htransport,
not a proof of the displayed source rule or its negation. It also does not
delete either result packet source to manufacture singleton output.

## 5. Exact blocker, failure conditions and stopping point

`I-formal` must classify what this unannotated formal contributes independently
of its resolved direct use. `I-call-rest` must classify whether this exact
Call produces any original result contract beyond its immediate complete
invocation position. Each requires an independently interpreted original
source rule; typed-boundary introduction currently receives `Gamma` as input.
Local inversion `I-exhaust` must then account for every original introduction,
including any constructor case not supplied by the present candidate table.
The table is not adopted as an exhaustive language introduction grammar.

The audited evidence fixes policy at applicable positions and establishes the
positive immediate seed. It does not establish the negative conclusions
`I-formal adds none` or `I-call-rest adds none`. Those conclusions remain
candidate assumptions. Counting the exact tree's eliminations would assume
the same missing locality premise already exposed by the earlier induction.

A discriminating next artifact would supply a source rule that independently
licenses `p != p0` at `d_f` or `c`, with its original path/contribution and one
joint assignment, or proves its absence by source-rule inversion. This
classification fails as a no-counterexample report if such a licensed
constructor already exists in an omitted governing section. Transport rows
fail if a proposed edge is actually a justified first introduction, rather
than the stipulated packet image. None of those possibilities was settled
by broad source or production searches here.

No new equivalent toy probe is proposed. A checker containing only the
positive seed and transport rules would make the same source-introduction
premise an input and leave this blocker untouched. Both previous footprint
and preservation routes are preserved with their existing limitations.

## 6. Checks, independence, limits and resources

Commands used: read-only `git rev-parse HEAD`, `git status --short`, bounded
`rg --files`/`rg -n`/`cat`/`sed`/`wc` reads, and a single small Python process
comparing direct dependency bytes/SHA-256 with `git show <baseline>:<path>`.
Initial batched output was truncated; all governing sections and substantive
assigned research text were subsequently read in bounded captures. The
shared task/index reads served only as locators and were not treated as
semantic authority or exhaustive repository coverage.

Final metadata check passed: final newline, no trailing whitespace, all
eleven relative links exist, and all fourteen recorded pinned digests match
their baseline blobs. Concurrent primary integration advanced HEAD to
`76fffec0edaacf56a9328ac50df2892fdbb4c24d`. Thirteen dependency working files
still matched the baseline; the substitution note changed as recorded below.
A narrow `git diff <baseline> -- <dependency>` inspection found review-status
updates and a precision repair: excluding its particular `s1` does not exclude
all other possible result-root schemas. That repair agrees with this note's
classification and leaves its source-origin premise unchanged. No unrelated
shared-record diff was consumed as semantic evidence.

The twelve-row coverage is manual and finite, on one selected source tree.
There is no executable semantic oracle, randomized seed/range, executed
mutation, source-acceptance experiment, compiler build or test. The conceptual
mutations are adding a dependent result schema, converting view/activation
identity into original identity, copying `p0` to latent result positions,
equating public `step` and private `f` by endpoint shape, and merging external
`step` entry with the inner Name-return argument. Their rejected/unproved
premises are classified in §3. No mutated language rule was adopted.

Oracle independence: no Oracle source, semantics, trace or result was used.
No pending question-board bundle was consumed. The seed/address convention
and transport equations are shared assumptions with prior research; this
audit provides no independent oracle for their source validity. A future
checker adopting those same equations would certify their algebra, not
the original-source converse.

Resource use: short read commands and small metadata processes; zero heavy
processes, zero builds/tests, zero child agents. No numeric CPU/RAM/wall-time
allowance was supplied in this packet; CPU, peak RAM and authoring wall time
were not instrumented. Only the exact leased note was written. No Git
mutation, production/test edit, or shared coordination/authority edit occurred.

Unverified: complete source typing/satisfiability, current production
acceptance, original profile completeness, contribution normalization,
runtime receipt/capture/re-entry/lifetime, independent initial admission A,
all-view principality, B-equivalence, and Option A/2 production conformance.

Recommended next action: ask the source-rule construction lane for one
independently grounded `I-formal/I-call-rest` introduction/inversion derivation
on this exact tree, using the result-source discriminator in §4; retain P open.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-profile-extra-origin-falsification.md`.
- Baseline SHA: `167a5c2791abd8a5458554cf1ddbbb33f7f40b48`.
- Dependency hashes changed: none before authoring. At final comparison,
  `notes/progress/2026-10-06-profile-substitution-naturality-closure.md` changed
  from `786d2e1cf070949556f557882fdbcc53eebc089cc537377877986bea722dc59a`
  to `3c8f99d0456fb2becb57a6429407eb2fc7410ac5e27aaaa5c94cf81843112087`.
  Its narrow delta was checked as described above; the other thirteen direct
  dependencies were unchanged. Original pinned source/authority/research
  SHA-256 snapshot:

```text
ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd  rules/research-lab.md
9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29  rules/design-authority.md
e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e  rules/git-concurrency.md
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1  notes/design/2026-10-05-inferred-function-call-views.md
750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0  notes/design/2026-10-06-nested-block-function-source-realization-addendum.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186  notes/design/2026-10-05-source-contracts-and-common-allowance.md
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e  notes/design/2026-10-02-typed-computation-core-elaboration.md
1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb  notes/design/2026-10-02-typed-boundary-realization-draft.md
6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073  notes/progress/2026-10-06-source-call-generation-construction.md
ea32179888d41ceaddda7ba5c3566e1e83bf489da3fba763a28fda37e8876fad  notes/progress/2026-10-06-profile-source-normal-form-construction.md
b6258f6a586bcbdf7d331c0bda41587ab2948e5b045a03a6f35285acdeb7c9bb  notes/progress/2026-10-06-profile-adjacent-use-source-falsification.md
786d2e1cf070949556f557882fdbcc53eebc089cc537377877986bea722dc59a  notes/progress/2026-10-06-profile-substitution-naturality-closure.md
8b8b1d49e587835d65c4c6a13a0fc476b07bc58282ac5c58e782b4e5fd5b6a4b  notes/progress/2026-10-06-formal-profile-formation-rule-attempt.md
3a7749b9e3678bc05f6f5754ad5304a707169d84162e95c741e650686736b203  notes/progress/2026-10-06-profile-original-applicability-converse-construction.md
```

- Review status: producer-authored bounded classification; independent review
  pending; no theorem/authority promotion and no independent self-review.
- Checks already run: pinned-byte/hash comparison and targeted source reads;
  final leased-note whitespace/link/dependency checks recorded at submission.
- Proposed one-line research checkpoint message:
  `research: classify extra profile origins in the exact captured-step source`.
- Shared-record deltas intentionally left for primary/curator: if accepted,
  record twelve mechanisms with no licensed extra origin found, retain
  `I-formal/I-call-rest/I-exhaust` and P open, and keep the dormant result schema
  unlicensed. No shared task/index/theory/authority/question file was edited.
- Writes stop before frozen submission; the primary owns review and Git
  integration. This checkpoint does not close source or production gates.
