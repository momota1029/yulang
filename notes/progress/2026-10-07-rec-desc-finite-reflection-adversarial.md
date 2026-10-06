# Adversarial obstruction to REC-DESC finite reflection

Date: 2026-10-07
Baseline: `1870b1330160e83b71756f60300900f3e2ff4545`
Status: frozen, unreviewed research checkpoint; no semantic or implementation authority
Method: logical obstruction and conditional compactness derivation, not constructor induction
Claim class: conditional theorem plus minimized logical falsifiers; no admitted Yulang counterexample
Exclusive lease: `notes/progress/2026-10-07-rec-desc-finite-reflection-adversarial.md`

## Result and exact scope

The minimum additional law for the **finitary-clause factorization below** is
finite refutability of its compatible witness fiber: if no complete compatible
extension satisfies the independent descriptor clauses, some finite family of
those clauses already has no compatible extension. Finite families must then
be representable by one independently admitted FH presentation. This identifies
a stronger obligation than finding a bad finite prefix at one chosen witness.
It neither defines `DescMem` by FH nor proves that the actual descriptor admits
this factorization.

A one-variable natural-number fiber demonstrates why finitary clauses alone
do not imply that law after existential hiding. Every finite conjunction is
satisfiable, but the whole family is not. This falsifies a weaker
`forall finite h. exists e. Check(h,e)` bridge. It **does not falsify pinned FH**:
its selected finite witness eventually cannot extend along an independently
admitted next transition, violating FH's pointwise preservation premise.
No source-admitted counterexample to FH or REC-DESC was constructed.

The actual remaining premise is precise: derive either this finite refutability
law for each relevant independently interpreted descriptor fiber, or a stronger
source-grounded construction of coherent witnesses that makes it unnecessary.
The source's finite positive reference grammar does not by itself establish
the law for independent ordinary `DescMem` or Option 2 production extras.

## Baseline, authority and dependencies

Governing sections were read at the pinned revision:

- [source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2.2, 3, 10: independent `DescMem`, joint original witnesses, four admission
  cases, conditional constructor typing, and Option 2's hard constraint guard.
- [source-indexed realization](../design/2026-10-04-source-indexed-callback-realization.md)
  §§2–4: original sharing/scopes, finite reference derivations, inert returned
  handles, current-state raw resumption, and comparison-independent admission.
- [typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §§4, 9 and [ordinary computation](../design/2026-10-02-ordinary-computation-semantics-package.md)
  §§2–5: complete invocation/suffix, current store, original request and owner
  evidence, ordinary fresh invocation versus resumed execution, and finite
  prefixes of divergence.
- DAG nodes `DESC_CLAUSES`, `ADMISSION_CLAUSES`, `SEM_JOINT`, `REC-DESC`, `FH`;
  [FH's actual statement](2026-10-07-successor-recursive-synthesis.md) §4;
  [finite-reflection localization](2026-10-07-rec-desc-finite-reflection-localization.md)
  and [observation bridge](2026-10-07-rec-desc-observation-finite-bridge.md).

The committed approved answers for typed-value observation, production Function
denotation, production bound membership and inlet context domain were read.
Preserved decisions: Option A's existing complete typed observations and
independent satisfaction/admission; Option 2's licensed non-source extras;
all independently compatible punctured contexts at the original `(nu,K,D)`;
one whole typed projection; no admission by Q success. These answers do not
select the candidate clauses below. No historical Oracle meaning is inferred.

The three required operating rules were read in full. Task/index records were
used as locators; source sections govern. Rules and all direct inputs matched
both pinned HEAD and working files when checked before writing.

## Conditional derivation: expose the witness fiber

Fix the same actual provider `v`, descriptor `R`, original scopes and old
assignment `(xi,w)`. No old coordinate can change. Work in classical logic.
The following are **candidate hypotheses to discharge from the actual
independent clause package**, not new source definitions.

**H1 — exhaustive finitary factorization at the original binder positions.**
After independent root/static obligations `S`, a descriptor failure supplies
an independently specified complete obligation instance `o` whose compatible
witness fiber is empty. Let `E_o` be the universe of total event-local
assignments extending the fixed old assignment, respecting original binding
order and dependencies, without requiring descriptor validity. Let `J_o` be
the finite presentations of this obligation. For each `p in J_o`, define

```text
A_p = { e in E_o | the full checks attached to p hold at e restricted to p }.

The independent complete clause at o holds iff intersection(p in J_o) A_p
is nonempty.
```

This equivalence must be proved from the original clauses. In particular,
there can be no omitted condition on an infinite completed observation that
is not represented among the checks. A shared existential over several
obligations must stay shared: include that entire joint obligation in `o`.
An existential below a rigid universal stays below it. This theorem supplies
no license to replace `exists e. forall o` with `forall o. exists e`.

**H2 — independent coverage.** Every needed finite presentation is in the
exact original admission domain. Coverage does not assume `DescMem(v)`,
`CompleteMem`, Q success, or source-constructor realization of an Option 2
extra. All original inlet/world premises and the actual provider identity,
typed ports, current resumed state, raw handle and pending suffix are retained.

**H3 — exact local judgment and raw assignment extension.** At a finite
presentation `p`, FH's *whole* judgment `L(p;xi,w)` is equivalent to
`A_p != empty`. If FH's local judgment has existential extensions, this
requires every passing partial extension to extend to some total assignment
in `E_o`, ignoring checks outside `p`. It assumes no global typing success.
Conversely restriction of a total assignment supplies the permitted local
witness. The equivalence retains all local conjuncts and witness scopes.
It cannot be obtained by showing only one checked extension fails.

**H4 — finite conjunction coverage.** For every finite list
`p1,...,pm in J_o`, there is one independently admitted finite presentation
`p*` with the original joint coordinates and

```text
A_p* subset intersection(i=1..m) A_pi.
```

This presentation may require a finite branching interaction derivation rather
than one linear trace. Mutually exclusive developments cannot be concatenated
as if they execute sequentially. If the admission/FH domain does not contain
the needed joint presentation, an inconsistent finite family is insufficient
to produce the required single failing FH judgment.

**H5 — finite refutability of this fiber.** For this actual family, at these
fixed interpretations and old coordinates,

```text
intersection(p in J_o) A_p = empty
  => exists finite p1,...,pm. intersection(i=1..m) A_pi = empty.
```

This is the extra compactness law. It is only about the displayed family;
compactness of every semantic world or the whole CompleteMem environment is
stronger and unnecessary. One sufficient mathematical realization is a compact
assignment space `E_o` with each `A_p` closed: the finite intersection property
gives H5. Finite discrete event-witness domains with closed finitary constraints
are a sufficient product-space instance under the usual classical product
compactness theorem. Infinite domains require their own
justification. Logical first-order compactness that changes a fixed primitive
domain or its interpretation does not supply H5 here.

**Derivation.** Assume `S` and `not DescMem(R,v;xi,w)`. H1 supplies an `o`
with empty fiber. H5 yields a finite family with empty intersection. H4 supplies
one admitted `p*`; its set `A_p*` is empty. H3 gives `not L(p*;xi,w)`.
H2 ensures this is a history covered by FH, at the original coordinates.
Thus FH contradicts the descriptor failure. Only `DescMem` follows; `M_E`,
CarrierMem, WorldMem and the simultaneous CompleteMem conjunction remain
separate. No validated recursive environment or Q success was assumed.

Within H1–H4, H5 is the precise global-to-finite emptiness law this proof needs;
full topological compactness is a sufficient route, not a selected language
requirement. When `o` already has one finite complete presentation carrying
every clause, no infinite compactness step is needed. Finiteness of source
code or a membership derivation does not establish that stronger condition
for every independently interpreted descriptor obligation.

## Minimized logical falsifier for hiding before reflection

Use one old assignment, one retained provider, one event-local variable
`N in Nat` introduced at the first authorized event, and an unbounded sequence
of repeated abstract observations `a`. All roots/static checks are true.
There is no provider substitution or state reset. This is a logical fiber
example, not a typed source/admission construction. At every finite depth
`n >= 1`, take

```text
A_n = { N in Nat | N >= n }.
L(a^n) iff exists N. N >= n.
```

Every finite conjunction has a witness `N=max(n1,...,nm)`. Nevertheless
`intersection(n>=1) A_n` is empty: for any fixed natural `N`, depth `N+1`
fails. Thus

```text
forall n. exists N. N >= n          is true;
exists N. forall n. N >= n          is false;
exists n. forall N. not(N >= n)     is false.
```

Each full fixed-witness failure has a finite cause; projecting away that
existential witness removes uniform finite refutation. Finitary checks on an
enriched observation therefore do not automatically remain finitely
refutable after existential projection. The two quantifier negations above
cannot be interchanged.

Minimality here is structural, not a repository-wide search result. A single
finite conjunction cannot violate H5; a finite witness domain with nested
nonempty sets cannot violate it either. This example uses one hidden variable,
one observation label and an infinite depth family, with no extra provider,
world, comparison or permission machinery.

**Exact exclusion by pinned FH.** Once `N` has been chosen, it is an existing
coordinate. At history depth `N`, an independently admitted next `a` requires
`N >= N+1` and cannot preserve the local check using a compatible extension.
FH §4 premise 2 fails. Reselecting a larger `N` per longer history is forbidden.
Putting `N` into the old `w` instead makes the finite failure visible directly
at that fixed `w`. Restricting admission to stop at `N` changes the independent
domain and cannot repair the bridge. This is not an admissible countermodel
to the pinned pointwise FH premises.

Hand mutations discriminate the assumption: bounding depths at `B` gives the
global witness `N=B`; adding a genuine allowed value `infinity` also gives a
global witness. Neither mutation is adopted. In particular, a nonstandard
infinite natural from a different primitive interpretation would change the
fixed domain rather than prove the needed original law.

## Other failure seams and exclusions

| Seam | Exact condition still needed | What this attack establishes |
| --- | --- | --- |
| Empty admission / no future event | Every active root condition is in independently proved `S` or an admitted zero-step full check | Event enumeration alone cannot discharge an unrepresented root clause; no empty-domain source example was proved |
| Inert Return and latent handle | Finite presentations retain the same actually returned provider and its original typed future-use port | Returning a handle supplies no call; future-use coverage in H2 must be independently supplied |
| Raw resumption | Same exposed request and original raw suffix, current resumed state, original scope/dependency and source-prescribed live-owner mapping | This note alters no invocation/resumption transition and repeats no repaired receipt confusion |
| Infinite complete observation | H1 must exclude an unrepresented infinite condition, and H5 must survive allowed existential hiding | The natural-number fiber falsifies finitary-to-projected-compactness without H5 |
| Sibling joint witnesses | H4 must expose the complete failed finite conjunction in an admitted presentation | A finite set of separate successful local checks is insufficient when they cannot be joined; no new Boolean toy probe was run |
| Option 2 extras | H1–H4 cover independently licensed extras as well as source-base observations | Source constructor derivations are neither universally required nor proof of extra coverage |

A separate minimal obstruction to H1 is a singleton infinite loop with every
finite local check true and a hypothetical extra condition requiring eventual
Return. The loop fails only that infinite condition. This is a logical
falsifier for *arbitrary* complete predicates, not a competing Yulang meaning:
source-indexed §3.2 explicitly asserts no termination or infinite-liveness
property of its finite reference denotation. No such extra ordinary descriptor
clause was found or adopted. The example identifies what a clause audit must
exclude, while the witness-fiber example attacks a distinct premise even when
all constraints themselves are finitary.

The admitted histories, actual descriptor clauses and their common SEM_JOINT
interpretation are still unsupplied. Accordingly neither example proves
authority-consistent semantic non-entailment, source rejection, impossibility,
nor a need for a new user decision. Current all-world admission prevents
silently narrowing contexts to remove a failure. The retained source-envelope
restrictions do not justify a new production rejection bound.

## Checks, resource budget and independence

No checker, compiler edit, test, build, Oracle execution or exhaustive search
was used. The method is algebraic: the natural-number statements cover all
`n,N in Nat` by the explicit witnesses `N=max(ni)` and `n=N+1`. Seeds and
enumeration ranges are inapplicable. Mutations above were derived on paper.
There was one method packet, not repeated enlarged toy experiments.

Commands already run: bounded `git show 1870b1330:<path>` reads; Python
section extraction for the governing headings; a SHA-256/byte-equality check
against pinned blobs, current HEAD and working inputs. A truncated broad capture
was replaced by complete narrow operative-section reads, including FH §4.
Initial path discovery used `rg`; semantic reads came from pinned blobs.
Only read-only Git operations occurred. No shared mutable build output or
temporary research artifact was created.

Resource cap: one lightweight top-level read/write process at a time, serial
metadata subprocesses, no compute campaign, no children and zero heavy builds.
Aggregate wall time, CPU consumption and peak RSS were not measured. The
individual read-tool calls completed within 0.2 seconds as reported by the
tool; this is not aggregate research timing. No timeout or killed search
occurred. Repository-wide absence of descriptor clauses was not searched.

The proof uses explicit independently required hypotheses rather than a
supplied transition checker. There is no oracle/reference implementation,
so no claim of oracle independence or source-semantics validation by execution.
Both falsifiers assume only their written logical domains; neither shares a
validated source admission derivation. Producer reasoning is unreviewed and
is not independent review.

Recommended next action: the primary should ask the descriptor-clause producer
to identify the actual binder order and complete witness fiber of one latent
Function clause, then test H1–H5 against that clause. Prefer proving coherent
extension from pinned FH when available; do not add a generic compactness axiom
or impose a finite observation limit.

## Frozen direct dependency SHA-256

All listed inputs matched the pinned commit and current working files before
the artifact was written; no changed dependency hash was observed.

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-04-source-indexed-callback-realization.md` | `76874a219ac86068027b1f08a5bc27a12d93a0169a52cebd896a6ff6f2c6b671` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-ordinary-computation-semantics-package.md` | `ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917` |
| `notes/progress/2026-10-07-rec-desc-finite-reflection-localization.md` | `1ba67b64fe17d9cac3d558e25d11007db5f73761d7b80fd15e35aeca90fd18bc` |
| `notes/progress/2026-10-07-rec-desc-observation-finite-bridge.md` | `c1a89ab082e1e4560ac493a79260487668fe43cdead50d610224e4ef772e0183` |
| `notes/progress/2026-10-07-successor-recursive-synthesis.md` | `e34a568946f5c1946c01828aae34e890747477ee8c272775408438acd95aa43f` |
| `notes/theory/successor-proof-obligations.md` | `81b0c3f61cfd3de255fdbd4b0ae005694aa7cd5cdeaf384352272d80359009d9` |
| `questions/2026-10-04-function-bound-value-observation/approved-answer.md` | `5a349fd0a87397372097701ca96b4dd45a0c37efb59a7e821eae53f3cddba22f` |
| `questions/2026-10-05-production-function-denotation/approved-answer.md` | `7e7f3c717b16a70fc754c930a1654666c8b61a89a4861fca27b0ae3fa5f1890a` |
| `questions/2026-10-05-production-function-bound-membership/approved-answer.md` | `d9ddea04a44d2307cf587bc4ae9b2a1c50d062c4077306a5bf9ea9da00eca179` |
| `questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md` | `9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3` |

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-07-rec-desc-finite-reflection-adversarial.md` only.
- Baseline: `1870b1330160e83b71756f60300900f3e2ff4545`.
- Changed dependency hashes: none observed; frozen hashes above identify the direct inputs.
- Claim/review status: conditional fiber-reflection theorem and logical falsifiers; frozen, unreviewed, research-only. No actual source counterexample, closed descriptor gate, independent review or production authority is claimed.
- Checks already run: bounded pinned-section reads and dependency SHA-256/byte equality; no tests/builds/probes. Primary owns final exact diff/lease inspection and dependency revalidation before integration.
- Proposed one-line research-checkpoint commit message: `research: isolate descriptor witness-fiber finite refutation`.
- Shared-record deltas intentionally left for primary/curator: retain `DESC_CLAUSES`, `SEM_JOINT` and `REC-DESC` open; if this artifact is accepted, add the finitary-factorization/compatible-fiber/finite-conjunction obligations as a method-specific proof route and explicitly exclude the natural-number example from countermodels to pointwise FH. No task, index, authority, theory map or question bundle was edited.
- Next action: test the actual latent Function clause against H1–H5 or discharge coherent extension directly from its pointwise local rules.

Writes stop at submission. This artifact is frozen for external review.
