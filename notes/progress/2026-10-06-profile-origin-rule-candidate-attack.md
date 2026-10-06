# Captured-step original profiles: candidate origin grammar and premise attack

Date: 2026-10-06
Baseline: `bab14bf7a740d271e9c27585d4fb9371c1cf0230`
Status: research-only producer artifact; frozen on submission; independent review pending
Claim classes: candidate grammar, conditional grammar inversion, bounded premise audit
Scope: original profile at the outer `f` of the exact captured-step component
Exclusive lease: this file only
Semantic, theorem-status and implementation promotion: none

## 1. Objective and result

Construct a candidate origin grammar independently, then attack its premises
rather than enumerate profiles admitted by a supplied transition system. The
exact source remains:

```text
my apply f = { my step x = f x; step }
```

The candidate has three introduction families: written annotation, direct
source Function elimination, and independently certified declaration origin.
It rejects an extra position **as a derivation in that candidate grammar**.
It does not prove that those families exhaust the original source judgment.
No independently source-licensed `p != p0` was constructed.

One premise attack discriminates two meanings of “direct resolved Function
elimination.” Requiring a Function already known from an annotation or
declaration fails even to derive the accepted immediate seed for unannotated
`f`. Generating the dependent Function constraint from the resolved source
application succeeds before solving. This repair yields the positive seed,
but still does not justify an exhaustive grammar for original profiles.
The retained Call construction already establishes this distinction; the
mutation tests the candidate's wording rather than reopening that result.
No new original-introduction premise is discharged by this audit.

The implicit-formal and dependent-result alternatives are not ruled out by
the approved formation direction merely because they are implicit or symbolic.
Neither alternative currently has an independent first-introduction rule.
The observation quotient supplies neither that rule nor a realizable exact-
source separation witness. This is a proof-completion blocker, not evidence
for a different selected language meaning or a new user decision.

## 2. Fixed authority, inputs and hypotheses

Authoritative inputs are [inferred call views](../design/2026-10-05-inferred-function-call-views.md)
§§1–5 and the [nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–4. They fix sequential binding, returning `step` without invoking it,
lexical resolution of `f` and `x`, capture of the same outer `f`, one shared
inferred contract, stable source identities, Q-independent formation, full
protection caused by annotation absence, and the scoped formal-role refinement
without changing a supplied callable's actual role or entry.

Conditional mathematical inputs are [source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
§§2–3/10, [typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
§6 and [typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md)
§6. Their source envelope is already decorated: profiles and typed owner/view
premises are supplied. Exhaustive execution-clause accounting in that envelope
is not exhaustive raw-source profile formation.

The [initial call construction](2026-10-06-source-call-generation-construction.md)
§§3–4 is retained as an established bounded research input, including:

```text
Gamma(f)=Value(A_f)             Gamma(x)=Value(A_x)
c=call(result(name f),result(name x))
R_f; one dependent complete F_c at R_f
beta=(d_f,R_f)                 p0=(beta,call.effect)
ElimOrigin(c,u_f,d_f,R_f,p0,p_out(c))
FullProtection(p0); no annotation-removal grant
```

It supplies the initial contribution, not complete `Slots_original(beta)`.
The [introduction construction](2026-10-06-profile-original-introduction-construction.md)
and [extra-origin classification](2026-10-06-profile-extra-origin-falsification.md)
were read after selecting the candidate rule-premise method, to respect their
failed routes. Their consumer-count, packet-inversion and twelve-mechanism
searches are not rerun here. This artifact is an independent production
method, not an independent review of those inputs.

The quotient audit is read at the explicitly assigned historical revision:

```text
git show f762d7464:notes/progress/2026-10-06-profile-completion-observation-quotient.md
```

That path is absent from `bab14bf7a`; the explicit historical input is kept
separate from the semantic baseline and contributes no new authority.

All reasoning uses the original scope tree and **one** `xi=(nu,K,D)`. Incoming
provider/result packets are indexed inherited inputs. The source-owned
introductions of this component are distinct from those inputs even if an
inherited packet carries an equal static label. Copying, receipt, dynamic
activation and aliasing are not new original introductions.

## 3. Independent candidate grammar G

Let `OriginalApplicable(C,d_f,R_f,p;xi)` denote the original source judgment
whose complete introduction rules are under investigation. It is not defined
by G's output. The candidate judgment is separate:

```text
Origin_G(C,n,beta,p,reason;xi)
```

Its source terms and reasons remain recorded, rather than identifying an
origin with a solved effect row. Candidate rules are:

| Rule | Independently named premise | Candidate conclusion |
| --- | --- | --- |
| G-Ann | A real written annotation occurrence at source node `n`, lexical slot resolution, and its admitted annotation-to-path derivation | An original contract position at the path governed by that occurrence; only its specified contribution receives any concrete permission |
| G-Call | A resolved source application `n`, its callee's lexical root and the initial Function-elimination constructor | The dependent complete Function variable, source incidence and immediate `call.effect` position |
| G-Decl | A source declaration/primitive with an independently certified profile introduction and original component identity | Exactly the positions and contributions in that certified declaration contract |

An import preserves its declaration's own origin; it cannot become an
introduction by C merely because C receives its packet. A local definition's
own slot also cannot be relabelled `beta_f` by endpoint equality. These are
ownership conditions on the candidate rules, not a claim that declaration
profiles have already been derived for every possible declaration.

Name, Result, Bind, capture and typed adaptation retain origins through the
existing indexed packet images. Receipt adds receiving ownership. Boundary
introduction allocates a dynamic boundary with a supplied static profile.
None of these operations concludes a new `Origin_G`. Their retained packet
judgments are separate from G's first-introduction judgment.

G-Call deliberately means **source constraint generation**, not successful
resolution of `A_f` to a Function head. It inherits the independent positive
constructor above; it does not ask Q or choose independent witnesses for
Function ports. G-Ann likewise requires its genuine annotation derivation;
the printed/public type or an internal seed is not a written annotation.

Three assumptions would be needed to use G for the original source theorem:

```text
Sound_G: Origin_G(...) implies the corresponding original introduction.
Complete_G: every original introduction at C factors through one G rule.
Preserve_G: the factorization preserves contribution witnesses, paths,
            original scopes and whole xi, including inherited inputs.
```

`Complete_G` is the missing exhaustive rule bridge, not a definition of
`OriginalApplicable`. This separation prevents a candidate checker from
proving source completeness by defining the reference as its own output.

## 4. Conditional rejection and the smallest premise discriminator

**Conditional grammar statement.** Relative to G's stated introduction
rules, the selected exact source tree, lexical resolution and initial Call
constructor, every `Origin_G` at this component's `beta_f` has position `p0`.

**Derivation.** Invert the last G rule. G-Ann has no written occurrence in C.
G-Decl has no independently profiled declaration of the outer formal `f`;
an ambient declaration/import belongs to its own component and the local
`step` definition has its own identity. G-Call has exactly one application
with callee root `d_f`, namely c, and concludes `p0`. Packet transport has no
first-introduction conclusion. Thus a finite G derivation with conclusion
`beta_f,p != p0` has no possible last rule. This is an impossibility result
**inside the candidate grammar**. Applying it to an arbitrary original
witness would require `Complete_G`, which has not been established.

Now mutate only G-Call's premise to:

```text
G-Call-known requires Gamma(f)=Value(KnownFunction(F))
from a written annotation or independently declared Function interface.
```

The smallest relevant subtree of the exact selected program is `f x`, with
the independently generated context `f:Value(A_f), x:Value(A_x)`. Neither
ordinary formal is annotated, and `A_f` is still symbolic. Lexical resolution
identifies `d_f`, not a pre-solved Function interface. G-Call-known therefore
cannot apply; G-Ann and G-Decl cannot supply its Function premise. It emits
no `p0`, contrary to the accepted bounded initial-call construction.

This is a minimized **rule-premise rejection**, not a type-error claim or an
extra-profile counterexample. Restoring source application plus generation of
dependent `F_c` repairs it. If “resolved Function” was already intended to
mean this source constraint generation, the mutation does not attack that
intention; it identifies the exact premise the final grammar must state.

The repaired rule cannot infer `Complete_G` from the presence of its seed.
The approved §2 explicitly permits formation from declarations, definitions,
uses and recursive components without annotation, and §5 leaves the exact
profile-producing judgments open. Those sentences do not enumerate G's three
families, nor impose a source-consumer locality theorem on every contract.

## 5. Implicit formal and dependent result clauses

A possible implicit-formal clause has the schematic shape:

```text
NoAnnotation(d_f), shared contract R_f, independent source profile derivation
--------------------------------------------------------------------------
IntroFormal(C,d_f,R_f,dependent positions and contributions;xi)
```

Approval of implicit formation and full protection supports the need for
some such connection to the shared contract. It does not supply the omitted
profile derivation or enumerate its positions. Typed-core §6's `Value(A_f)`
fixes entry/rebind behavior; it does not mean `A_f` lacks nested Function or
Thunk contracts. Consequently neither annotation absence nor ordinary entry
proves that an implicit clause can contribute only `p0`.

A more specific candidate extra clause can name a symbolic result root
`A_c` at c before solving, preserve `beta_f`, and carry a dependent path
schema for later result ports. It can be Q-independent and natural under
uniform substitution. Its first-generation justification would need:

```text
resolved c, shared F_c and original xi
plus independently licensed source result-contract formation at c
----------------------------------------------------------------
Intro_original(C,c,beta_f,p_result,kappa;xi), p_result != p0
```

The missing second premise is substantive. Naming c and A_c in a predicate
is not a source license. Typed-core's symbolic result construction produces
`Computation(E_c,A_c)`; Normalize consumes its known outer computation and
retains its profile. Typed-boundary §6 takes an independently supplied
callee-result profile as one indexed input to result transport. Neither
rule concludes the displayed first-generation judgment.

Conversely, the “no solved-shape-created origins” requirement does not forbid
every preintroduced dependent schema. A schema would need a real source
formation derivation first; solving could then instantiate its already
licensed paths while preserving the same original witness. The approved
direction constrains that derivation but does not currently establish it.
Thus a dormant symbolic-result candidate is **unlicensed**, rather than a
proved impossibility for every eventual Authority-conformant rule package.

G is minimal in its currently certified positive output. Minimality of that
candidate output does not establish principality of the original relation.
An omitted source clause could restrict whole xi or introduce a contribution
without adding an immediately executed source consumer. No such clause is
asserted to exist here; excluding it requires `Complete_G` and contribution
inversion. Under the repaired G-Call and the hypothetical dependent-result
attempt, this same premise remains untouched. This lane stops there instead
of implementing another supplied-profile checker.

## 6. Observation quotient: no realizable exact-source witness

The historical quotient audit gives a conditional kernel discriminator: an
added protected, no-grant incidence changes a handler candidate precisely
when the candidate is active and covering, has no common protection or
grant, and has a live matching added incidence. That is a calculation on
independently supplied typed packets, paths and receipts.

For the exact source, the candidate extra still lacks its original
introduction witness from §5. It also lacks the actual receiving assignment
and activity facts necessary to make the added incidence live. Returning
`step` and retaining captured `f` do not establish those latter facts.
A supplied latent-result profile in an external provider is inherited, and
cannot certify a new original position in C. Hence the quotient condition
is not a realizable exact-source counterexample to G's source completeness.

Nor does local receiver expiry prove that G exhausts the original static
relation. Source-contracts §2 keeps retained predicates active at their
original incidences, while typed-boundary §6 retains source tags, profiles,
the shared K ledger and matching D references. A quotient would additionally
need every-original-solution lifting and complete independent admission and
observation equivalence. Candidate-local disappearance of an incidence does
not supply that certificate.

No Oracle output or global equivalence oracle is used. The candidate and
the audited conditional machinery share the approved source tree, initial
Call seed, original binder identities and supplied typed-kernel contracts.
They are not two independent implementations of raw-source formation. No
bounded execution result is being substituted for source-rule validation.

## 7. Checks, limits, resources and failure conditions

Checks were sequential read-only `git show`, bounded `rg`/`sed` and Python
standard-library SHA-256 comparisons, followed by this single leased note
write and a narrow whitespace/local-link check. An early combined capture
was truncated; relevant derivations use subsequent targeted section reads.
The attempted baseline lookup of the historical quotient path failed because
the path is absent from `bab14bf7a`; it was then hashed at its assigned
`f762d7464` revision. That failure is not a dependency equality result.

Coverage is three candidate first-introduction families, their conditional
last-rule inversion for one exact tree, the explicit KnownFunction-premise
mutation, and two proposed missing-rule premises. This is not an exhaustive
search of source grammars, source programs, typings, profiles, worlds or
histories. Seeds and numeric ranges are inapplicable to this manual method.
No compiler tests, builds, executable model, Oracle run, performance samples,
Git mutations, child processes for research builds, questions or shared-file
writes were performed. Only one lightweight read/check command was active
at a time; heavyweight-process count was zero. No numerical CPU/RAM/wall
budget was assigned in the packet. Exact elapsed time, CPU time and peak RSS
were not instrumented; this was a bounded manual session with no enumeration.

The G inversion fails if G gains an independently licensed formal/result
introduction, or an inspected premise incorrectly excludes a declaration
origin at beta_f. The G-Call-known discriminator does not apply when “known”
already includes the source-generated dependent Function constraint. A real
original completeness certificate could validate G; a real extra-origin
derivation could refute it. Neither was produced here. A realizable quotient
witness would additionally require the omitted actual receipt/liveness and
independent admission certificates.

Unverified scope: original introduction/contribution completeness, full
same-root seed/refinement preservation, actual packet attachment and receiver
activation, evidence-rich principality, full-world admission, production
source acceptance and Option A/Option 2 conformance.

Recommended next action: require a source-rule package for the exact formal/
Call seam whose **independently interpreted original premises** prove or
refute `Complete_G`, including implicit-formal and dependent-result cases;
retain the source-generated dependent Function premise of G-Call. Review that
package before funding another quotient or supplied-transition experiment.

## 8. Frozen dependencies and commit packet

The following direct inputs were read at `bab14bf7a` and matched worktree
bytes when checked:

| Input | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| `notes/progress/2026-10-06-profile-original-introduction-construction.md` | `c5ec22bab3b082de6c460aff3b6775fe9aa0f0624659748e9c5b2feb2d08d8c9` |
| `notes/progress/2026-10-06-profile-extra-origin-falsification.md` | `abbef6d58c5e5691e84ed85fb85038a9805a3a237e19769bdae3dce9da60bf05` |

The explicitly pinned historical quotient input at `f762d7464` has SHA-256
`967f4efbf16e023e571d7504b26b50238074714bbb6c81b0740cc9515a6f4b17`.
It is not claimed to be a baseline-present or live-worktree dependency.

Commit packet:

- Exact leased path: `notes/progress/2026-10-06-profile-origin-rule-candidate-attack.md`.
- Baseline SHA: `bab14bf7a740d271e9c27585d4fb9371c1cf0230`.
- Dependency hash changes: none observed for baseline-present direct inputs;
  historical input pinned separately as above. Revalidate before integration.
- Review status: frozen producer-authored research-only artifact; independent
  review pending; no original-profile theorem or authority promotion.
- Checks already run: governing section reads; conditional grammar inversion;
  KnownFunction-premise mutation; direct-input byte/hash comparison; leased-note
  whitespace/newline/local-link and dependency recheck before submission.
- Proposed one-line research-checkpoint commit message:
  `research: attack original-profile candidate grammar premises`.
- Shared-record deltas intentionally left for primary/curator: retain P open;
  record the distinction between pre-known Function type and source-generated
  dependent Function constraint; retain `I-formal/I-call-rest/I-exhaust` as
  missing original-rule premises; do not promote G completeness or quotient
  closure. No shared task/index/authority/theory/question file was edited.
- Writes stop before submission; primary owns independent review and Git
  integration.
