# REC-DESC: adversarial attempt against pointwise finite extension

Date: 2026-10-07
Baseline: `3cf6bb70b7514e6a17a3d3adb8fce0f4e7676c38`
Gate/method: REC-DESC; cardinality obstruction and source-clause discrimination
Status: frozen, compiler-referee-reviewed research checkpoint; no gate closure
Claim class: elementary logical obstruction; failed application to actual FH
Exclusive lease: this file only; no semantic or implementation authority

## Objective and outcome

Attack the compatible-extension premise of FH while fixing the actual provider,
descriptor, original scopes and original `(xi,w)` before choosing a history.
The prior `N >= n` example is excluded: its already chosen natural eventually
cannot extend. The later coherent-path theorem is retained, not reproved.

A different mathematical obstruction survives **pointwise finite extension**:
every finite partial injection from an uncountable index set into the naturals
extends without changing an old coordinate, while no total injection exists.
All its constraints are binary and finite. Thus serial finite extension by
itself does not entail the earlier adversarial note's compatible-fiber finite
refutability H5 for an arbitrary joint family.

This is not a countermodel to the whole pinned FH package or to Yulang. No
inspected actual descriptor clause supplies this index domain, cross-event
injectivity relation, or total joint witness at the required binder position.
The model's source application is rejected at that interface. There is no new
actual-clause result and no admitted source counterexample. The note records
the obstruction and its exact failed applicability, rather than interpreting
`DescMem` with a new rule.

## Baseline and governing dependencies

Operative semantic reads use pinned Git blobs. Initial task/index discovery
used the working files as locators; no conclusion depends on their unfinished
contents. The three assigned operating rules were read in full, together with
`rules/question-board.md` for the committed approved decisions.

Exact governing sections:

- [Recursive synthesis](2026-10-07-successor-recursive-synthesis.md) §4:
  pointwise initial certificate, every admitted transition from W, original
  returned handles, four independent history cases, compatible original
  event scopes, and the separate sibling compatibility prerequisite.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2.1–2.2, 3.1–3.7, 10: independently supplied primitive/owner contracts;
  separate `M_E`, `A_E`, and `DescMem`; finite immutable source envelope;
  admission inventory; conditional constructor typing; independently guarded
  Option 2 extras. A finite positive derivation does not discharge its guard.
- [Source-indexed realization](../design/2026-10-04-source-indexed-callback-realization.md)
  §§2–4: joint original witness binding, rigid quantifier placement, inert
  providers, finite reference observations and independent future-use rules.
- [Source adequacy](../design/2026-10-02-source-interface-adequacy-theorem.md)
  §§2–3: guarded future interactions and forward coverage at the same
  assignment; no arbitrary joint-witness inverse follows.
- Prior [localization](2026-10-07-rec-desc-finite-reflection-localization.md),
  [observation bridge](2026-10-07-rec-desc-observation-finite-bridge.md),
  [root/Return attempt](2026-10-07-rec-desc-root-return-clause-attempt.md),
  [adversarial note](2026-10-07-rec-desc-finite-reflection-adversarial.md), and
  [quantifier attack](2026-10-08-rec-desc-finite-reflection-quantifier-attack.md).

Accepted decisions are the committed production Function-denotation answer d1,
decisions 1–5 (Option A); bound-membership answer d1, decisions 1–4 (Option 2);
and inlet-context-domain answer d1, decisions 1–5. Complete typed observations,
independent constraints/admission, original scopes and joint dependencies,
and licensed extras remain distinct. No new language meaning is selected.

## Exact premise and mathematical discriminator

FH §4 does not merely say `forall h exists e`. Its local premise requires
every admitted next transition from a passing W configuration to pass at a
compatible extension of that configuration. Let `b=(xi,w)` denote the fixed
old assignment. The following construction isolates the mathematical
extension requirement; its presentations are **not** asserted to be admitted
Yulang histories.

Take `I = P(Nat)`. A finite presentation has a finite set `F subset I` of fresh
indices, and its event coordinates form a partial function

```text
e : F -> Nat.
W(F,e) := e is injective.
L(F,e) := for all distinct i,j in F, e(i) != e(j).
```

The old `b` is an unchanged parameter, with no event coordinate hidden in it.
Extension means function extension: every previously assigned value is fixed.
The empty presentation passes. For **every** finite passing `(F,e)` and every
fresh `i in I\F`, set

```text
k := least natural not in image(e)
e' := e union {(i,k)}.
```

The finite image omits a natural, so k exists; e' is injective and agrees with
e everywhere on F. Reusing an existing index retains its existing value.
This proves the pointwise property

```text
forall finite F, passing e, fresh i:
  exists passing e' extending that exact e to F union {i}.
```

It also gives a passing construction for every finite sequential presentation
and every finite union of requested index sets. It never increases an old
natural, reselects b, resets a configuration, or assumes global membership.
Unlike the rejected `N >= n` model, no finite prefix can exhaust the available
values; every old finite assignment extends at every next index.

For the fiber formulation, let `E = Nat^I` be all total functions, ignoring
typing success, and let

```text
A_F := { a in E | a restricted to F is injective }.
```

Every passing finite e has a total raw extension: use e on F and 0 elsewhere.
Every finite family of presentations has nonempty intersection, because its
union is finite and can receive distinct naturals. Their complete intersection
would contain an injection `P(Nat) -> Nat`, which cannot exist. Explicitly, an
injection j would define a surjection `s:Nat -> P(Nat)` by returning the unique
A with j(A)=n when one exists, and the empty set otherwise. The diagonal set
`B={n | n not in s(n)}` is in no s(n), a contradiction.

Therefore

```text
intersection(all finite F) A_F = empty,
but every finite intersection of these A_F is nonempty.
```

This establishes failure of H5 **for this written mathematical family**, even
with the displayed pointwise finite-extension property and finite-conjunction
coverage. It is an unbounded algebraic result, not bounded enumeration. One
index sort, one witness sort and binary disequality suffice; no global
minimality claim is made. The failed total witness is mathematical, and is
never identified with actual `DescMem`.

## Why this is not an actual FH countermodel

To apply the discriminator, an actual independent descriptor clause would
have to supply all of the following, without shifting any binder:

1. A single joint obligation with this uncountable family of authorized event
   coordinates, rather than a separate witness for each finite interaction.
2. The pairwise cross-event readout and the total witness requirement at their
   original scopes, jointly with the actual `nu,K,D` and provider identity.
3. An independently typed punctured context for every required finite
   presentation, and the exact argument, response, raw-handle and future-call
   cases needed to map it to FH.
4. The actual W/local-check suppliers and the required sibling compatibility
   law on that source interpretation.

None is supplied by this construction. In particular, a fresh coordinate per
event does not establish permission to bind one total function jointly over
all alternative events. If that function was already an original w-coordinate,
it must be fixed before histories; its restriction would expose any finite
collision directly. Introducing it later would change the original binder tree.

Sibling compatibility is another explicit limit. Two independently chosen
finite injections can agree on their overlapping indices yet assign the same
natural to two different indices. Their raw union is a function, but it is not
injective. Sequentially constructing a passing assignment for their joint
finite presentation does **not** preserve both such already chosen witnesses.
The model proves pointwise addition from each passing finite assignment, not
arbitrary amalgamation of independently chosen siblings. FH permits sibling
conjunction only with the supplied compatible joint extension. This note
does not silently turn that prerequisite into an amalgamation theorem or
claim it is satisfied for every candidate pair.

The inspected contracts supply finite decorated graphs and finite reference
derivations, with no finite bound on future histories. They do not supply the
particular uncountable joint binder needed above. Nor does their syntactic
finiteness alone prove that every independently supplied primitive domain and
every complete descriptor witness family is countable. This is a bounded
clause audit, not a repository-wide cardinality or absence theorem. Option 2
allows independently licensed extras; it does not license this example.

The precise stop is the independent latent Function clause's **joint witness
domain and binder position**. Without that clause there is no grounded choice
between a finite, countable-path, countable-joint or larger joint obligation.
The earlier countable coherent-path result remains intact. Repeating larger
finite injection probes could not decide this source premise.

## Mutations, independence, checks and limits

Independent compiler-referee review found no blocking, major, or minor
mathematical findings. It confirmed the finite-extension construction,
finite-intersection argument and Cantor diagonal, while retaining the
applicability boundary: no actual descriptor domain, authorized joint binder,
admission interpretation, or whole-FH countermodel is supplied. The review
also confirmed that overlap agreement does not imply sibling amalgamation and
that the countable coherent-path result is unaffected. It did not verify
baseline provenance of dependency hashes or REC-DESC applicability.

Paper mutations discriminate the obstruction:

- `I=Nat`: the total assignment `a(i)=i` exists, so the cardinality obstruction
  disappears. This does not prove source completion/readout.
- A finite witness range of size B: after B assigned indices, the next fresh
  index cannot extend. This mutation fails the pointwise premise and is
  excluded as an FH attack.
- Remove disequality: the constant-zero total function passes.
- Keep each finite interaction's witnesses separately quantified: every
  finite presentation passes; there is no single total injection obligation
  to refute. This mutation changes the candidate formula's binder position.
- Require amalgamation for every overlap-agreeing sibling pair: the colliding
  pair above falsifies that stronger premise. It cannot be assumed for FH.

No mutation was executed. There is no checker or oracle. The proof uses
elementary set theory and its written constraints; it does not validate actual
source transitions. Prior reviewed notes share the original scope/admission
assumptions and do not independently review this output.

Checks already run: bounded `rg` discovery; pinned `git show` section reads;
Python read-only section extraction; serial SHA-256 and byte-equality checks
of the sixteen direct inputs listed below against baseline, HEAD and working
files. All matched and HEAD was the pin. Some initial broad captures truncated;
operative FH/source sections and the prior attacks were subsequently reread
in bounded captures. No exhaustive repository search occurred.

Budget used: no tests/builds/Oracle, no experimental process, no children, no
formatting or Git mutation. Metadata subprocesses inside each Python read were
serial. Independent reads were batched; no compute campaign ran. No numeric
CPU/RAM/wall-time allowance was supplied or inferred. Aggregate CPU, peak RSS
and reasoning wall time are unknown; reported individual read commands finished
within 0.2 seconds. No seeds, search shards, ranges, timeout or killed run apply.
Only this leased note was written.

Unverified: a source-grounded model satisfying the whole pinned FH package;
actual descriptor/admission clauses and SEM_JOINT; initial world and local W
suppliers; scope/legal completion and sibling compatibility; separate `M_E`,
CarrierMem/WorldMem and simultaneous CompleteMem; REC-DESC, source adequacy,
soundness, principality and production conformance. No gate changes status.

Recommended next action: obtain one actual latent Function clause with its
original binder tree and joint witness domain, then decide whether the
cardinality/completion obstruction applies before attempting further probes.

## Frozen dependency SHA-256

None differed among baseline, HEAD and working files at the check. The primary
owns revalidation before integration.

| Dependency | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `rules/question-board.md` | `8c617ceb978dfa26ce12f4f71ecc8ece22ffd8f1cf1982125b33142f645ae1c0` |
| `notes/progress/2026-10-07-successor-recursive-synthesis.md` | `e34a568946f5c1946c01828aae34e890747477ee8c272775408438acd95aa43f` |
| `notes/progress/2026-10-07-rec-desc-finite-reflection-localization.md` | `1ba67b64fe17d9cac3d558e25d11007db5f73761d7b80fd15e35aeca90fd18bc` |
| `notes/progress/2026-10-07-rec-desc-observation-finite-bridge.md` | `c1a89ab082e1e4560ac493a79260487668fe43cdead50d610224e4ef772e0183` |
| `notes/progress/2026-10-07-rec-desc-root-return-clause-attempt.md` | `3ee501a6611358777c4f1be99ba12794b9e0299f5c30404185f29d54d6e87637` |
| `notes/progress/2026-10-07-rec-desc-finite-reflection-adversarial.md` | `63b70f17794e0b8f21ef9079a0abaa05a75961b99cad0275c6d4d3f6179069c8` |
| `notes/progress/2026-10-08-rec-desc-finite-reflection-quantifier-attack.md` | `374c098ce7880f77af163a711a67acf38b3a02317337b560b63f7a06381e8ade` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-04-source-indexed-callback-realization.md` | `76874a219ac86068027b1f08a5bc27a12d93a0169a52cebd896a6ff6f2c6b671` |
| `notes/design/2026-10-02-source-interface-adequacy-theorem.md` | `6b8f95cfc2380508d500c447c82b64fd2c26fb32248e6fb3244314cc02023660` |
| `questions/2026-10-05-production-function-denotation/approved-answer.md` | `7e7f3c717b16a70fc754c930a1654666c8b61a89a4861fca27b0ae3fa5f1890a` |
| `questions/2026-10-05-production-function-bound-membership/approved-answer.md` | `d9ddea04a44d2307cf587bc4ae9b2a1c50d062c4077306a5bf9ea9da00eca179` |
| `questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md` | `9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3` |

## Commit packet

- Exact changed paths: this note and `tasks/current.md` (primary status synchronization).
- Baseline SHA: `3cf6bb70b7514e6a17a3d3adb8fce0f4e7676c38`.
- Changed dependency hashes: none observed; frozen hashes above.
- Review status: compiler-referee-reviewed, research-only. No model certified
  against actual FH/source clauses and no REC-DESC closure.
- Checks already run: pinned operative-section reads, pointwise-extension
  derivation and diagonal contradiction, direct dependency SHA-256/byte
  equality. No executable semantic checks, tests, builds or Oracle.
- Proposed one-line research-checkpoint commit message:
  `research: test finite extension against joint witness completion`.
- Shared-record synchronization: `tasks/current.md` records the mathematical
  distinction between pointwise finite extension and arbitrary joint
  completion, including the ungrounded domain/binder and sibling compatibility
  limits. Descriptor/admission/REC-DESC gates remain open. No authority, theory
  or question-board file was edited.

The research artifact is frozen after review; any actual countermodel claim requires a source-grounded descriptor clause.
