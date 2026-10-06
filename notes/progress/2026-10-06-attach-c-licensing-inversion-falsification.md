# Attach_C licensing inversion: bounded comparison and the Option 2 quantifier

Date: 2026-10-06
Assigned baseline: `cae29e238397cfa5dd490bf52d664c0f965806df`
Status: compiler-referee-reviewed research-only unsuccessful falsification; no findings in scope
Method: compare prior attacks, then audit the quantifiers of the proposed inverse
Exclusive lease: this note only
Semantic and implementation authority: none

## Objective and result

Attack, on the exact original row for
`my apply f = { my step x = f x; step }`, the local candidate
`Lic_C(X,t) iff Attach_C(X,e0,t)` and its existential-image generator.
**No novel same-X countermodel was constructed.** Endpoint keys, multiplicity,
inherited-packet retagging and the external step-entry carrier were already
attacked by other workers; this note does not rerun those probes.

The distinct attempted route was an unanchored production alternative under
Option 2. It fails to establish a falsifier: lack of a source-execution anchor
for an observation does not establish lack of attachment to a source-owned
signature exposure. Those predicates have different witness sorts. This is
a bounded quantifier audit, not a proof of the candidate law, existence of an
extra, or an independently admitted source row.

## Authority, baseline and explicit hypotheses

Read directly: [FVIEW](../design/2026-10-05-inferred-function-call-views.md)
§§1.1–5; [source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
§2.2, §§3.1–3.7 and §10;
[directional protection](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
§§2–4; and [nested-block meaning](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–3. Option 2 is selected; the particular §3.7 abstraction grammar is only
a conditional sufficient construction, not selected production semantics.

Research inputs: [licensing construction](2026-10-06-original-signature-licensing-construction.md),
[constructor derivation](2026-10-06-original-signature-constructor-derivation.md),
and [profile/admission construction](2026-10-06-source-profile-admission-construction.md).
The [mapping](2026-10-06-attach-law-mapping-adversarial.md),
[slot scope](2026-10-06-slot-profile-scope-adversarial.md), and
[multiplicity](2026-10-06-original-signature-licensing-adversarial-next.md)
attacks were read to avoid duplication. The
[contribution typing attempt](2026-10-06-attach-law-construction-attempt.md)
locates the current missing association judgment.

H: the approved resolved core graph and original binder tree; ordinary
symbolic constructors; selected unannotated formal seed and same-root
exposure. Reuse, without reproving, the conditional singleton direct-exposure
inventory `E_C(beta)={e0}`. Preserve the same candidate whole row X, including
original `xi=(nu,K,D)`, upper demand, providers, environment, world,
continuation and retained constraints. H includes neither complete licensing
nor complete-row validity/admission. No method/role resolution is supplied.

Use distinct sorts:

```text
e0 = (k,beta,u,sigma,p0)      original upper introduction
t  = (beta,s,p,c)             original signature incidence
y                            whole membership observation
d                            source execution derivation
```

An observation y is not automatically the original contribution c. The
complete invocation operand is not automatically its typed contribution.
Protection at p0 is not membership, a receipt, or a provider-lower mark.

## Exact local discriminator and failed Option 2 route

For fixed X, singleton exposure gives only the definitional reduction

```text
G_C(X,t) = exists e in {e0}. Attach_C(X,e,t)
         iff Attach_C(X,e0,t).
```

Thus the smallest logical falsifier needs one X and one original tagged t:

```text
F_forward: Attach_C(X,e0,t) and not Lic_C(X,t)
F_inverse: Lic_C(X,t) and not Attach_C(X,e0,t).
```

These are witness specifications, not instantiated witnesses. Even a second
licensed incidence cannot refute the relation merely by being second:
Attach_C is allowed to be one-to-many. An admitted-language falsifier would
add independent complete-row and initial/history admission proofs on X.

The new route considered a permitted production observation with no source
anchor. In the conditional §3.7 grammar, assume for this attempt only:

```text
HardEnvelope_X(y) and Z_X(y)
no d derives y in the source base R_X
```

These premises conditionally give membership in `H_HardEnvelope(R_X)`.
They give no conclusion of either displayed falsifier. To refute the inverse
one would still have to prove all of:

```text
independently typed original contribution/slot association T_X(y,t)
Lic_C(X,t)
not Attach_C(X,e0,t)
```

The first premise must not be a cast from observation y to contribution c.
The second must not be defined by production membership. The third must not
be inferred from the absence of d. In particular, a signature's complete
invocation contract can cover an independently licensed conservative
observation while retaining the original source exposure u; the absence of
a source execution deriving that observation does not logically remove u.
This is a compatibility possibility, not an instantiated attachment theorem.

Conversely, licensing every production observation as a fresh beta-owned
incidence would require its own source ownership/typing rule. Option 2 does
not provide that rule or permission for a new capture grant. Reading
`A_invert` as requiring a source execution for every production observation
changes its domain from original signature incidences to membership witnesses.
That strengthened reading is unsupported. The actual local law remains open.

## Bounded comparison and stopping point

| Suggested candidate | Status after comparing the retained evidence |
| --- | --- |
| Distinct original slots/positions/contributions | Need independently typed associations on X; arbitrary extra labels are not a falsifier. |
| Inherited versus beta-owned incidence | Source-arm inversion was already audited; an inherited same-beta label does not establish own-source Lic. |
| Callback versus output position | Existing external-step-carrier attack lacks independent beta ownership and complete admission. |
| Annotation versus internal contribution | Exact source has no annotation; adding one changes C. Source/public/internal layers stay distinct. |
| Same endpoint, different contribution | Existing mapping attack already rejects endpoint casts; no new independently licensed pair is supplied. |
| Multi-use or recursion | A new source Call/recursive reference changes this exact graph; repeated dynamic use does not supply an original association law. |
| Production-only observation without source anchor | Distinct attempted route above; observation-to-incidence association and negative attachment are both unproved. |

The precise blocker is still the independently interpreted source introduction
and inverse for `OriginalAssocType_X(beta,p0,j_call;s,c)`, followed by
`Attach_C => Lic_C` and `Lic_C => Attach_C` on the same X. A constructor of
the complete invocation expression or a singleton exposure inventory supplies
neither the typed association nor the list of all original licensing last
rules. Previous attempts already left this premise untouched; no additional
toy enumeration was run.

Recommended next action: expand the original contribution/slot constructor
and its licensing last rules, explicitly stating whether conservative
membership alternatives change a contribution contract or introduce an
original incidence. Then test its inverse on the same X. This is proof work
under the selected contract, not a request to reopen language meaning.

## Coverage, independence, checks and resources

Finite analytical envelope: exact approved graph, one original exposure,
one hypothetical incidence and one hypothetical unanchored observation;
seven candidate classes compared above. No source-program enumeration,
random seed/range, executable mutation, test, build, runtime checker, Oracle
execution, formatting, scratch output or child delegation occurred. No
uncovered search shard is represented as complete. Whole descriptor/provider/
world/carrier validity, complete profiles, recursive/general source coverage,
all histories, principality and production inclusions remain unverified.

Logical failure mutations: replace incidence inversion by source-execution
inversion (changes the quantified sort); cast y or j_call to c (assumes missing
typing); infer nonattachment from absence of a source derivation (missing
cross-sort bridge); use successful Q or a separate xi to create the witness
(violates formation independence or correlation). These were audited, not
executed as tests.

Oracle supplies no premise. This audit shares H and independently interpreted
kernel obligations with its predecessors; it does not validate those rules
or count as independent review. A checker supplied with attachment/licensing
rules would check those assumptions and could not prove their source meaning.

Commands: bounded `cat`, `sed -n`, `rg --files`, `rg -n`, Python SHA-256,
lease-absence and note-integrity checks. Initial `git rev-parse HEAD` and
`git status --short` were read-only but exceeded the packet's literal no-Git
instruction; no Git mutation occurred and no further Git command was used.
Initial aggregate captures truncated; decisive governing and predecessor
sections were reread in bounded captures. No repository-wide absence claim.

Output budget: one note, consumed. Lightweight shell/hash processes only;
zero heavyweight processes. No numerical CPU/RAM/wall budget was supplied;
CPU time, peak RSS and total wall time were not instrumented. The pinned HEAD
was observed at startup; final baseline-byte equality is primary-owned.

## Frozen direct dependency hashes

SHA-256 at freeze; no dependency edits by this worker:

| Input under notes/ | SHA-256 |
| --- | --- |
| `design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `progress/2026-10-06-original-signature-licensing-construction.md` | `f5032a91781706551dcd01474f6024eb34fcb0cb110fa6157f7ec577ccfc5cff` |
| `progress/2026-10-06-original-signature-constructor-derivation.md` | `5dc90af8e6c789487ed3f0cb82ba254ce7a99648350f7dbce0e0f000184f8f19` |
| `progress/2026-10-06-source-profile-admission-construction.md` | `00f9e4e8db427fe97a46bd25245cf235c02d2e38007c5b9bb9088d9b40db8636` |
| `progress/2026-10-06-attach-law-mapping-adversarial.md` | `ed64f8c2e88486db608568753828d41ab48599fa43a16c06db14ddad516095ba` |
| `progress/2026-10-06-slot-profile-scope-adversarial.md` | `4b657fe4226717d7d7cd758283dd4ccede2c2618bbe5d9b6920961768ad8d649` |
| `progress/2026-10-06-original-signature-licensing-adversarial-next.md` | `76ccf31fba662d637e57600933ba12bb5f75d31b4f460d778ea8bb510363cd29` |
| `progress/2026-10-06-attach-law-construction-attempt.md` | `b94e829e06027c2bd4cc2f0dbf4a33dc954aa10ee058fbc4918da75ad151a241` |

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-06-attach-c-licensing-inversion-falsification.md`.
- Baseline SHA: `cae29e238397cfa5dd490bf52d664c0f965806df`.
- Changed dependency hashes: none observed between reads and freeze; pinned
  baseline-byte comparison remains for the primary.
- Review status: frozen, unreviewed bounded unsuccessful falsification and
  quantifier audit; no independent review or gate closure.
- Checks already run: governing/predecessor reads, same-X/sort audit,
  dependency hashes and recheck, lease-absence and note integrity. No runtime
  verification.
- Proposed research-checkpoint commit message:
  `research: bound Option 2 falsifiers to original licensing inversion`.
- Shared-record deltas intentionally left for primary/curator: no new
  countermodel; distinguish production observation ancestry from original
  signature-exposure ancestry; retain original association, licensing,
  complete profile/row and admission gates as open. No shared record changed.

Review: compiler_referee PASS on the frozen note content SHA-256
`13cb079f7c60cd4111752d0b38a6255cd7c860ffc3c41043ce47b94b7686eec0`.
The audit covered same-X quantifiers/sorts, the conditional §3.7 Z arm, and
the specified inverse falsifier; no compiler implementation or independent
admission theorem was reviewed.

Writing stops before submission for frozen review.
