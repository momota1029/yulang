# Exact-candidate P boundary: profile completeness by rule inversion

Date: 2026-10-06
Baseline: `b0dd026bb9438b7dfb13c68a474a49145eb97555`
Status: frozen research submission; unreviewed; non-authoritative
Method: restricted rule inversion, with a minimal typed transport discriminator
Scope: `my apply f = { my step x = f x; step }`, P only
Implementation authority: none

## 1. Result and claim class

The generated singleton `InitialSeedSlots(beta)={p_0}`, approved same-root
role result, and existential decorated Call do not **derive** complete
original `Slots(beta)`, `Foot_S`, or source-profile normalization in the
displayed constructor inventory. Inverting the decorated Call extracts its
supplied profile certificate. It does not construct that certificate from
the singleton seed. This is a bounded proof-interface obstruction, not a
counterexample to the selected source meaning or an impossibility theorem
for P.

No Authority-consistent pair of complete source realizations with different
original inventories is established here. In particular, adding a latent
slot because a Function result can contain a Thunk would not establish such
a pair. The small pair in §4 instead discriminates inherited actual-value
evidence from original contract contributions. Both legs are abstract typed
transport derivations; neither is asserted to be an execution of the exact
source component.

## 2. Baseline, dependencies and hypotheses

The source skeleton and capture identity are fixed by the Authoritative
[nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–3: the block returns `step`; only a later invocation executes `f x`;
that use refers to the same outer `f`. The approved
[q1/a2 answer](../../questions/2026-10-05-function-call-view-formation/approved-answer.md)
and [call-view contract](../design/2026-10-05-inferred-function-call-views.md)
§§2–5 fix the protected internal Handler seed, the singleton ordinary-Value
formal/use refinement, annotation-dependent protection, scope retention and
comparison-independent formation. Actual provider role and entry remain
distinct from that internal refinement.

The examined construction is
[source-call generation](2026-10-06-source-call-generation-construction.md)
§§4–7. Its initial address and interpreted existential Call are retained as
positive results. The remaining footprint interface is also stated in
[main-source generation](2026-10-06-main-source-generation-minimal-clause.md)
§6. The interpreted relation inventory and conditional conformance theorem
come from [source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
§§2–3; §10 retains the adoption boundary. Transport/introduction/receipt and
activation are distinguished by
[typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md) §6.

The restricted inversion has these explicit hypotheses:

1. Use only the displayed source constructors, canonical role/address record
   constructors, independently interpreted decorated Call, and typed packet
   transport/receipt/observation rules. An independently specified primitive
   P rule is not already among the inputs.
2. A profile-introduction step requires its source-derived signature profile;
   this is the introduction premise of typed-boundary §6. Generic descriptor
   well-formedness does not identify that original source profile.
3. `TypedCallCert_Dec` retains the supplied decorated profile, receipt,
   observation and correspondence premises, exactly as construction §5 says.
   It is not redefined to mean a raw-source derivation of them.
4. Work at the original scope with one shared `xi=(nu,K,D)`. No successful
   comparison, per-port witness choice, or production/source identification
   supplies a missing premise.

These hypotheses describe the existing displayed route. They do not prohibit
a future source-applicable P constructor or decide whether that constructor
will prove a singleton inventory.

## 3. Restricted last-rule derivation

For the single resolved application `c=Apply(u_f,u_x)`, source-call §4 gives

```text
beta = (original d_f,R_f)
p_0 = (beta,call.effect)
ElimOrigin(c,u_f,d_f,R_f,p_0,p_out(c))
InitialSeedSlots(beta) = {p_0}
SeedPolicy(beta,p_0) = FullProtection
AnnotationRemovalGrant(beta,p_0) = None
SeedRole(R_f) = ProtectedHandlerSeed
RefinedFormalRole(R_f) = NonHandlerFormal
```

The deterministic address records are unique up to coherent renaming. This
derives an immediate complete-invocation effect address before the result
shape is solved. It does not derive `p_0=result.latent.effect`; those are
different typed positions. Nor does it derive a live receiver or runtime
observation from `ElimOrigin`.

Suppose a derivation additionally concludes the **complete original**
applicable-position/contribution relation and its normalization. Inspect the
last rule that first supplies this source interpretation:

| Candidate last rule | What inversion provides | Why it does not supply complete original P |
| --- | --- | --- |
| Canonical role/address construction | The records above, on the shared source root | It produces the initial Call contribution; it states no exhaustive test over other dependent positions or original contributions. |
| Name, capture, binding or result transport | An input packet and matching typed correspondence | Relational image preserves an input profile witness. It cannot identify a new original profile or its complete domain. |
| Boundary introduction | A fresh boundary with a supplied signature profile | The missing source profile is an input premise to this rule. |
| Receipt or observation | A received view or an executing typed port | Neither introduces a boundary/profile; observation alone supplies no original contract contribution. |
| Decorated Call | `F_c,e`, including the retained full profile certificate | These are existential witnesses satisfying decorated premises, rather than their source constructors. |
| Conjunction, scoped binding, renaming or constructor composition | Joint premises or their uniform image | Original interpretation must already occur in a premise. Composition adds no independent source-profile clause. |

Consequently no such first rule exists under §2's restricted inventory.
This is induction on a finite derivation; a recursive reference only points
to a registered relation and does not introduce an unexplained profile
primitive. Supplying an independently interpreted P primitive defeats the
obstruction, as intended.

In particular, the Call equivalence is correctly conditional:

```text
decorated Call derivation
  iff exists F_c,e satisfying WF_Dec, checking, image and TypedCallCert_Dec
```

Both directions retain the same decorated profile premise. They do not yield

```text
source Call occurrence + initial address/roles
  => original profile certificate extracted from e
```

Source-contracts §3.5 requires local typing and a source-conformance
certificate before its inverse correspondence applies. Its proof does not
remove this requirement. Taking all satisfying decorated witnesses may give
a legitimate interpreted envelope; equality with original source profiles
still needs both directions of P's source inversion.

The inverse `erase/lift` proof of source-call §4 concerns canonical role and
address records. To promote it to seed-to-refined **full-view** preservation
would require an independently interpreted relation at both stages and a
map retaining the original contribution/path incidences and unrelated
packet evidence. The record inverse does not supply those semantic premises.
`NonHandlerFormal` neither grants annotation removal nor changes the actual
callable's role/entry. This obstruction does not license erasing protection.

## 4. Minimal typed pair: inherited result evidence

This pair attacks a specific shortcut: treating the resulting view's entire
profile as the original profile contributed by `beta`.

Take one finite supplied Function signature with two effect-position sorts:
`p_0=call.effect` and `p_1=result.latent.effect`. Let its result be one latent
value with effect position `q=latent.effect`. Typed result transport has
`M_result(p_1,q)` and has **no** `M_result(p_0,q)`.

Supply two alias views of the same underlying latent value `v`, with the
same value signature, ledger, dependent incidences and lineage:

```text
V_0 = (v,t, chi_0={},             K,D,L)
V_1 = (v,t, chi_1={(q,b_ext)},    K,D,L)
```

Here `b_ext` is one separately supplied well-formed protected boundary
witness at that latent position, with no concrete grant. It is not a
boundary created by `beta`. Alias views can differ in attached boundary
evidence under typed-boundary §6; underlying pointer equality does not merge
their views. A typed witness, including its ownership references, is an
explicit input, not evidence that either alias has been source generated.

Fix the same supplied callee-result contribution on both legs; choose none
at `p_1` for this discriminator. Apply the actual-result correspondence
`Id(q)` and the indexed union rule. The resulting profiles are respectively
empty and `{(q,b_ext)}`. The initial `beta` policy at `p_0` contributes nothing
to `q`, since the requisite typed path is absent. The two outputs therefore
differ while their initial Call records and selected formal roles agree.

This is minimal for the shortcut: one latent effect position, one external
profile incidence and identity transport suffice. `p_0` is retained to test
the actual outer-versus-latent confusion. Removing the external incidence
removes the distinction; adding the forbidden `p_0 -> q` correspondence
changes the premise rather than explaining the result. No operation-family
equality, handler event or request is needed.

The pair establishes neither a second original slot of `beta` nor two
satisfying decorated Calls for the exact component at fixed `xi`. It only
shows why inherited result evidence is not an oracle for P. A complete P
rule must separately identify its newly introduced contribution and retain
any independently supplied actual-result packets.

## 5. Policy, activation and omitted claims

Annotation absence fixes full protection at the applicable original
positions and gives no concrete removal grant. It does not determine the
position domain by itself. The annotated `[io]` alternative grants scoped
permission; it does not prove removal occurs and cannot grant removal for
unrelated contributions. Neither policy licenses deriving a latent slot
from row support or copying the `p_0` policy to every descendant.

Persistent profiles are also distinct from actual protection of a handler
candidate. Typed-boundary §6 requires matching `Flow`, the executing view's
`Observe`, an actual `Receive`, and current activity of the handler, its
owner and original receiver. Static Call/address/role records alone satisfy
none of those activation premises. An expired receiver does not delete the
raw profile, and a retained raw profile does not reactivate the receiver.

No source-valid executions, full profile uniqueness, complete context
admission, dynamic capture receipt, production containment, principality or
finite effective solver presentation are claimed. P's inventory might be
exactly `{p_0}`; this result does not refute that possibility. The bounded
negative result fails if a relevant source-profile constructor outside the
named inventory is supplied, or if `TypedCallCert_Dec` is separately proved
to be source generated from these inputs. Such a proof must be exhibited.

## 6. Checks, independence and frozen dependencies

This is a manual rule-inversion derivation, not an executable search or a
checker of assumed transition rules. There is no Oracle/reference executable,
no random seed, no enumerated range and no mutation run. The pair shares the
typed-boundary transport axioms on both legs, so it is conditional evidence
about those axioms; it independently distinguishes the input evidence
origin, not source-semantics validity. Conceptual shortcut mutations tested
by the derivation are identifying initial slots with complete slots, copying
`call.effect` to a latent result, and identifying inherited evidence with a
new original contribution.

Checks run: narrow governing-section reads; `git rev-parse HEAD`; `sha256sum`
on the seven dependencies below; `git diff b0dd026bb9438b7dfb13c68a474a49145eb97555 --`
those exact paths (empty); and an absence check on the leased output before
creation. No build, test, probe, formatter, Git mutation, child delegation or
shared-file edit was performed. Local command execution was sequential or
parallel read-only work; heavyweight process count was zero. CPU/RAM peaks
and total wall time were not instrumented. No numeric compute budget was
supplied beyond the prohibition on tests/builds/Oracle.

| Dependency | SHA-256 at submission |
| --- | --- |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/progress/2026-10-06-main-source-generation-minimal-clause.md` | `495aceda697cef317f27be0375423246d9b2c7a341ea81a2bbf8df6e28910b4e` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |

Recommended next action: supply a source-applicable P constructor that
explicitly classifies original dependent positions/contributions and gives
the same-root seed-to-refined full-view map. Test its inverse on the exact
singleton before attempting another decorated transition probe.

## Commit packet

- Exact lease/change: `notes/progress/2026-10-06-profile-P-completeness-falsification.md`.
- Baseline: `b0dd026bb9438b7dfb13c68a474a49145eb97555`.
- Changed dependency hashes: none at the recorded comparison; pinned hashes
  are listed above. The primary must recheck them before integration.
- Review status: frozen, unreviewed research submission; no independent
  certification, theorem closure or production authority claimed.
- Checks already run: governing-section reads, HEAD resolution, dependency
  SHA-256/diff comparison and output-path absence check; no runtime checks.
- Proposed commit message: `research: isolate exact-candidate profile completion premise`.
- Shared-record deltas left to primary/curator: record the restricted P
  inversion obstruction and the inherited-evidence discriminator; retain P
  as open. Do not record source underdetermination, an extra original latent
  slot, or a need to reconsider the approved singleton role/protection meaning.
