# Attachment coverage: bounded adversarial attempt at the original source boundary

Date: 2026-10-07
Baseline: `2f337bf640c5b9165d941d6c879c0764ca0fabfe`
Branch: `research/simple-sub-intrusion`
Status: frozen, independently spec-audited research-only bounded negative result; no findings
Method: source/core premise audit of execution-dependent coverage, with a conditional witness reduction
Exclusive lease: this note only
Semantic and implementation authority: none
Review: `spec_auditor` PASS on content SHA-256 `418263dff4595c1317d95ee59ff321fb37e62513fb69930d7d6b6c43454ee1f4`; scope is the bounded source-realized attack, same-X quantifiers, and authority/semantic boundaries

## Objective and result

Attack original attachment coverage for exactly
`my apply f = { my step x = f x; step }`, using one original X and
`xi=(nu,K,D)`. The requested falsifier is an independently licensed original
incidence with no matching source attachment. No source-realized whole-row
counterexample, admitted pair, or independent original licensing derivation
was constructed.

The bounded result has two parts. First, an incidence already attached to e0
cannot itself falsify the existential inverse; a typed association alone does
not establish attachment or licensing. Second, the attempted hole obtained
by removing an exposure when its execution is absent is blocked by the exact
source/core premises: closure return is inert, while the retained source body
contains the original Call and its static upper-use demand. Failure to reach,
finish, or outwardly expose that invocation does not erase that source record.

These results do **not** show that every licensed incidence originates there.
The missing original licensing last rule prevents that conclusion. This lane
does not repeat endpoint-key selection, proof-copy multiplicity, inherited
retagging, external-step-carrier substitution, or Option 2 unanchored extras;
those prior failed attacks are retained as boundaries.

## Governing clauses, dependencies and hypotheses

The primary selected the language meaning. This note uses it without opening
another semantic choice:

- [FVIEW](../design/2026-10-05-inferred-function-call-views.md) §1.1 separates
  written annotations, public schemes and internal views. §2 requires source
  declarations/definitions/uses to form one shared contract; static identity,
  annotation presence and lexical scope survive transport; Q cannot create
  relations or admission. §§3–4 supply the selected formal seed/refinement and
  scoped permission. §5 explicitly leaves detailed formation, principality,
  source adequacy and production conformance open.
- [Directional addendum](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
  §2 records the binding user decision: protect the original upper output,
  with no provider-lower backflow. §3's notation requires the protected
  variable and original source upper exposure, independently of Q or solved
  membership; it does not recursively introduce latent descendants. §4 keeps
  original occurrence identities, static slots, membership, receipt and
  dynamic boundaries distinct. The direct user decision governs; the detailed
  formalization retains its Draft status.
- [Exact nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
  §2 fixes sequential local binding, inert return of step, and capture of the
  same outer f. §3 grants no meaning to other brace forms and no call-view
  registration rule.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §2.2 keeps independent descriptor, membership, admission and provider
  predicates jointly active. §3.1 supplies a *decorated* source envelope;
  §3.2 retains Lambda body/capture roots and the complete Call operands;
  §3.3 separates initial and future-use admission and includes finite prefixes
  without requiring return. §§3.4–3.5 preserve original scope and make
  realization conditional on the certificates. §6.1 is a proposed conservative
  allowance interpretation retaining the non-coverage kernel; its Bind clause
  covers an unreached suffix and its returned-provider clause retains latent
  paths without executing them. It is not an original licensing rule.
  §§8–10 leave value/capture completeness, production extras and adoption open.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §3 gives inert Closure construction and Result/Bind/Call translation; §6's
  structural rules synthesize the body interface without running it.
  [Typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md)
  §4, “Structural observation before dispatch,” separates outward support from
  a conditional observation in an entered view; §6 supplies profiles separately
  and transports tagged incidences without consuming the source evidence.

The assigned six predecessor notes were read: licensing construction,
multiplicity attack, constructor inversion, repaired Value-entry constructor,
licensing-inversion falsification, and mapping attack. The packet's
`2026-10-06-attach-law-mapping-attack.md` is absent; the existing input is
[attach-law-mapping-adversarial](2026-10-06-attach-law-mapping-adversarial.md).
Additional direct inputs are [Call generation](2026-10-06-source-call-generation-construction.md)
§§3,4.2,5 and [original contribution typing](2026-10-06-attach-law-construction-attempt.md),
“Backward derivation and the first missing judgment.” These are reviewed
bounded research, not authoritative completed source rules. Current task and
design index were used as locators only.

Fix the approved resolved core term:

```text
C = lambda(f,
      bind(step,
        result(lambda(x, call(result(name f), result(name x)))),
        result(name step)))
```

H consists of this correspondence and original binder tree, ordinary symbolic
core constructor meanings, and the reviewed seed-at-exposure premises.
Reuse their bounded result `E_C(beta)={e0}`, with
`e0=(k,beta,u,sigma_x,p0)` and `p0=outEff(U)`. This inventory is not a
singleton-slot theorem. X retains original xi, U, provider roots and actual
role/entry, environment, world, continuation and every retained constraint.
Witnesses remain below their original rigid binders.

Complete validity, successful Q, initial/history admission, slot completeness,
OriginalAssocType, Attach_C and Lic_C are **not** added to H. When operational
phases are mentioned, their independently typed decorated kernel is an
explicit conditional input, not an admitted source provider invented here.

## Conditional reduction: what an attached Call can falsify

Keep the sorts separate:

```text
e0              static original upper introduction
t=(beta,s,p,c)  original tagged signature incidence
j_call          complete invocation operand; not c by a cast
d               finite execution development; not a source slot
```

For the candidate generator and independently interpreted licensing predicate:

```text
G_C(X,t) := exists e in E_C(beta). Attach_C(X,e,t)
A_invert(X): forall t. Lic_C(X,t) => G_C(X,t)
```

**Conditional logical lemma.** Under H, any independently established
`Attach_C(X,e0,t0)` establishes G_C(X,t0), regardless of whether Lic_C(X,t0)
holds. Proof: use e0 as the existential witness. Thus t0 cannot satisfy
`Lic_C(X,t0) and not G_C(X,t0)`. If it is unlicensed, that instead attacks
A_sound.

The weaker premise
`OriginalAssocType_X(beta,p0,j_call;s0,c0)` alone does not prove Attach_C:
the predecessor's Attach-Call rule is still a candidate. No implication from
that typing premise to Lic_C is supplied either. Keeping these distinctions
prevents treating an original association as an inverse counterexample.

A counterexample that *also* has the known positive attachment needs another
fully tagged incidence t1:

```text
same X:
  Attach_C(X,e0,t0)
  Lic_C(X,t1)
  not Attach_C(X,e0,t1)
```

Necessarily t1 differs from t0 as a complete incidence record; otherwise the
positive and negative attachment premises contradict. This is a witness
reduction, not a construction of t1. One-to-many attachment remains allowed:
the mere existence of a second incidence is insufficient. No cardinality,
different-slot, or different-endpoint shortcut establishes nonattachment.

For the alternative with no supplied positive attachment, the exact residual
is already minimal:

```text
one X, one independently source-typed t:
  Lic_C(X,t)
  not Attach_C(X,e0,t)
```

To call either an admitted-language witness additionally requires independent
CompleteOriginalRow(X) and initial/history admission on that same X. No
separate row is completed for t, a phase, or a port. None is produced here.

## Attempted coverage hole: remove the unexecuted original body exposure

The discriminating method is to trace the approved source constructors before
asking what a development executes.

```text
resolved outer f capture + x binding + source Call(f,x)
    => Gen-Call-0 original U, p0 and ElimOrigin
seed-at-exposure + original SourceUpperUse(u,A_f,U,sigma_x)
    => original e0

outer execution:
  Result(Lambda x . Call(f,x))
    => return inert step closure with that body and capture
  Bind step ... Result(Name step)
    => return the same closure value, without Call(f,x) execution
```

The first tree is source generation; the second is the conditional ordinary
core execution. They share source identity and X. Nested §2 explicitly
requires the second behavior, while FVIEW §2 and Call-generation §4.2 retain
the first static schema. Therefore erasing e0 because the outer execution
returns before the body runs changes the fixed source-generation premises.
This is a blocked attack on **absence of a static exposure**, not a proof of
a licensed contribution, complete profile, or initial admission.

The bounded phase audit is:

| Proposed erasure | Exact source/core discriminator | Outcome |
| --- | --- | --- |
| step is returned without invoking its body | Nested §2 plus typed-core §3 retain the body and capture in the inert closure; Gen-Call-0 is static | No absence of e0 follows |
| A finite development stops before the inner Call, or that invocation does not complete | Source-contracts §3.3 separates prefix/future-use admission from return; source emission remains at the recorded graph | No absence of e0 follows; no actual admitted prefix is claimed |
| No outward event survives a supplied complete invocation | Typed-boundary §4 distinguishes pre-dispatch observation from outward support; even an entered view's absence of events does not erase its source Call | No absence of e0 or negative Attach_C follows |

These cover three proposed deletion criteria on this one retained source
Call, not all source executions or licensing rules. In particular, the inner
argument is `J_x=ReturnImage(Name(d_x),original environment)`; replacing it
with an arbitrary pure divergent carrier would discard Call-generation §3's
exact original operand. This note makes no such replacement and adds no
external caller/provider graph. Actual receiver activation remains distinct
from beta and e0; the proof does not identify them.

The strongest supported negative statement is therefore precise: under H,
the listed execution-based deletions cannot demonstrate absence of the
original static exposure. They may show absence of an activation, completed
return or outward event. Those have different witness sorts.

This does not settle a licensed incidence whose source formation is not
Dir-Protect. Source-contracts §3.2 enumerates execution/root clauses, not every
original Lic_C last rule. The fact that the graph has one Call does not prove
that all own-beta signature entries factor through it. Nor does the directional
decision identify Lic_C with NewProtection. Neither a latent extra entry nor a
new membership predicate is fabricated to fill that gap.

## Blocker, limits and next action

The required discriminating input is an independently interpreted original
licensing rule with a real source derivation of t, plus its original
slot/contribution association on X. No inspected clause supplies that
conclusion. Without it, a negative Attach_C atom would be an arbitrary relation
assignment rather than a source/core counterexample. An affirmative attachment
also needs the candidate Attach-Call source law beyond OriginalAssocType.

The finite search was a manual premise audit of one source term, its one reused
static exposure, the positive-attachment witness reduction and three
execution-based erasures. It produced no same-X pair. Seeds/ranges, random or
exhaustive executable enumeration, and runtime mutation counts are inapplicable.
No incomplete program enumeration is represented as complete. After the
attachment premise remained untouched in the association-only and phase-erasure
routes, this lane stopped rather than constructing another assumed-rule probe.

Named logical mutations and failure conditions: identify static exposure with
dynamic activation; require a return or outward event to retain a source record;
infer Lic_C from OriginalAssocType or NewProtection; declare one Call to be the
only licensing rule; replace the exact Name operand; or choose separate X/xi
for the positive attachment and alleged missing incidence. The first two
discard explicit source premises; the remaining four add unproved premises or
change the original tuple. These are audited mutations, not executed tests.

Established inputs remain the selected exact structure and reviewed bounded
static introduction. New claims are the conditional witness reduction and
bounded rejection of the listed deletion arguments. Original association,
both licensing directions, exhaustive profile formation, complete-row
nonemptiness, independent admission, generalization/recursion, principality,
source adequacy and production conformance remain unverified. There is no
source impossibility result or evidence of a new language decision.

Recommended next action: make the original licensing constructor expose its
source derivation and original `(s,p,c)` association, then test whether a
genuine own-beta last rule yields t without attachment on the same X. Another
execution-consistency or arbitrary-incidence-table checker cannot supply it.

## Commands, independence and resources

Only the leased note was written. Commands were bounded cat/sed/rg reads,
read-only git revision/branch/status, and Python SHA-256 plus
`git show 2f337bf640c5b9165d941d6c879c0764ca0fabfe:<path>` byte comparisons.
Seventeen direct dependencies matched the pin. Initial aggregate captures
truncated; decisive governing/constructor windows were recovered separately.
No repository-wide absence claim depends on truncated output.

No Oracle code/output/execution, Cargo, compiler edit, test, checker,
formatter, Git mutation, child delegation or scratch output. Oracle
independence is complete. The logical lemma shares H and the predecessor's
independently interpreted predicate discipline; it neither validates those
source rules nor counts as independent review. A checker coding the same
transition premises would only establish conditional consistency.

Resource budget supplied: one note and no Oracle/Cargo execution; no numeric
CPU/RAM/wall ceiling was given. Consumption: one output path, zero heavyweight
processes, short read/hash processes; largest initial read batch had five
processes. Aggregate CPU, peak RSS and elapsed wall time were not instrumented.
Frozen direct-input hashes follow; snapshot equality is evidence about bytes,
not proof certification.

## Frozen dependency snapshot

All paths matched the pinned blobs; this worker changed no dependency.

| Path | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/progress/2026-10-06-original-signature-licensing-construction.md` | `f5032a91781706551dcd01474f6024eb34fcb0cb110fa6157f7ec577ccfc5cff` |
| `notes/progress/2026-10-06-original-signature-licensing-adversarial-next.md` | `76ccf31fba662d637e57600933ba12bb5f75d31b4f460d778ea8bb510363cd29` |
| `notes/progress/2026-10-06-original-signature-constructor-derivation.md` | `5dc90af8e6c789487ed3f0cb82ba254ce7a99648350f7dbce0e0f000184f8f19` |
| `notes/progress/2026-10-06-original-signature-attachment-constructor-attempt.md` | `8341debee8da5e0d0357190ff1085e21427726182c8a9fce33838f1707706462` |
| `notes/progress/2026-10-06-attach-c-licensing-inversion-falsification.md` | `dc3695cb38989c8e95eff52cb90a09bd6c85d0c2684f0c973bca970a9398d326` |
| `notes/progress/2026-10-06-attach-law-mapping-adversarial.md` | `ed64f8c2e88486db608568753828d41ab48599fa43a16c06db14ddad516095ba` |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| `notes/progress/2026-10-06-attach-law-construction-attempt.md` | `b94e829e06027c2bd4cc2f0dbf4a33dc954aa10ee058fbc4918da75ad151a241` |

## Commit packet

- Exact leased/changed path:
  `notes/progress/2026-10-07-attachment-coverage-adversarial-attempt.md`.
- Baseline SHA: `2f337bf640c5b9165d941d6c879c0764ca0fabfe`.
- Changed dependency hashes: none; all seventeen direct inputs match the pin.
- Review status: spec-auditor PASS on frozen content SHA-256
  `418263dff4595c1317d95ee59ff321fb37e62513fb69930d7d6b6c43454ee1f4`;
  bounded witness reduction/unsuccessful source attack, with no semantic
  authority or gate closure.
- Checks already run: exact clause/constructor/sort and same-X audit; leased
  path absence; seventeen pinned-byte/hash comparisons; note-local integrity
  and final dependency recheck. No runtime verification.
- Proposed one-line research-checkpoint commit message:
  `research: bound execution-dependent attachment coverage attacks`.
- Shared-record deltas intentionally left for primary/curator: record that
  positive attachment cannot itself refute inversion and execution-based
  removal does not erase the retained original source exposure; retain
  OriginalAssocType, independent original licensing and exhaustive inverse,
  full profile/admission and all soundness/principality/source-adequacy gates.
  No task, theory, index, authority, question bundle or other shared file changed.

The note's technical content remains the reviewed frozen artifact. The primary
updated only the review metadata and owns shared synchronization and Git
integration.
