# Attach law mapping: lookup keys versus original contribution coordinates

Date: 2026-10-06
Baseline supplied by primary: `1868c9bee71cf6759b7d85542ab7374d1078ab7d`
Status: frozen, spec-audited research-only adversarial derivation; no findings in scope
Method: conditional lookup equivalence and attack on its missing semantic premise
Exclusive lease: this note only
Semantic and implementation authority: none

## Objective and result

Examine proposed associations from the already constructed complete Call
operand to the original `Attach_C` incidence `(beta,s,p,c)`. The candidates
are callee-use identity, source Apply identity, mandatory address `p0`, pending
rows and complete output. Retain exactly the selected source
`my apply f = { my step x = f x; step }` and one original `xi=(nu,K,D)`.

The new result separates **selection of the known operand** from
**interpretation of its original contribution and slot**. On this singleton,
several keys can select the same source record. Changing among those keys
alone cannot distinguish attachment laws. None of those successful lookups
supplies the missing original `(s,c)` association. Conversely, a proposal to
use one key is not inherently contradicted merely because the key itself has
a different sort from a contribution: it could index an independently typed
relation. Direct casts and licensing conclusions need separate premises.

No pair of complete Authority-consistent alternatives or admitted semantic
counterexample was constructed. This is a bounded conditional derivation and
a precise blocker, not a nonexistence or language-underspecification theorem.
The prior slot-scope attack's external-step-carrier discriminator is not
repeated here; its failed complete-pair construction remains a retained input.

## Governing sources and explicit hypotheses

Read directly:

- [FVIEW](../design/2026-10-05-inferred-function-call-views.md) §§1–5:
  source/public/internal layers, shared original scope, stable slots,
  Q-independent formation and the still-open contribution rules.
- [Directional protection](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
  §§2–4: the protected variable's upper output receives protection; provider
  lower occurrences retain separate provenance. Equal endpoints do not merge
  occurrences or create membership, grants or receipt.
- [Nested source meaning](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
  §§1–3: sequential binding, inert return of step, same captured outer f.
- [Reviewed Attach-Call construction](2026-10-06-attach-call-contribution-construction.md)
  §§3–6: the complete source-rooted operand; candidate table premise;
  unproved `(s,c)` interpretation and both licensing directions.
- [Licensing construction](2026-10-06-original-signature-licensing-construction.md),
  “Explicit hypotheses and sorts,” “Conditional constructor and both coverage
  directions,” and “First unclosed leaf”: independent Attach/Lic judgments,
  possible one-to-many incidence, and conditional soundness/inversion.
- [Source-call construction](2026-10-06-source-call-generation-construction.md)
  §§3–5 and §7 P: Name roots, Gen-Call-0, supplied decorated inputs and the
  distinction between seed inventory and complete original profile.
- [Original constructor derivation](2026-10-06-original-signature-constructor-derivation.md),
  “Partial construction” and “Leaf-retention derivation”: original table
  input persists through ordinary constructors.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §6 structural rules and §7 Function contracts; [typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md)
  §6 introduction/transport; [source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2.1–2.2, §3.1, §6.1: conditional complete execution, independent kernels,
  supplied profiles and coverage distinct from contribution licensing.

H is the reviewed source-prefix envelope: resolved approved component and
original binder tree; ordinary symbolic Name/Result/Lambda/Bind/Call rules;
the selected seed and its same-root exposure; canonical generated labels.
Fix one candidate whole row X with the original xi, provider/actual role and
entry, environment, world, continuation and retained obligations. X need not
be admitted, a complete original solution, or satisfiable. Every witness
stays below its original rigid dependencies. Interpretation of execution
still assumes the independently specified decorated kernels.

Reused conclusions under H are the sole direct exposure `e0`, mandatory
`p0=outEff(U)`, its ElimOrigin and the generated complete invocation record r:

```text
beta=(d_f,R)
e0=(k,beta,u,sigma_x,p0)
r includes (a_src,u,beta,R,U,p0,p_out(a_src),original scope and X operands)
J_f=ReturnImage(Name(d_f),original environment)
J_x=ReturnImage(Name(d_x),original environment)
j_call[X]=J_f >>= (lambda actual_f.
    ExecuteCallable_X(actual_f,Delay(J_x);U,e))
```

Here `a_src` is the source Apply, `u` its upper/callee use and `c` the
original contribution coordinate. Those sorts are distinct. The checking
coordinate e in j_call is not protection witness e0. r retains entry, body,
designated consumer, return and suspended suffix; the preceding construction
is reused, not offered as independent source validation by this note.

## Candidate mapping audit

The table addresses the exact singleton; it does not assert a general
injectivity law, singleton complete Slots, or singleton licensed support.

| Candidate | Supported operand association | First missing premise / unsupported strengthening |
| --- | --- | --- |
| Callee use u | Resolved direct callee use and generated ElimOrigin select this source Call record in C. | An independently typed relation from that occurrence's complete invocation to original s,c. Setting c=u is a sort interpretation, not a consequence of name resolution. |
| Apply a_src | Its retained callee/argument and rooted Call image select r. | Original signature licensing at this source occurrence. c=a_src or one Apply implies one incidence is unproved; attachment may be one-to-many. |
| p0 | It designates the complete immediate invocation effect position; the known singleton incidence can recover r relative to C. | An original static slot association s with p0 and contribution typing. p0 is not proved to be the slot sort, and c=p0 is not proved to denote the complete contribution. |
| Pending rows P | The reviewed structural audit preserves ordered rows and exact Apply joins. They locate retained obligations. | An interpreter that establishes original typed contribution/signature entries. The pending category names do not discharge the obligations they record. |
| Complete output | If this means rooted j_call, it is the constructed complete invocation operand. | A contribution-sort interpretation/typing lemma and source table introduction. If it means Comp(E_c,A_c) or outward support, it is a projection/bound and does not replace j_call's original dependencies. |

The pending-row assertion reuses only the bounded
[current seam audit](2026-10-06-current-attach-contribution-seam-audit.md),
“Exact new route”: PendingCall's whole borrowed table is valid for its
validated singleton, whereas RawCall groups by exact Apply. This note makes
no fresh all-repository claim that there can be no other consumer.

Contradictions apply to named strengthened hypotheses, not bare index choice:
using successful Q to produce any relation violates FVIEW §2; endpoint-only
identification erases the selected original upper/lower distinction;
equating p0 with result.latent.effect contradicts Gen-Call-0's designated
position; treating a profile transport rule as fresh source introduction
reverses its supplied-input direction. An association retaining typed
source indices avoids those particular contradictions, but remains unproved.

## Conditional selector equivalence and the exact residual

For key i, suppose `Recover_i(C,X,key_i)=r` recovers the same complete rooted
record, not a printed shape or independently completed row. For u, a_src and
the known p0 this is available on the selected canonical source record.
Pending-row recovery needs its exact Apply join; it is not inferred from the
row payload alone. The rooted j_call is already an operand of r.

Let `Assoc(X,r,t)` be a separately interpreted original table association.
This is the **candidate semantic premise**, not a definition of Lic or a
proved source clause. Define only the key-indexed candidate implementation:

```text
M_i(X,e0,t) iff Assoc(X,Recover_i(C,X,key_i),t).
```

**Conditional lookup lemma.** If two recovery equations above hold on the
same C,X,r, then `M_i(X,e0,t) iff M_j(X,e0,t)` for every original tagged t.
Proof: substitute r into both candidate definitions. No choice of xi, world,
provider or per-port witness is made. The conclusion is purely about lookup
representation; it does not prove Assoc, Attach or licensing.

Thus a discriminator comparing only the five lookup spellings while giving
them the same assumed table is necessarily unable to settle the missing law.
Distinct numeric s,c labels also do not supply different meanings if one
coherent renaming preserves the table, scopes and interpretation. A real
alternative must differ in an independently interpreted incidence or its
observable consequence, not merely its labels.

The first missing premise after recovery is now precise:

```text
SourceTableIntro(C,X,e0,r,t) establishes Assoc(X,r,(beta,s,p0,c))
with original slot interpretation, complete contribution typing,
scope/dependency preservation and separate own-upper/inherited tags.
```

Even with this premise, independently interpreted licensing requires:

```text
M_i(X,e0,t) => Lic_C(X,t)               [forward soundness]
Lic_C(X,t) => M_i(X,e0,t)               [exhaustive original inverse]
```

No inspected source conclusion supplies SourceTableIntro or those
implications. This is bounded to the listed sources and proof spine. It is
not an impossibility proof for another construction. Defining Assoc to be
Lic_C, or declaring the one Call the only licensing rule, would assume the
original-source premise under attack.

## Falsifier, attempted witness and stopping boundary

Given an independently interpreted source table and a proposed M_i, the exact
falsifier is one original X and tagged t such that either:

```text
M_i(X,e0,t) and not Lic_C(X,t), or
Lic_C(X,t) and not M_i(X,e0,t).
```

A purported complete-language discriminator additionally requires both
alternatives to satisfy every retained Authority/source/descriptor premise
and complete-row/admission obligations on the same original xi. A proposed
singleton incidence can fail the inverse through a second independently
licensed t; inventing that t by filling a Boolean table is not a witness.

The smallest available fragment is the selected `f x` Call with its original
captured f, rebound x and mandatory address. It suffices to prove the lookup
lemma and locate SourceTableIntro. It supplies no semantic counterexample:
neither the positive nor negative Lic premise of the displayed falsifier is
independently established. The attempted pair therefore stops before claiming
two complete alternatives. No genuine user-decision criterion is met.

Analytical mutations, not executed experiments: drop the exact Apply join
from P and recovery is unproved; replace r by a bound and recovery loses the
complete original operand; declare a single-valued `(s,c)` map and silently
assume incidence cardinality; append extra licensed t by fiat and manufacture
the inverse's falsifier; complete a different X for each t and lose the
original whole-row theorem. These name failure conditions rather than
asserting realized Yulang runs.

No Oracle material or execution supplies any premise. The lookup derivation
shares H and the predecessor's decorated kernels; it does not independently
prove those source rules. Seeds/ranges, runtime mutation counts and numerical
search coverage are inapplicable. No executable checker or enumeration was
run; no failed or unfinished search range is concealed.

## Checks, resources and dependency snapshot

Commands used bounded `cat`, `sed -n`, `rg -n`, `sha256sum`, lease-path absence
checking and the note write. Initial `pwd` and read-only `git status --short`
were also used; the latter conflicts with the assignment's no-Git wording.
No Git mutation occurred and subsequent checks used only the filesystem.
Aggregate output captures truncated; decisive governing/Call/table sections
were reread in bounded windows. No global absence result depends on them.

No compiler edits, tests/builds, checker, Oracle, formatter, scratch artifact
or children. Output budget: one note, consumed. Zero heavyweight processes;
at most five concurrent lightweight reads. No numeric CPU/RAM/wall ceiling
was supplied. Aggregate CPU, peak RSS and elapsed wall time were unmeasured.
Baseline equality remains for the primary to check under the no-Git boundary;
the listed bytes are the frozen live dependency snapshot, with no dependency
edits by this worker.

| Direct dependency under notes/ | SHA-256 |
| --- | --- |
| `design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `progress/2026-10-06-attach-call-contribution-construction.md` | `4261105c8f9a5012a693cc39dc0f7df8c0e70024594a10282046dbaebf851a96` |
| `progress/2026-10-06-original-signature-licensing-construction.md` | `f5032a91781706551dcd01474f6024eb34fcb0cb110fa6157f7ec577ccfc5cff` |
| `progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| `progress/2026-10-06-original-signature-constructor-derivation.md` | `5dc90af8e6c789487ed3f0cb82ba254ce7a99648350f7dbce0e0f000184f8f19` |
| `progress/2026-10-06-current-attach-contribution-seam-audit.md` | `3e96fae0e04989596313c69329d063ddb4649e5c749590f6872d11f6d61b1851` |
| `progress/2026-10-06-slot-profile-scope-adversarial.md` | `4b657fe4226717d7d7cd758283dd4ccede2c2618bbe5d9b6920961768ad8d649` |

Unverified scope: original `(s,c)` interpretation/typing, table introduction,
complete inversion, full Slots/profile, complete-row existence/admission,
general multi-use/recursive formation, event protection, principality,
source adequacy and production Option A/2 conformance.

Recommended next action: derive the original table introduction and
contribution typing for r, then prove forward licensing on the same X;
another key-only or assumed-table checker leaves the precise premise untouched.

## Commit packet

- Exact leased/changed path:
  `notes/progress/2026-10-06-attach-law-mapping-adversarial.md`.
- Baseline SHA: `1868c9bee71cf6759b7d85542ab7374d1078ab7d`.
- Changed dependency hashes: none observed across this attempt; frozen live
  hashes above. Primary-owned baseline-byte equality is not claimed here.
- Review status: spec-audited bounded conditional lookup derivation and failed
  semantic-witness construction, no findings in scope; no gate closure.
- Checks already run: governing/source reads, candidate-sort/same-X audit,
  lease absence check and direct dependency hashes. No runtime verification.
- Proposed one-line research-checkpoint commit message:
  `research: distinguish attachment lookup keys from contribution licensing`.
- Shared-record deltas intentionally left for primary/curator: record the
  conditional key-recovery equivalence and exact SourceTableIntro premise;
  retain original contribution/slot interpretation, forward/inverse licensing
  and profile/admission gates. No shared record or question bundle changed.

Research writing stopped before independent review. Primary owns adjudication
and integration.
