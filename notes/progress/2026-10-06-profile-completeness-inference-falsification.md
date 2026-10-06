# Profile completeness: policy assembly and original licensing quantifiers

Date: 2026-10-06
Baseline: `0a28c92cce9f469856b5f8776426bb6a2c53eb81`
Branch assigned: `research/simple-sub-intrusion`
Status: independently spec-audited bounded algebraic falsification; non-authoritative
Scope: exact `my apply f = { my step x = f x; step }`, original profile P
Method: quantifier audit and an injectivity derivation for source-owned policy
Exclusive write lease: this note only
Implementation authority: none

## 1. Result and boundary

The source-owned no-annotation policy determines the marks **once original
applicability is independently fixed**. Its assembly preserves, rather than
eliminates, the existence and coverage obligation on that applicability.
The derivation below makes this dependence exact. The finite source/control
witnesses and conditional SV theorem cannot be substituted for that premise.

No meaningful new source counterexample or pair of authority-consistent
complete profiles was obtained. Adding a latent position or varying an
uninterpreted applicability atom would assume the premise under investigation.
This lane therefore returns a precise proof obligation. It does not dispute
the producer's stated result: that result already leaves the obligation open.

This differs from the earlier generic last-rule obstruction and inherited
result-packet discriminator in
[P falsification](2026-10-06-profile-P-completeness-falsification.md), and from
the independent initial-context discriminator in
[admission falsification](2026-10-06-source-profile-admission-falsification.md).
Neither attack is repeated here. No initial-admission relation is mutated.

## 2. Frozen inputs and exact premises

The producer is
[source profile/admission construction](2026-10-06-source-profile-admission-construction.md)
§§3.1–4.1,6–9. Its assigned hash was
`bb29863cb679ef5b286ef8432f828a72f23efae1a466da8c2458d33a5622bcd7`.
During this assignment the primary supplied a review-metadata-only update;
the current hash is
`add4197a6e4e047db7d71d746c97b771e03ffad83be6aa75cb204c20ad350ff2`.
The primary reported the derivation body and semantic dependencies unchanged.
The new hash was checked locally. No claim of an independently verified
body diff is made.

| Governing source | Exact use and limit |
| --- | --- |
| [Inferred call views](../design/2026-10-05-inferred-function-call-views.md) §§1.1–5 | One shared source contract, original slot/scope, annotation absence and Q independence; complete generation and principality remain gates. |
| [Directional addendum](../design/2026-10-06-directional-inferred-effect-protection-addendum.md) §§2–4 | The protected-variable/original-upper premises produce one tagged output occurrence. No reverse lower protection or automatic result traversal. |
| [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md) §§2–3,6–9 | Primitive whole-tuple meanings are independent inputs. C-realization requires exhaustive accounting and local typing. Allocation covers its stated view class; Option 2 preserves independently licensed extras. |
| [Typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md) §6 | A source profile marks exactly its applicable positions. Boundary introduction consumes that profile. Indexed transport preserves source witnesses. |
| [Callback delivery](../design/2026-10-03-callback-context-delivery.md) §§2–4 | B consumes a known original profile before literal elaboration; actual provider role/entry survive adaptation. |
| [Call construction](2026-10-06-source-call-generation-construction.md) §§4–5 | Generates the designated output address and semantic checking obligations; decorated profile premises remain supplied. |
| [Joint construction](2026-10-06-directional-joint-source-judgment.md) §§3,5 | S1 generates the tagged upper delta; S2 retains it under a compliant refinement. Neither asserts complete solution existence. |
| [SV construction](2026-10-06-directional-source-view-instantiation-construction.md) §§3–6 | Constructs Pending/actual-result/capture/read evidence for independently typed original rows with one compatible complete original profile. |
| [Nested-block meaning](../design/2026-10-06-nested-block-function-source-realization-addendum.md) §§1–4 | The returned local function captures the same outer formal; its return is distinct from invoking it. |

Fix this source C, its original binder tree sigma and one original
`xi=(nu,K,D)`. Let theta contain the remaining original whole-tuple coordinates:
complete Function demand, provider/result sources, world/history and their
original dependencies. Theta never supplies an independently chosen xi per
port or per history. Quantifiers below are shorthand under the original
binder tree; none is moved outside a rigid dependency.

Let a denote a **tagged original source-owned incidence**, including its
contribution, upper occurrence and signature-position correspondence. It is
not merely an effect endpoint. Let a0 be the known
`(k,beta,u,sigma,p0)` incidence. Inherited provider/result sources are retained
separately, including an inherited occurrence of the same static beta; they
are not silently counted as a new introduction by this boundary.

Explicit hypotheses of the derivation:

1. S is an independently licensed original applicability/contribution set at
   theta, retaining these tags and sorts. Existence of such an S is not assumed
   when deriving the source emitter's result.
2. For this unannotated source-owned component, profile support is exactly S.
   On every member protection is true and the concrete grant is absent.
   Outside S this component contributes no incidence. These are the producer's
   §3.3 and typed-boundary §6 clauses.
3. Full packets retain separate inherited components; policy assembly does
   not modify their grants, lower marks or origins.
4. Complete source-profile validity, descriptor validity and original
   all-world conditions keep their independent meanings. They are not defined
   by satisfaction of the emitted known conjuncts or by erasure of SV.

Hypothesis 1 is the open premise. Hypotheses 2–4 specify the already selected
policy and interpretation discipline; they introduce no candidate semantics.

## 3. Derivation: assembly reflects its input domain

Define only the source-owned policy assembly:

```text
Pol(S)(a) = (protected=true, grant=none), if a in S
            absent,                         otherwise.
```

The support and tags are retained. Consequently

```text
support(Pol(S)) = S,
Pol(S1) = Pol(S2) iff S1 = S2.
```

Proof: if a is in S, the assembly has its indexed incidence; if it is absent,
the component contributes none. Thus support recovers S. Equality of policies
implies equality of recovered supports; the reverse implication is pointwise
equality of the fixed policy fields. This argument concerns the source-owned
component, not an untagged union of all received packets.

For any independently specified family I(theta) of compatible original
applicability sets, assembly is therefore a bijection from I(theta) onto
its policy image. In particular:

```text
exists S in I(theta)              iff exists Gamma in Pol[I(theta)],
exactly one S in I(theta)          iff exactly one Gamma in Pol[I(theta)].
```

This is a conditional algebraic result; independent review is limited to the
equation and its non-entailment boundary below.
It proves no fact about whether the actual I(theta) is empty, singleton or
larger. Additional profile/descriptor constraints can restrict I(theta);
they must be supplied independently. Assembly does not discharge them.

The tempting inference loses that dependency:

```text
forall independently licensed S. unique Gamma=Pol(S)
mandatory source member a0
finite actual source/control witnesses
---------------------------------------------------- INVALID PROMOTION
exists a compatible COMPLETE original S and Gamma=Pol(S),
with exhaustive original licensing and complete original-row validity.
```

The first premise is functionality conditional on S; it contains no witness
in I(theta). The second proves a member, not a complete set's validity. The
third gives concrete constructor/control witnesses, not membership of their
whole tuples in I(theta). Policy assembly reflects exactly the missing set;
it cannot supply its validity by changing notation from S to Gamma.

## 4. The source/control and SV quantifiers retain the cut

The producer's identity run supplies an actual returning control derivation
with the mandatory upper mark and separate empty provider profile. The loop
and request cases supply their finite Pending/resumption envelopes under
their stated independent recursive/declaration premises. All are retained.
The producer explicitly does not establish complete original-profile validity
for any of their whole tuples.

Writing Op_C(theta,h) for only that established operational envelope and
ValidOriginal_C(theta,S) for complete original source-profile validity, the
witness evidence has the form

```text
exists theta,h. Op_C(theta,h) and MandatoryDelta_C(theta,a0).
```

It does not have the stronger form

```text
exists theta,S,h.
  ValidOriginal_C(theta,S) and Op_C(theta,h).
```

This is an audit of which conjuncts were proved, not a model declaring either
conjunct false. Even one complete identity witness would establish only that
nonempty fiber; it would not prove original-profile coverage for every allowed
whole tuple or future development.

SV has a different universal conditional:

```text
forall theta,S,h.
  ValidOriginal_C(theta,S) and OriginalAdmittedHistory_C(theta,h)
  => paired receipt/result/capture/read extension for that same theta,S,h.
```

Its causal extension is substantial: it covers Pending prefixes and actual
transitions without requiring a return. But its antecedent contains the very
complete profile being sought. The reverse direction reconstructs that same
input profile. Composing operational witnesses with SV requires proof of the
antecedent on their **same** whole tuples. No completion may be chosen anew
for each resumption, executing port or horizon.

Finite templates do not repair this gap. A finite clause can quantify over a
dependent position/occurrence domain without enumerating it. Correct finite
syntax does not prove that the clause has the original exhaustive meaning.
Source-contracts §3.6 expressly excludes proving primitive contracts from its
syntactic checker cost. Its §3.5 theorem assumes exhaustive rule accounting;
using that theorem to establish the missing accounting would be circular.
Option 2 likewise prevents restricting complete membership to the displayed
source witnesses. It does not itself mint another beta-owned incidence.

## 5. Exact remaining proof obligation and failure conditions

Supply an independently interpreted original licensing judgment L_C at this
generated contract, with source declaration/seed/exposure premises, tagged
contributions, original positions and scopes. For a proposed finite generator
G_C, prove the following on the claimed original envelope:

```text
forall original theta,a.
  G_C(theta,a) => L_C(theta,a),       [no fabricated original incidence]
  L_C(theta,a) => G_C(theta,a).       [no omitted original incidence]
```

The first implication includes more than sorting or an endpoint match. The
second needs original licensing inversion, including every independently
specified formation alternative in that envelope. Neither direction requires
or permits inventing a latent slot merely from solved type shape.

Then instantiate at least one actual whole-tuple witness theta,S and verify
the complete original profile/descriptor/provider/world predicates at their
original binders. For a relation-wide source producer, prove extension and
reverse reconstruction on the independently specified original solution
relation; one nonempty example is insufficient. Keep policy assembly and SV
as subsequent conditional lemmas. No stronger coverage over all endpoint
assignments is presumed here.

The obstruction ends if an existing source Function/signature constructor
already supplies L_C together with exhaustive inversion and a compatible
whole-row witness; its actual clause and proof should then be exhibited.
It also ends if the new construction supplies those clauses. The current
report does not show that no such derivation can exist elsewhere.

Conceptual mutations audited: promote conditional uniqueness to existence;
promote operational nonemptiness to complete-profile nonemptiness; use SV
erasure to define the original profile; equate source-template accounting with
original semantic exhaustiveness. Their failures above are logical premise
failures, not executable mutation results. No new toy interpretation was
constructed after the prior attempts left source licensing untouched.

Recommended next action: expand the original Function/signature licensing
clause at beta and prove its two incidence inclusions, then discharge it on
one shared complete identity row. Return to experiments only when they can
distinguish a stated consequence of that independent clause.

## 6. Checks, independence, resources and frozen dependencies

Commands used: bounded `cat`/`sed`/`rg` reads; `sha256sum` on the dependencies
below; output-path absence check; note-local link/whitespace/hash checks.
One read-only `git rev-parse HEAD` was run and matched the assigned baseline;
this exceeded the packet's literal no-Git-operations constraint. No Git
mutation occurred, and no further Git command was used. Current branch
verification and baseline-diff verification remain with the primary.

No build, test, Oracle execution, random experiment, enumeration, executable
checker, formatter, child delegation or shared-file write was performed.
There is no oracle/reference implementation; Oracle was excluded both as
authority and as evidence. The policy lemma shares the explicit independently
fixed profile clauses with the producer; it does not independently validate
those source rules. This artifact is a producer result, not its independent
certification. Read-only commands ran in small batches; heavyweight processes:
zero. CPU/RAM peaks and elapsed wall time were not instrumented. No numeric
CPU/RAM/wall-time budget was supplied. Seeds/ranges and mutation-run counts:
not applicable. No source-semantic search was completed or claimed.

Unverified scope: complete applicability interpretation/nonemptiness, source
and admission coverage, arbitrary recursive inference, complete descriptor
and all-world validity, principality, production acceptance and containment.
No already selected language meaning is reopened.

| Dependency | SHA-256 at freeze |
| --- | --- |
| `notes/progress/2026-10-06-source-profile-admission-construction.md` | `add4197a6e4e047db7d71d746c97b771e03ffad83be6aa75cb204c20ad350ff2` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/design/2026-10-03-callback-context-delivery.md` | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| `notes/progress/2026-10-06-directional-joint-source-judgment.md` | `fc459dfac03693f426dea575585a0d20d7a075f8c7ac27be9fd2e67a150466c1` |
| `notes/progress/2026-10-06-directional-source-view-instantiation-construction.md` | `462d792e518409199f77bb20a41aaa54d64898fe30363f98f0afff7ab3f805e3` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |

## Commit packet

- Exact leased/change path: `notes/progress/2026-10-06-profile-completeness-inference-falsification.md`.
- Baseline SHA: `0a28c92cce9f469856b5f8776426bb6a2c53eb81`.
- Changed dependency hash: producer `bb29863cb679ef5b286ef8432f828a72f23efae1a466da8c2458d33a5622bcd7` to `add4197a6e4e047db7d71d746c97b771e03ffad83be6aa75cb204c20ad350ff2`, primary-reported review metadata only. Other recorded semantic hashes match the producer's frozen dependency table.
- Review status: frozen and independently spec-audited; no theorem closure, source counterexample, or implementation authority.
- Checks already run: narrow governing-section and anti-duplication reads, dependency hashes, path absence, note-local links/whitespace and final hash. No runtime verification.
- Proposed commit message: `research: isolate original profile licensing quantifiers`.
- Shared-record deltas intentionally left to primary/curator: record that unique source-owned policy assembly reflects applicability existence/coverage; keep original licensing and complete-row nonemptiness open. Record no additional slot, source rejection, competing semantics or new user decision. Shared task/index/theory/authority files remain untouched.

## Independent review

A spec auditor reviewed the frozen artifact and governing clauses; no
blocking, major or minor finding remained. The reviewer confirms that the
policy equation transfers only conditional uniqueness over an independently
supplied applicability family. It proves neither applicability existence or
coverage nor complete-row nonemptiness, and supplies no source counterexample
or alternate semantics. Original licensing inversion, all-view principality
and production conformance remain open.
