# Whole-relation principal factorization: the source-to-query proof cut

Date: 2026-10-07
Status: frozen unreviewed research attempt; conditional composition and bounded proof-cut characterization
Baseline: `035f7f8e97f5544ccd028bd1f167b83054134fdc`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this note only
Implementation authority: none

## Objective and outcome

Attempt a direct derivation of DAG `PRINCIPAL` from the closed transport and
ordinary-use results, preserving the whole source relation and the actual
designated common export. The attempt reaches the existing ordinary-use
extension theorem and stops before its missing source-to-query implication.
No unrestricted principal theorem, source counterexample or new independent
gate is established.

The precise proof cut has two parts that a global adequacy hypothesis must
not conceal: independently valid views need suitable complete checking
derivations, and those derivations need evidence accepted by the query at the
actual common export. The source-allocation result supplies both only in its
stated matched-kernel class. These are proof obligations inside `ALL_VIEW`,
not additional opaque completion hypotheses or a proposed replacement meaning.

## Baseline, authority and exact dependencies

The governing DAG sections are `PRINCIPAL`, `SOURCE-ADEQUACY`, `ALL-VIEW` and
`PROJECTION` in [the canonical ledger](../theory/successor-proof-obligations.md).
The ledger is routing, not semantic authority. The proof attempt uses:

- [Charter](../design/2026-09-29-scc-intrusion-redesign-charter.md) §§2–4,
  8–12: the selected conservative abstraction, full supported envelope,
  soundness/principality, and honest finite-presentation classification.
  Its selected typed transport and role amendments remain binding.
- [Certified uses](../design/2026-10-04-certified-callback-and-constrained-use.md)
  §§2–3 and 5–6: complete certified transport, whole fresh-copy/graft/query
  syntax, exact projection iff scoped extension, and actual-root distinction.
- [Global synthesis](2026-10-07-successor-global-synthesis.md) §§2–3:
  one original joint `J_S` and its original binder tree. Its open all-view
  sequent is the starting boundary, not the result of this attempt.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§1, 3.7, 5.3, 6.1–6.3, 7 and 10: conditional active formation and finite
  comparison certificates; exact `V_alloc`/`V_alloc,H` scope and exclusions.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §§7 and 9: complete checking/domain containment is a semantic proposition,
  distinct from effective complete query evidence.
- [Safe preimages](../design/2026-10-04-common-allowance-context-preimage.md)
  §3.2 and §6.1: an independent containment-validity criterion and the missing
  complete-query representation theorem.
- [Residual factorization](../design/2026-10-03-open-residual-factorization.md)
  §§2–5 and [scoped equality](../design/2026-10-03-scoped-constraint-solving.md)
  §§1–2, 5: exact joint rewriting with retained `Phi`, original endpoints,
  permissions and evidence, not all-view query completeness.

The accepted principal criteria in
[the scheme record](2026-10-04-principal-scheme-acceptance-criteria.md),
“Common-allowance factorization gate,” are retained. Option A, Option 2 and
the committed inlet-context answer preserve independent endpoint/admission
meaning, production extras without compulsory source-constructor witnesses,
and all independently typed compatible punctured contexts at original
`xi=(nu,K,D)`. None supplies exhaustive concrete rules or implementation
authority. This attempt does not use Oracle semantics or reinterpret roles,
entry, protection, common allowances or the designated root.

## Exact quantified objective and hypotheses

Fix an admitted source component `S`, its imports, original scopes and binder
tree `T`. Let `P_S` be the computed legal constrained presentation if the
pending production/projection construction supplies it. Its designated root
is the actual `B_common`, including its resolver/evidence alternatives.

The intended public class is **every independently valid finite public scheme
in the declared conservative abstraction and supported source envelope**.
Call that class `V_ind(S)` as notation only; it is not defined by being an
instance of `P_S`. It includes any separately licensed checking/adaptation
forms in that envelope. `V_alloc,H(S)` is a conditional subcase, not a
replacement for this quantifier. Infinite unfolding with a finite graph is
included when that graph has been independently justified. This note proves
no presentation theorem for other cases.

The target is one finite ordinary-use graph per view:

```text
forall V in V_ind(S). exists finite m_(S,V).
  forall original xi and public assignment v.
    C_V(v;xi) implies Scoped_T(
      J_S and K_G and Q_common and
      Direct(B_common, R_V(v); actual evidence)).
```

`Scoped_T` abbreviates satisfaction using the existing quantifier tree,
including its permitted witness dependencies; it is not an existential
prenex block. Original universal worlds, challenges and finite-history
closure remain in admission and membership. The finite graph is fixed for
`S,V`; solutions/strategies can vary with `v,xi` only at their original
positions. Neither a new graph per challenge nor a global ground substitution
chosen before every view is allowed.

The following are **candidate sufficient hypotheses**, not newly established
source facts:

1. **Independent checking inversion.** Each `C_V(v;xi)` in this class supplies
   a complete independent source/interface checking derivation `d` with a
   compatible original source witness/strategy. Its generation inversion
   supplies `J_S` and the legal graft at `T`, with the same providers,
   occurrences, scopes, imports and joint dependencies. If validity is given
   extensionally by safe containment, deriving such a finite certificate is
   itself required; it cannot be assumed from a finite written predicate.
2. **Export checking elaboration.** From this *same derivation and witness*,
   construct a compatible legal common-formation witness and a finite accepted
   proof of `Direct(B_common,R_V)`. Every source/descriptor/checking rule used
   by `d` needs a corresponding evidence introduction case. The proof must
   cover every actual membership/admission alternative, including Option 2
   extras, and quantify over the complete admitted domain. A rule need not
   invert each extra observation to source syntax.
3. **Certified computed representation.** `P_S` preserves the complete joint
   source/common relation, the query operands, their incidence and the
   corresponding direct evidence under the allowed scoped transport. It is
   a legal finite exported representation and admits the ordinary-use graph.
   Bare equality of an endpoint marginal is insufficient for this hypothesis.

Hypothesis 1 is the view-specific inversion seam of source adequacy;
hypothesis 2 is the source/checking-to-actual-query seam of `ALL_VIEW`;
hypothesis 3 belongs to the declared `PROJECTION`/generalization contract.
They are not silently inferred from the DAG dependency arrows.

## Conditional derivation and stopping point

Assume all three hypotheses. Construct `m_(S,V)` once by whole fresh-copy,
an admissible finite graft if required, retained `C_V`, and one complete
query at `P_S`'s designated export. Certified-use §5.1 supplies this graph.

For arbitrary `v,xi` satisfying `C_V`, hypothesis 1 provides the original
scoped source witness and independent checking derivation. Hypothesis 2
extends that witness with common formation and evidence for the actual
export query. Hypothesis 3 transports the *joined tuple and that evidence*
to the computed graph. Each binder is interpreted at its original position;
one shared identity has one assignment throughout. Thus the scoped extension
of this use exists for every public solution. Certified-use Theorem 3 gives
exact public projection: the use loses no `C_V` solution and, because it
retains `C_V` conjunctively, adds none.

This is conditional composition of already reviewed operations. It does not
invoke transitivity of concrete successes. No inference is made from
`R_source <: B_common` and `R_source <: R_V` to `B_common <: R_V`.
No hidden original export substitutes for `B_common`.

**The derivation stops at hypothesis 2, with hypothesis 1 also unestablished
for the full class.** The exact unavailable rule is an admissible
source/interface-checking-to-ordinary-query introduction theorem at the
actual common root, uniformly over the independently valid views. The closed
certified transports can carry a supplied query proof; they cannot create
one. Equality quotienting and exact residual rewriting preserve predicates
already present; they do not derive the pending query's evidence.

Source contracts §5.3 exposes the missing proof rule concretely. Its sole
displayed parent `Function` introduction requires matching actual
role/entry/consumer and non-coverage interface, a finite proof of
`Eq(D_common,D_V)`, and a finite proof of `Le(M_common,M_V)` under one map.
Its `Eq-C`/`Le-C` cases require matching ordered operands and primitive
relations. Arbitrary valid changes to value interfaces, domains, adaptations
or complete root predicates have no supplied introduction case in this
calculus. The note explicitly calls accepting even that local rule a
resolution-conformance hypothesis.

Typed-core §9 supplies the weaker semantic premises
`D_V subset D_common` and complete observation containment on `D_V`.
It explicitly does not supply an effective general subtype algorithm.
Safe-preimage §3.2 proves that particular independent semantic validity law;
§6.1 separately asks for its complete-query evidence representation. Taking
these propositions as already accepted evidence would assume the missing
rule this attempt was assigned to derive.

This identifies an internal proof cut, not a new independent theorem or a
semantic weakening. A second whole-relation rewriting attempt would reach
the same cut. The lane therefore stops here.

## Falsifier, existing witness and exclusions

A falsifier of hypothesis 2 would be one independently licensed finite view
with a complete original source checking witness whose direct query at the
actual common export has no accepted evidence alternative. It must establish
the complete source/admission premise first. Failure of the restricted local
certificate alone is not such a falsifier, because another resolver case may
apply. No such source witness is produced here.

The [existing proper-domain separation](2026-10-06-principality-proper-domain-view-boundary.md)
already distinguishes semantic domain inclusion from the allocation
certificate's equality requirement; its
[source-licensing audit](2026-10-06-principality-record-domain-source-license.md)
keeps the Record premise conditional. This attempt neither repeats that
countermodel nor treats it as an accepted-source failure. It is sufficient
evidence against identifying the two proof obligations without their missing
license/evidence theorem.

The conditional composition fails if a transformation removes a queried
dependency, changes a rigid import, rebinds an old witness, exchanges
quantifiers, selects different providers in different factors, loses an
Option 2 alternative, substitutes a hidden root, or supplies only semantic
containment where actual query evidence is required. It establishes nothing
about omitted source forms, mutable state, arbitrary adapters, resolver
termination or effective projection. Failure of a sufficient premise does
not authorize rejecting the source/view.

## Evidence, resource use and freeze

Method: manual derivation and narrow pinned-source comparison, with no
executable semantics experiment. Source authority is independent of solver
output and query success. The conditional derivation shares its explicitly
listed presentation, certificate and binder laws with the imported theorems;
it is not an independent oracle validating their source premises.

Commands: bounded `cat`, `rg`, `sed` reads; read-only `git rev-parse` and
`git status`; Python SHA-256 comparison using `git show BASE:path` versus live
bytes; leased-note whitespace inspection. Initial batched outputs containing
large documents were truncated; decisive named sections were subsequently
read directly. No exhaustive repository search is claimed.

No tests, builds, formatters, checker, enumeration, mutation runs, seeds or
ranges were used. No child agents or Git mutations. Only lightweight reads
and hashing ran; zero heavyweight processes. CPU, peak RSS and total reasoning
wall time were not measured. No numerical CPU/RAM/wall-time budget was supplied
in the packet. Hashing used one Python process with sequential short `git show`
children. Dependency bytes matched the baseline; final checks are recorded
below. The producer claims no independent review. Writes stop at submission.

Recommended next action: assign an exhaustive source/interface checking rule
to actual-export query evidence derivation under the eventual complete
descriptor/admission clauses, beginning with the exact unmatched checking
cases rather than another relation-rewriting probe. Retain a separate validity
inversion obligation if the declared view class uses semantic containment
rather than independently supplied finite checking derivations.

## Dependency pins

Every dependency above is fixed by the full baseline. Salient SHA-256 pins:

```text
18bfa4e5bb461616ca17a0c9a1492f75ff7fca2f6231a13b3d68e0a3335136dc notes/theory/successor-proof-obligations.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed notes/design/2026-09-29-scc-intrusion-redesign-charter.md
887bc7c0743d2f34608b46ccb8e5ee9b58ea4a39995b93a5aaced764295bae80 notes/design/2026-10-04-certified-callback-and-constrained-use.md
b34c5b3644637bc1340f5636e0b6dc3fcc42c39de5d9cc73bcb48b84293e417e notes/progress/2026-10-07-successor-global-synthesis.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186 notes/design/2026-10-05-source-contracts-and-common-allowance.md
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e notes/design/2026-10-02-typed-computation-core-elaboration.md
e3aa657d281f8e528d41544d862ee5e938bb6d3c4d36fa60fd04306c1f1dfb7e notes/design/2026-10-04-common-allowance-context-preimage.md
```

## Commit packet

- Exact leased path: `notes/progress/2026-10-07-principal-whole-relation-factorization-attempt.md`.
- Baseline SHA: `035f7f8e97f5544ccd028bd1f167b83054134fdc`.
- Changed dependency hashes: none at final check; source/rule/answer dependencies
  matched pinned bytes. Unrelated branch advancement is not semantic input.
- Claim/review status: unreviewed conditional composition and bounded proof-cut
  characterization; frozen research-only attempt. No universal theorem closure
  or independent certification.
- Checks already run: exact source-section reads, baseline/live hash comparison,
  final dependency comparison, leased-file whitespace/scope check. No tests/builds/probes.
- Proposed message: `research: isolate principal source-to-query evidence cut`.
- Shared-record deltas intentionally left for primary/curator: optionally
  annotate `ALL_VIEW` with the independent-validity inversion and actual-export
  checking-evidence cuts. Keep `PRINCIPAL`, `SOURCE_ADEQUACY`, `ALL_VIEW` and
  `PROJECTION` open. Add no duplicate opaque completion gate and promote no
  local certificate to universal completeness. No shared task/index/theory,
  authority, question, compiler or other worker path was modified.
