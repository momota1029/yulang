# Round 3 aggregate attack: the source-to-actual leg is independent

Date: 2026-10-07
Baseline: `6fb5d7f697d5d592e0a39532ddb4967b54e18090`
Direct dependency snapshot: `31b97ed3b56db5a642ae9eddeebda366af74233e`
Status: independently compiler-referee/spec-auditor reviewed research-only nonimplication and rule-head extraction
Implementation authority: none; production cutover remains prohibited

## Result

No additional existing OPEN node is proposed for conditional closure. The
specific result is that PROD_CONFORMANCE's source-to-actual leg cannot be
replaced by its two displayed domain/observation containments, even when
both actual admission and actual observations are nonempty. Its three
prerequisite names do not themselves identify the original source descriptor
with the independently interpreted actual production descriptor.

This is an inference countermodel to an omitted bridge, not a Yulang source
counterexample or two competing Authority-consistent complete semantics.
Option A still requires the original complete relation and constraints;
the result identifies the correspondence needed to apply that requirement.

## 1. Exact contracts and a nonvacuous separation

The [canonical contracts](../theory/successor-proof-obligations.md) state:

- SOURCE_ADEQUACY constructs source/typed-core/observation correspondence
  at one original scoped tuple, with compatible witnesses and admission.
  Its directly reused REF_SIM explicitly does not prove Option 2 production
  completeness.
- DOMAIN_INCLUSION proves `forall xi. D_C(xi) subset D_A(xi)`.
- OBS_INCLUSION proves `forall xi,c in D_C(xi).
  P_A(c;xi) subset P_C(c;xi)` for every actual member, including extras.
- PROD_CONFORMANCE additionally requires both source and production squares
  to commute on the original tuple.

Fix the original source object `X`, scope tree and `xi=(nu,K,D)`. There is
one admitted challenge `c`; let `o0,o1` be distinct complete observations in
that same fiber. Give all witnesses the same original coordinate assignments:

| Relation | Value |
| --- | --- |
| Source/reference observation relation | `P_ref(c;X,xi)={o0}` |
| Checked complete contract | `P_C(c;X,xi)={o0,o1}` |
| Independent actual production relation | `P_A(c;X,xi)={o1}` |
| Checked and actual admission | `D_C(X,xi)=D_A(X,xi)={c}` |

Source/reference transport may be identity on `{o0}`, and source adequacy
to the checked presentation holds since `{o0} subset {o0,o1}`. Both displayed
containments hold. Nevertheless the actual production relation omits the
source observation `o0`. This failure uses neither empty domains, empty
actual observations, a changed `xi`, nor a choice of different fragment
witnesses. Repeating the same construction at every original binder valuation
preserves the universal quantifiers; no quantifier exchange repairs it.

Thus the premises establish an upper envelope for actual observations and
adequate checked admission, but do not establish that the actual relation
contains the original source base. Calling `P_A` conservative would require
proving precisely the missing extensivity fact.

## 2. The exact missing local head

After SOURCE_ADEQUACY has transported an original source observation to its
single compatible original row, the remaining head is, schematically,

```text
GeneratedSourceObservation(X,c,O,w;xi)
and IndependentAdmission(X,c;xi)
  => Scoped_original ActualMember(descriptor_X,c,O,w_A;xi).
```

Here `descriptor_X` must be the actual descriptor corresponding to that
original source object, not a fresh convenient descriptor. `w_A` must extend
or transport the same original witness on every shared coordinate, using
one scope-preserving correspondence for endpoints, roles/entries, origins,
continuations, typed paths, authority and `K,D`. The scope operator preserves
the original binder order and allowed dependencies. All required contexts,
future histories and original valuations remain universally quantified.

This is not a proposed new judgment or a sufficient assumption under which
to declare the aggregate closed. It is the exact unproved head. A useful
next proof must derive it for each actual constructor/member clause, using
child membership derivations and the original constructor witness; include
the independently interpreted descriptor conjunct rather than only the
endpoint predicates. The resulting constructor induction would establish
the lower source-to-actual leg without restricting production extras to
source-generated observations.

The direct [source contract](../design/2026-10-05-source-contracts-and-common-allowance.md)
§2.2 expressly warns that `DescMem` can discard generated witnesses without
the constructor typing lemma. Section 3.5 proves source-base correspondence
only with those local typing/conformance inputs. Section 3.7 proves
`R subset H_G(R)` from the identity arm and `R subset G`, but the complete
actual grammar and its primitive guards are unselected. This reviewed
extensivity proof supplies a genuine sufficient mechanism; neither the
[Option A](../../questions/2026-10-05-production-function-denotation/approved-answer.md)
selection nor [Option 2](../../questions/2026-10-05-production-function-bound-membership/approved-answer.md)
selects that mechanism or supplies its actual constructor correspondence.

The [global synthesis](2026-10-07-successor-global-synthesis.md) §3 already
separates the source-to-actual square from the domain square and the opposite
observation containment. This attack makes its missing lower leg explicit
and gives a nonvacuous falsifier for dropping it. No stronger production
closure is extracted from the reviewed source-base theorem.

## 3. Other aggregate cuts

SOUND cannot be obtained merely by composing an exact joint decision theorem
with semantic source/production conformance. A correct decision procedure
for a public fiber `{0}` is consistent with an unrelated publisher emitting
the universal fiber `{0,1}`. The solver theorem remains correct while the
published scheme is unsound. The actual publication/use preservation law
must connect the exported residual, hiding, evidence and accepted use back
to the same original solved relation. PROJECTION's actual ordinary-use
factorization addresses this kind of law; SOUND's current listed route
does not inherit it merely from JOINT_DEC. This is a mathematical pipeline
countermodel, not evidence of such behavior in the compiler.

IFACE_EQUIV remains an actual primitive-law obligation. A complete finite
graph and decidable alpha-isomorphism do not establish that an interpreted
predicate is equivariant. A predicate testing an interchangeable name
against an unaccounted fixed identity distinguishes isomorphic graphs.
The fixed observer must be enumerated and made rigid, or the actual
predicate's covariance/reflection law must be proved. CI_USE already
requires those laws independently; applying it does not derive them.

FRESH_LIFE additionally needs actual lifecycle premises to hold. CI_USE
proves correspondence for coherent fresh maps; REUSE assumes valid internal
roots, independent fresh substitutions, reference transport and atomic
publication. An actual incoming-use implementation that aliases the locals
of two distinct uses does not satisfy those hypotheses, even when the
conditional theorems themselves are true. A theorem about correctly mapped
uses cannot establish that the actual maps or publication barrier exist.
The [reviewed lifecycle theorem](2026-10-05-inference-lifecycle-interface-conditional.md)
§2 states these as hypotheses explicitly.

SOURCE_ADEQUACY was not relabeled: no additional full composition proof or
full countermodel to its entire prerequisite cone is claimed here. The
concurrent source/Call/world attacks own that constructive seam. PRINCIPAL's
separate reviewed conditional theorem is preserved and not duplicated.

## 4. Freeze and next action

All ten directly consumed semantic/map files were byte-compared with the
direct dependency snapshot above and matched. The only written path is
this note. Source inspection and the two finite set calculations are the
verification; zero probes, builds, tests, Git mutations or shared-map writes
were performed. No production source counterexample, theorem certification,
status promotion or semantic decision follows.

Recommended next work: derive the original source constructor's actual
`Sat_A`/descriptor membership clause at the same tuple. Retain independent
domain inclusion and all-member upper containment as separate obligations.
Adding another conditional theorem that simply assumes this missing lower
leg would not reduce the actual OPEN proof burden.

## 5. Independent review

Fresh `round3_aggregate_referee` and `round3_aggregate_spec` independently
reviewed SHA-256
`ae1f757b98f84c4b64e79105a015c3014367608ddc8242b2940c32ad28f03a48`
against the original source contracts, Option A/2 decisions, canonical
aggregate contracts and lifecycle hypotheses. Both returned PASS with no
required repair, and the primary accepted both after the panel completed.
No executable probe was needed for the displayed finite-set reasoning.

The exact new contribution is the nonempty fixed-fiber separation and full
original-descriptor rule head. The underlying source-to-actual leg was
already open in the global synthesis; it is not a newly closed or discharged
semantic obligation. The SOUND illustration concerns valid public solution
and accepted-use assignments, not a permitted Option 2 observation
overapproximation. See the [integration record](2026-10-07-successor-round3-review.md).

Subsequent direct attack: the independently reviewed
[SOUND publication synthesis](2026-10-07-sound-publication-synthesis-round3.md)
supplies §3's missing application leg using the existing **full** HIR_WIRING
contract and its PROJECTION/fresh/resource cone. SOUND's generic composition
is now CONDITIONAL-CLOSED on that strengthened sufficient route, with only
the existing HIR_WIRING edge added. This does not invalidate the narrower
countermodel above or establish any actual upstream implementation. The
source-to-actual production membership head remains OPEN.
