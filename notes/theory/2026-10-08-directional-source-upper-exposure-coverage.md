# Directional protection: bounded source upper-use coverage

Date: 2026-10-08
Baseline: `9ec4f7c290a8bd9619301a01daed9218c46d446a`
Branch: `research/simple-sub-intrusion`
Status: frozen producer research; independent review pending
Claim class: constructive bounded occurrence characterization and conditional
directional coverage; explicit missing source-constructor table
Method: syntax-constructor inversion, binder ancestry and premise audit
Write lease: this file only
Semantic/implementation authority: none

## 1. Objective and result

The current target is [directional protection §6](../design/2026-10-06-directional-inferred-effect-protection-addendum.md):
enumerate source-justified seeds **at their exposures** together with original
upper Function-use occurrences. A completed type, successful comparison or
solved graph cannot supply either premise. Existing provider/lower occurrences
remain separately indexed.

This note constructs the entire direct-Name Call inventory from a finite
ordinary core skeleton, without taking its upper-use set as an input. It
proves an exact occurrence inverse for that bounded class. Composing that
inventory with the already derived registration/capture seed premise gives
exact directional coverage for the two selected singleton source patterns.
For the larger skeleton class, directional coverage remains conditional on
source seed eligibility and applicability at each exposure. An annotation
boundary, computed callee and recursive member root each has a distinct
missing source premise; none is discharged by increasing a supplied-record
checker domain.

This is an enumeration result for original **direct upper Call demands**.
It does not identify all signature formation anchors with upper exposures.
Declared and inherited ports can have their own formation anchors, and remain
outside this inventory unless an actual direct upper Call introduces one.

## 2. Authority and established dependencies

The direct user decision in the directional addendum §§1–6 governs. Its §3
rule has exactly these premises and conclusion:

```text
ProtectedVarAt(k,v,sigma,u)
SourceUpperUse(u,v,U,sigma)
----------------------------------------- Dir-Protect
NewProtection(k,u,outEff(U))
```

The upper and lower occurrences stay distinct even if their effect endpoints
eventually denote the same value. This rule creates one upper output-effect
incidence; it supplies no provider-event protection, receipt, membership,
grant or recursive marking of latent result positions.

The exact dependencies used are:

| Source | Sections and retained result |
| --- | --- |
| [Inferred call views](../design/2026-10-05-inferred-function-call-views.md) | §§1.1–5: binder annotation provenance, shared contract/scope, no Q-generated admission, selected ordinary-formal example; generic generating judgments remain open. |
| [Nested block interpretation](../design/2026-10-06-nested-block-function-source-realization-addendum.md) | §§1–3: only the exact block candidate, same outer `f`, local `step`, final return without invocation. |
| [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md) | §§2,6: ordinary parameter registration, Name/Result, symbolic application interfaces and original result tags; raw annotation and recursive inference remain open. |
| [Original Call construction](../progress/2026-10-06-source-call-generation-construction.md) | §§3–5: original direct Name Call demand, complete-invocation output address and same original scoped constraints. Its full receipt/profile premises are not source conclusions here. |
| [Local producer](../progress/2026-10-06-directional-protection-source-generation.md) | §§2–3: exact join on already justified seed/exposure pairs, no lower backflow; §7's checker does not generate its source premises. |
| [Joint source derivation](../progress/2026-10-06-directional-joint-source-judgment.md) | §§3–4,6–7: selected registration-to-captured-exposure derivation; multi-use and general transport hypotheses; no late semantic seed replay. |
| [RS/LX supplier](../progress/2026-10-06-directional-recursive-generalization-supplier.md) | §§3,5–7: retained rule-occurrence decoration and lexical import mapping; selected completed singleton normalization; recursive discharge and semantic generalization eligibility remain separate. |

The selected seed derivation and RS/LX supplier are established within their
reviewed envelopes. This note does not rerun their proofs or certify their
larger semantic premises. The former E/R adoption question and former
certificate discriminator are not current authority or a new attack method.

## 3. Bounded honest grammar and hypotheses

Use the following **ordinary core skeleton projection**, whose constructors
already occur in typed-core §§2,6:

```text
d ::= literal | name(b) | lambda(b,c)
c ::= result(d)
    | call(result(name(b)), result(d))
    | bind(b,c,c)
```

The grammar describes finite derivation syntax, not new Yulang surface
syntax. A lambda body is traversed even when the lambda is returned inertly.
An argument lambda contributes its own body Call occurrences; it does not run
during inventory construction. Computation-role Name consumers, computed
callees, source annotations as expression boundaries, handler constructs,
opaque primitive bodies and generalized incoming uses are outside this
grammar. Ordinary admitted binder annotations may be retained as binder
metadata, but this theorem does not elaborate their annotation judgments.

Its honest hypotheses are:

```text
H1  A finite tree/forest of the displayed constructor occurrences exists.
    References point to registered binders; they do not unfold definitions.
H2  Every Name has its actual resolved binder and source ancestry. Gamma
    gives its original Value(A_b) interface and actual registration identity.
H3  Every displayed Call uses typed-core's symbolic complete Function
    demand on that callee interface, with its designated output effect.
    Complete argument/entry/receipt obligations are retained, not solved.
H4  Source occurrence, binder and scope identities survive construction.
    A capture path points to the original registration; it creates no seed.
```

H1–H4 suffice for the **upper-demand inventory**. H3 is the existing
conditional ordinary source-core Call construction, not a claim that current
production HIR builds all such demands or that arbitrary raw source has
already supplied a complete typed derivation. Source demand construction
precedes satisfiability; H3 does not require successful Q.

Directional coverage has additional premises:

```text
H5  A source rule, in its actual scope, classifies each relevant seed binder
    and establishes its seed on the original inferred variable root.
H6  The source derivation establishes that seed's protection at the indexed
    exposure, with its same-root/capture correspondence and dependency order.
```

H5–H6 are derived for the exact selected unannotated singleton patterns below.
They remain explicit conditions for arbitrary trees of this grammar. Mere
annotation absence on an arbitrary binder, or freshness of its endpoint,
does not discharge them. No candidate general seed policy is adopted.

## 4. Constructor-directed inventory

Traverse constructor **occurrences**, retaining syntactic parent/child paths.
Register each lambda/bind declaration once and resolve each Name to its
original binder. Use RS/LX's existing ancestry correspondence; do not infer a
capture from type equality. At each direct Call occurrence `c`, construct:

```text
D(c) = (component, c, calleeNameOccurrence, b, R_b,
        sigma_b, sigma_c, captureRoute, A_b,
        u_c, U_c, p_c, originalConstraintFamily)

u_c = the original source upper checking occurrence at c
U_c = the one symbolic complete Function demand of c
p_c = the designated output-effect OCCURRENCE of U_c
```

The actual Call constructor allocates the symbolic demand and its output
occurrence. `originalConstraintFamily` retains callee checking, actual Name
return, whole argument computation, provider-owned entry, result and typed
obligations at the one original `xi=(nu,K,D)`. It is not a vector of
independently chosen witnesses. Symbolic demand allocation does not prove
those obligations inhabited.

The record keeps both the binder's source scope `sigma_b` and the use's
textual scope `sigma_c`. A source capture correspondence relates them; they
are not asserted equal. `SourceUpperUse` uses the original scope through
that correspondence. `u_c` and the callee Name occurrence are distinct
identities. The occurrence key for `p_c` survives even when two upper uses
share a static slot or normalize to equal effect endpoints.

Binder metadata records actual annotation presence/absence and introduction
kind: selected inferred formal, other inferred formal, local definition,
known external declaration, or retained incoming view. The algorithm copies
that datum from registration; it never classifies a Name as an unannotated
formal merely because the Name itself has no annotation.

At `result(name b)`, construct the actual Name/Return root; a latent Function
shape does not emit a further Call demand. At a lambda, visit its registered
body without invoking it. At Bind, visit the RHS and body in their source
environments, retaining the result binding. No additional upper record is
created by these administrative constructors.

If an original lower/provider record is present, retain it as

```text
L(l) = (l, providerOrigin, binder/root, original scope,
        FunctionLowerOccurrence, lowerOutputOccurrence, inheritedPacket)
```

in a disjoint tagged inventory. Neither endpoint equality nor an SCC root
reference moves it into `D`. Independently protected lower evidence survives.

## 5. Exact bounded occurrence theorem

Let `Calls_Name(T)` be the actual Call constructor occurrences of a skeleton
`T` in §3. The inventory constructor returns `D_T` by the pass above, without
receiving a pre-enumerated upper-exposure set.

**Theorem U.** Under H1–H4, the map `c -> D(c)` is a bijection from
`Calls_Name(T)` to the generated direct source upper-demand records, up to
coherent nominal renaming. Every record reflects its original Call, binder,
scope route, upper orientation and designated output occurrence. No Result,
Lambda, Bind or provider/lower record is in its image except through its
actual contained Call occurrences.

**Proof.** A literal or Name has no Call occurrence and emits no demand.
Result returns the inventory of its data child. Lambda retains its binder
and takes exactly its body inventory; the source body scope/capture route
is preserved. Bind combines its distinct RHS/body occurrence inventories
with the registered result binder. At Call, the ordinary Call constructor
creates exactly its own `u_c,U_c,p_c` plus the inventories of its children.
The outer `c` key is distinct from every contained Call key, including a
Call in an argument lambda. These cases are disjoint and exhaust the grammar.
Each generated record projects to its creating Call; reapplying construction
at that Call returns the same dependent fields. Induction proves both
inclusions and uniqueness. No case reads solved shape or Q. QED.

This is structural source-constructor coverage for H1–H4, not a theorem that
every Function inequality anywhere in a solver is an original source upper
use. Annotation checks and structural comparisons require their own source
rules and are absent from `Calls_Name(T)`. Constraint replay creates no new
original Call occurrence.

**Conditional theorem DP.** Under H1–H6, the complete conclusions of
Dir-Protect **on these original direct Call exposures** are obtained by
joining the source-derived seed-at-exposure derivations with `D_T`:

```text
N_T = { (k,beta_b,u_c,sigma_b,p_c,route) |
        D(c) in D_T and the source derivation proves
        ProtectedVarAt(k,v_b,sigma_b,u_c) through route }.
```

For soundness, every emitted tuple has exactly the displayed rule's two
premises and its designated conclusion. For completeness, invert any such
conclusion: its original Call exposure is `D(c)` by Theorem U; H5–H6 supply
the same seed-stage witness, so that pair is enumerated. Both keep the same
original shared assignment. The lower inventory has no matching production
head. This is a restriction to one constructor class, not a new exhaustive
definition of whole-language protection.

No arbitrary seed-at-exposure set is claimed source-derived by this proof.
The new part over the local producer is construction and exact inversion of
the entire direct-Name Call inventory. H5–H6 remain the larger source gate.

## 6. Selected sources and separate difficult cases

### Selected unannotated sources and captured Apply

The approved ordinary pattern `apply f x = f x` has one Call demand on the
registered inferred formal `f`. Its selected annotation-absence seed is
registered before that body's exposure. Thus the existing selected seed
derivation discharges H5–H6, and Theorem U plus DP covers exactly that source
exposure without supplied completed P or successful Q.

For the separately approved exact candidate

```text
my apply f = { my step x = f x; step }
```

the selected structural correspondence is

```text
lambda(f,
  bind(step,
    result(lambda(x, call(result(name f), result(name x)))),
    result(name step)))
```

There is exactly one direct Call occurrence, inside `step`. Its Name route
points to the registered outer `f`, its upper output occurrence is produced
there, and the already derived selected registration/capture proof supplies
H5–H6. Returning `step` emits no second upper use. Its latent Function value
creates neither another seed nor additional protections by shape traversal.
This construction uses only the exact selected brace interpretation.

The capture route establishes static identity and the logical seed dependency.
It does not itself construct typed packet attachment at an actual receiver,
an event observation or protection of every event from an eventual provider.

### Annotation

For the selected annotated example
`apply(f: _ -> [io] _, x) = f x`, Theorem U still inventories the direct
Call under its admitted Value interface. It cannot reuse the **absence**
premise of the unannotated seed derivation. It also does not decide that all
existing protection vanishes. The actual annotation rule must identify its
governed contribution and scoped `io` permission, preserve unrelated and
inherited evidence, and distinguish permission from realized removal.

If elaborating that annotation creates an original Function upper check at
the annotation boundary, its occurrence is distinct from the Call's `u_c`.
The §3 grammar does not enumerate it. A total source upper-use inventory must
include that annotation constructor and prove its own seed-at-exposure
premise; identifying it with the Call by endpoint equality is unsound.

### Known external Names

A direct Call on a known external declaration has an original Call demand
and its actual declaration/root/scope route. It receives no **new
unannotated-formal seed from Name lookup**. External provenance is retained
even if its public signature contains variables or its use has no annotation.
Authentic inherited/certified incoming seed evidence, if any, remains its
original evidence; this note does not erase it or assert every external
packet is unprotected.

If that provider is passed to the selected protected formal, the formal's
upper demand and seed are separate from the provider's original lower
occurrence. The former does not back-mark the latter.

### Recursive SCC exposure

A finite registered recursive graph can be scanned once per source body:
back references reuse roots rather than unfolding. Hence the direct Call
**occurrence inventory** extends to those registered bodies. RS already
supplies the structural component ledger; another copy/origin checker is
unnecessary.

However, root predeclaration and SCC membership supply neither a new
protected-variable seed nor its applicability at an exposure. A Call on an
internal recursive member must retain its local-definition origin. Any
provider/lower Function constraint remains separately oriented. A seed
introduced by an actual SCC source rule needs that rule's dependency proof;
the final root graph cannot create it retroactively. Complete simultaneous
member validation and semantic view eligibility remain the existing RS
source leaves, not conclusions of this finite scan.

## 7. Minimized missing-constructor and owner table

The smallest missing sites are listed independently. These are constructor
obligations, **not admitted Yulang counterexamples or rejection policies**.
No alternate language meaning is selected.

| Minimal site | Inventory available now | Precise missing constructor/premise | Owning source responsibility |
| --- | --- | --- | --- |
| One annotated formal, one `f x` Call | Binder annotation occurrence and the distinct direct Call demand | Annotation-governed seed/protection premise and scoped contribution/permission correspondence; any annotation-generated upper needs its own origin record | Actual annotation elaboration/boundary rule, inferred-call views §4 |
| One known external Name used as callee | Declaration route and Call upper demand | No fresh seed is missing merely because this Name is unannotated; inherited applicability needs its authentic source/use derivation | Declaration or whole incoming-use provenance, never Name's local spelling |
| Exact selected captured `f x` | Original binder route, one upper occurrence, selected seed-at-exposure proof | No missing static exposure premise in this case; typed event/receiver attachment is a separate gate | Existing selected Name/capture/Call derivation, then typed realization |
| One recursive member with a self-reference and one Call | One root, one original Call occurrence, separate lower records if produced | Any claimed recursive-definition seed and its source-stage applicability; independently, simultaneous member validation | Recursive source formation/discharge, not SCC identity allocation |
| One computed callee returned by an inner Call | Outer Call exists outside this grammar | Source correspondence from the actual returned callee to an original protected inferred root and its exposure premise | Result/provider correspondence and ordinary Call elaboration |
| One later semantic seed on a root with an earlier exposure | Both origin events can be retained | A source rule proving protection at that earlier exposure | Source-stage applicability; physical worklist order is insufficient |

For the recursive row, `my r x = r x` is a one-member/one-Call **schematic
constructor site**. It fixes the internal callee Name to definition `r`, not
formal `x`. It is not a parser, typechecking, termination or protection
acceptance claim. Deleting the Call removes the requested exposure; deleting
the recursive reference removes the SCC-specific obligation. The purpose is
to locate the minimal owner of an unsupported seed claim, not to prove that
the selected language must create such a seed.

The annotation site likewise minimizes to its one annotation boundary and
one governed use. Its raw Call count cannot tell whether an annotation
upper exists, whether protection is independently present, or which actual
contribution a granted permission governs.

The precise blocker for a universal source theorem is **total original
upper-rule and seed-applicability construction across these source owners**.
Neither a larger local join enumeration nor another RS decoration proves
that premise. The recommended different method is constructor inversion at
the actual annotation/recursive source rules, returning their missing heads
or proofs, rather than a third supplied-record probe.

## 8. Independence, failure conditions and omitted scope

No executable oracle is used. Theorem U is proved by inversion of the
independently stated existing source/core constructors, with H3 explicit.
DP shares the selected Dir-Protect rule with the local producer; it is a
conditional composition theorem, not independent validation of that source
rule. An implementation/checker that accepts `ProtectedVarAt` as input would
only check the join after the unresolved applicability premise.

No random seeds, ranges, mutant runs or exhaustive finite searches are
claimed. Named failure conditions are source incidence loss, collapsing
Name/Call or upper/lower occurrence identity, treating binder annotation
absence as Name metadata, manufacturing a seed from external lookup,
omitting latent lambda-body Calls from the static traversal, and replacing
a source-stage proof by root reachability or successful Q. The source cases
above distinguish these shortcuts logically; they are not executed mutation
coverage.

Unverified: arbitrary raw source elaboration; annotation semantics/realized
removal; computed-callee correspondence; recursive seed eligibility,
simultaneous validation and semantic generalization; all original upper
checks beyond direct Calls; complete profile/admission/descriptor/event
realization; full solution coverage and principality; foreign/production
correspondence and implementation. Failure of the bounded grammar hypotheses
does not authorize source rejection or weakening natural inference.

## 9. Baseline, checks, resources and stop conditions

All eight direct mathematical dependencies below were compared with bytes
at the pinned baseline; each matched. No unfinished worker artifact is a
premise. Rule reads: `rules/research-lab.md`, `rules/design-authority.md`,
`rules/git-concurrency.md`; no shared task/index/rule/authority file was edited.
Final artifact integrity and dependency revalidation results accompany the
submission. The artifact freezes when submitted; later review repair needs
a renewed write lease.

The assignment supplies a no-code/no-test/no-build budget and this single
output path, with no numerical CPU/RAM/wall cap. This lane used serial small
read/hash/integrity commands only, no heavyweight process, probe, child,
build, test, Oracle, Git mutation or temporary output file. Peak RSS and
aggregate CPU are not measured. Wall time is reported in the submission;
no performance claim depends on it. The proof uses symbolic finite grammar
induction, so no finite search domain is disguised as universal coverage.

Stop conditions: do not fill a missing source head by a new semantic
assumption; stop source completeness at the owner table; do not broaden
brace authority, infer a stage witness from a solution, or request code/
question/Git authority. Shared status promotion remains primary/curator work.

| Direct dependency | Baseline SHA-256 |
| --- | --- |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/progress/2026-10-06-directional-protection-source-generation.md` | `3702eb2ea5108eba1adc8ab7a557542abb9993cee09f70b738e2999a05a2d185` |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| `notes/progress/2026-10-06-directional-joint-source-judgment.md` | `fc459dfac03693f426dea575585a0d20d7a075f8c7ac27be9fd2e67a150466c1` |
| `notes/progress/2026-10-06-directional-recursive-generalization-supplier.md` | `2f169e0f894fff8695cf8e1ef40f5a9734abfe87484d9db6aab23eae941b8898` |

## Commit packet

- Exact leased path: `notes/theory/2026-10-08-directional-source-upper-exposure-coverage.md`.
- Baseline: `9ec4f7c290a8bd9619301a01daed9218c46d446a`.
- Changed dependency hashes: none at producer freeze; eight pinned/live
  byte comparisons match, with full hashes above.
- Review status: frozen new producer, independent review pending; prior
  selected seed and RS/LX results retain their existing scoped review.
- Checks already run: narrow branch/baseline/path inspection, direct-input
  SHA-256 and baseline equality; final Markdown/link/whitespace integrity
  result supplied with the packet. No compiler/runtime check or executable
  proof claimed.
- Proposed checkpoint message: `research: bound directional source upper-use coverage`.
- Shared-record deltas intentionally left for primary/curator: record the
  direct-Name Call inventory inverse and conditional source coverage;
  preserve annotation, computed-callee and recursive applicability leaves;
  no full-source/gate closure, new authority, public source restriction or
  implementation-status promotion.
- Recommended next action: independently review the frozen bounded theorem
  and owner table, then assign the annotation upper/seed-applicability
  constructor inversion as the next source method.
