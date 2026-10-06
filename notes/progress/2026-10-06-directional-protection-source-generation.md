# Source generation after the directional protected-variable correction

Date: 2026-10-06
Baseline: `7c92667fac06bd8414d72bf0a11843d3b6dc8ea8`
Status: independently reviewed bounded research derivation and executable characterization
Authority: the direct current user decision recorded in the linked addendum;
           all other source, role, scope, and production rules are unchanged
Claim class: constructed local producer; compiler-referee-reviewed local proof;
             finite regression evidence; not a certified full-source theorem
Implementation authority: none

## 1. What changed

The [user correction](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
selects a primitive that the earlier work did not have: a protected variable
exposed by an original upper Function demand protects that view's output
effect, whereas an existing Function lower bound does not receive backward
protection. This is not an approval of the old E/R inventory.

The critical pair is now fixed, not left as an arbitrary supplied profile:

```text
protected v
L = 'e -> ['g] 'h       L <: v
U = 'a ['b] -> ['c] 'd   v <: U

new protection from this seed: upper occurrence 'c
not new protection from this seed: lower occurrence 'g
```

`g` and `c` can have equal eventual denotations. Their originating occurrences
are still different. Inheritance can already protect a provider independently;
that fact must not be deleted in order to display the negative case.

Two earlier shortcuts are therefore withdrawn: counting Call nodes to infer
an exhaustive profile, and putting a default on all effect positions of a
completed/unknown result merely because it belongs to `f`'s eventual type.
The lower/upper distinction must exist before those representations are erased.

## 2. Constructor from source, not from a completed original P

The bounded source remains the approved component

```text
my apply f = { my step x = f x; step }
```

The [selected source interpretation](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
fixes the same outer `f` capture, local binding, and final return of `step`.
The [ordinary source rules](../design/2026-10-02-typed-computation-core-elaboration.md)
section 6 provide the Value parameter/Name/Result skeleton. The
[previous Call construction](2026-10-06-source-call-generation-construction.md)
provides a source demand on a symbolic complete Function variable before
satisfiability. These are used with their existing scopes; no new surface
parser acceptance is claimed.

Generate the following source-indexed records in order of logical dependency:

1. Resolve the unannotated formal `d_f`, its shared endpoint `v=A_f`, its
   original contract root `R_f`, and its source scope `sigma`. Record actual
   annotation absence on the binder, not merely absence of an annotation at
   a Name use. Apply the user's existing protected-variable treatment to this
   formal, yielding a seed witness `k` before its Function exposure.
2. At the actual use `c=f x`, Name lookup reuses `v`, not a separately chosen
   provider. The argument is the actual returning Name computation after
   the inner Value-entry rebind; retain `J_x` as well as its printed
   `Comp(empty,A_x)` interface. An arbitrary empty-row computation is not
   interchangeable with this returning Name root.
3. Emit the original symbolic upper demand `u: v <: U` whose complete
   Function view has input/result endpoints and output-effect occurrence
   `outEff(U)`. Retain the original Call, binder and scope correspondence.
   The demand is source-generated even if its later comparison fails.
4. Apply `Dir-Protect(k,u)` to emit protection at exactly `outEff(U)`.
   This step takes no `Applicable_original`, `Slots_original`, successful
   `Q`, solved result shape, actual provider value or completed profile as
   an input. It is the newly supplied local original-protection producer.
5. Keep the generated `(k,beta,u,outEff(U))` witness alongside all original
   constraints and independent inherited packets. Do not infer a runtime
   `Flow`, receipt, active receiver, `Observe`, event membership or grant
   from this static output.

For a previously known imported/externally supplied callable, step 1 does not
supply a new formal seed merely from Name lookup. For a protected root with
an existing recursive/provider lower `L <: v`, preserve `L` and its `g`
unchanged; its orientation does not match step 4. Their later direct complete
`L <: U` obligation is retained, not assumed true and not composed from two
successful concrete queries. Variable-bound replay and semantic evidence are
different from propagation of protection backwards into `L`.

This yields the exact-source local producer without the former complete-P
premise. General source binding/SCC formation, all upper-exposure provenance,
and all other kinds of effect-position introduction remain outside this local
construction. In particular this note does not infer a generic rule that a
Value-entry callable is Pure, or change the actual provider's entry.

## 3. Exact finite rule normal form

Let `S` be the set of original seed witnesses `(k,v,sigma)`. Let `U` be a
finite set of original source upper-exposure records; each includes the
certificate that `v` was protected by `k` at the exposure, its original
scope, and its designated output-effect occurrence. Lower bounds live in a
separate set `L` and continue to constrain the underlying joint relation.

Define, using the selected single production rule, not a new universe of
admissible effects,

```text
M(S,U) = { (k,beta,u,sigma,outEff(U_u)) |
             seed k protects the shared v at u in its original scope,
             u is an original source-generated v <: U_u exposure }.
```

Original scope correspondence is exact. A capture/use in a nested textual
scope refers back to this same original scope through its source witness;
textual containment alone is not a certificate. Any general transport to a
freshened scope must carry the whole correspondence.

### Local soundness and completeness

Every emitted record has a seed and a source upper exposure as its witnesses;
therefore it is precisely a conclusion of `Dir-Protect`. Conversely, any
instance of that displayed rule selects one such pair and the unique output
effect occurrence of its Function view, so its conclusion occurs in `M`.
There are no recursive branches in this one-step producer. Repeated records
are set-idempotent; different introduction/use witnesses remain distinct.

This is a proof of the local rule's complete implementation in the displayed
incidence relation. It does not assume the desired original profile as a
premise. It also does not prove that every protection producer of the whole
language is this rule, or that every source elaboration has already generated
all its input exposure certificates.

### No backward contamination

For every set of provider/recursive lower records `L`,

```text
NewFromThisRule(S,U,L) = M(S,U).
```

Proof: no selected production clause reads `L` to create protection. The only
head-producing rule matches `v` on the left of its Function demand; a lower
record places the Function on the left and `v` on the right. It therefore
cannot discharge that premise. This excludes newly marking a lower `g` from
this seed, not retaining an independently protected `g`.

Adding a lower bound can of course change the set of solutions of the full
typing constraints. The equality above concerns the newly generated local
incidences over a fixed source inventory, NOT equality of typing solutions
before and after adding a genuine lower-bound constraint.

### Q independence and staging

`M` contains source upper-exposure certificates but no pending comparison
result. Thus changing a pending Q result cannot alter `M`. A comparison-only
Function shape without its original source exposure cannot enter `U`.
This does not prohibit the source itself from emitting an inequality; it
prohibits using success of that inequality to justify its protection premise.

The premise "protected while still a variable" must be retained. Enumerating
already-certified inputs in another order leaves the join unchanged. This is
not a proof that arbitrary inference-stage reordering is valid, nor a decision
that a newly created seed retroactively licenses every earlier exposure. If
such replay is needed, it must retain or derive the relevant stage witness.
The finite checker's permutation test has only the former, static meaning.

### Joint renaming and extension

A capture-avoiding bijection `r` that transports seeds, original scopes,
endpoints and exposure records coherently gives

```text
M(rS,rU) = r M(S,U).
```

Map each seed/exposure witness pair through `r` for one inclusion and through
its inverse for the other. This uses no independent per-port choices.
It is not a claim about a graft that generates new exposure derivations; such
new derivations must first be justified as source input.

For any fixed existing original relation `R` over whole rows `xi=(nu,K,D)`,
a deterministic dependent evaluation of these newly generated records has the
exact graph extension

```text
R_dir = { (xi, M_xi(S,U)) | xi in R }.
```

Erasure maps it onto exactly `R`, and its fibers are singletons. Every
unchanged downstream predicate on the old row therefore commutes with this
extension. All old predicates, provider coordinates and scopes remain in the
same row. This is static bookkeeping conservativity, not a proof that adding
protection leaves handler observations unchanged. It is also not a definition
of `R`, general source soundness or source-wide principality.

## 4. An actual obstruction to forgetting direction

There is a two-record counterexample to an endpoint-shape-only producer:

```text
H_up   = { seed(k,v), source upper v <: Fun(a,b,c,d) }
H_down = { seed(k,v), provider lower Fun(a,b,c,d) <: v }.
```

Erase the inequality direction but retain exactly the same variable,
Function shape and undirected adjacency. The two erased inputs are equal.
The user-selected new output is nonempty for `H_up` and empty for `H_down`.
Therefore no function of this erased input can equal the directional producer
on both histories. Proof: equal inputs force equal outputs, a contradiction.
No runtime admission assumptions or complete alternative Yulang semantics are
needed: the two desired local outputs were explicitly supplied by the user.

A related information loss occurs if one merges protected upper and
unprotected lower occurrences merely because their effect endpoints have
equal denotations. Printed/solved type equality is not original incidence
identity. This is why the proposed proof record carries original origin/use
and position, rather than a global bit keyed only by a normalized effect.
The counterexample constrains representation; it does not select a particular
solver data structure or demand a new carrier.

## 5. How this connects to the previous main gate

The current first-generation edge now includes a defined local primitive:

```text
resolved unannotated inferred formal / original scope
  -> original protected-variable witness
resolved Function use on the shared root
  -> original upper Function demand, before solving
these two together
  -> directed output-effect protection incidence, independently of Q
```

This removes the need to ask whether to paint all eventual result positions
or only a syntax-counted singleton. It also removes complete P as a premise
of THIS local introduction. The protected seed is information already present
at the variable stage, not a completed effect-profile inventory in disguise.

The following downstream tasks are not hidden in the new primitive:

- Compose every other source-licensed directional/typed propagation step,
  preserving lower-origin contributions separately. Do not infer protection
  of an arbitrary nested result from its latent shape or from belonging to
  the same final normalized type.
- Relate the generated incidence to source contribution observation, actual
  receiver/receipt, typed capture/rebind/read and original live state.
  Lexical capture supplies identity, not the missing typed packet attachment.
- Interpret complete descriptors and every independently admitted punctured
  context/world. The existing ordinary open-context constructor is reusable,
  but its full-world/admission and production correspondence are not proved
  by constructing one protection fact.
- Prove full seed/refined original-solution preservation, not merely the
  deterministic record extension. Prove all-view factorization and finite
  representation before principal inference or production cutover.

The maximal `J_call` source/typed-core constructor continues to use the actual
whole carrier, provider entry, body and designated consumer with the original
joint data. No port-wise `nu,K,D`, family-wide subtraction, public-type-as-
annotation identification, or Q-derived admission is introduced. Option A/2
still requires the separate complete `D_C subset D_A` and `P_A subset P_C`
obligations, including production-only members.

## 6. Frozen Oracle crosswalk

The [existing crosswalk](2026-10-06-main-source-generation-oracle-crosswalk.md)
remains mechanism evidence at its pinned historical source, not authority.
This continuation runs no Oracle and adopts no old solver representation.
The new direction says what its corresponding bookkeeping must preserve:

| Historical mechanism | Required preservation under the new direction |
| --- | --- |
| Shared formal endpoint | Keep the source seed and upper-use witnesses attached to the same formal; sharing does not turn a lower provider into an upper use. |
| Application constraints | Emit the upper demand before solving, with its original occurrence and output-effect position. |
| Environment-aware generalization | Preserve the captured root and all live directional provenance in the joint interface. |
| Coordinated use-time freshening | Rename the whole certificate/constraint family; do not merge distinct upper/lower origins at equal printed endpoints. |
| Provenance routing | Retain whether a Function edge was source upper demand or provider lower information. |
| Annotation/function-frame producer | Keep actual annotation absence and the variable-stage seed distinct from an imported callable's known contract. |

No marker depth, pop count, mutation level or old subtraction algorithm is
chosen by this table. In particular a legacy mechanism that erases direction
would require a preservation proof or a correction, not semantic authority.

## 7. Executable checks and their exact scope

Run from the repository root:

```sh
python3 tools/research_directional_protection.py
```

The script contains a literal rule-comprehension reference and an indexed
join. They share the displayed user rule and input certificate interpretation;
this is differential consistency, not independent source-semantics validation.
The finite domain is three roots, at most six upper demands, three lower
bounds, every seed/upper/lower subset, and eight assignments of effect endpoint
aliases. All **32,768** inputs agree; reversing certified-record enumeration
adds **32,768** order checks. There are **18** focused equality assertions,
one invalid-identity rejection, one coherent-renaming check, **256** complete
Boolean relations with **768** unchanged query filters, and seven rejected
mutants in total (six named incidence mutants and one marginal-product mutant).

Named errors include reverse-lower propagation, selecting the input rather
than output effect, blanket latent-result marking, origin erasure, omission
of required upper protection, and collapsing distinct use incidences into
one endpoint. The joint mutation detects independently recombining marginals.
The focused cases include pre-existing recursive lower bounds, independently
inherited protection, a known external binding with no local annotation,
missing or seed-mismatched stage provenance, wrong scope, Q-only shape, and
inert latent results.

The model uses supplied resolved/proof records. It does not parse Yulang,
classify arbitrary source formals, validate all stage certificates, resolve
Function inequalities, compute `Observe`, run handlers, or implement production
inference. It changes no compiler or shadow module and no existing golden
expectation. Python standard library only; one bounded process, no broad build.

## 8. Review, authority and integration

A compiler referee independently reviewed the frozen local derivation and
checker and found no semantic or proof-scope issue. A spec auditor checked the
directional rule against the governing call-view and nested-block contracts,
confirmed that the finite checker and dependency records do not exceed their
stated claims, and found one minor navigation defect in the two theory maps.
The maps now link the current directional-decision delta and label E/R
adoption as historical; the spec-auditor delta review found no further issue.
This closes only review of the local rule characterization and its navigation.
It does not certify the full-source theorem or mark any production gate closed.

The direct user correction supersedes the old E/R question; it requires no
fabricated E/R approved-answer bundle. The original question remains intact
and uncommitted, with a separate local supersession receipt. Shared task
navigation records the new target, and all earlier claim classes are retained.
Final Git-data publication must compare the expected branch head, preserve
all other paths, update without force, and read the resulting ref/tree back.
The final reply reports the actual successful commit, not a planned SHA.
