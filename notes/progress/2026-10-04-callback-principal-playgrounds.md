# Callback lift and principal-support research playgrounds

Date: 2026-10-04
Status: bounded executable characterization evidence; no implementation or
semantic authority
Review: independent compiler_referee review of callback/lift models found no
blocking/major finding. The row-match probe's minor “minimum” wording issue was
repaired as “lexicographically least.” The scalar-lift probe review found a
minor scope overclaim; the model now records explicit lexical-scope/path labels
and says that logical quantifier scope and joint hiding remain untested. The
primary reran the focused checker and closed that delta without another review
round.
The minor identity-coverage suggestion was closed by generating distinct
per-occurrence evidence identities and checking preservation after lifting.
A later bind-composition delta review found that the minimum counterexample
needed to distinguish empty joins from nonempty exact joins; both minima are
now reported, and the primary reran the exhaustive checker.
Independent spec_auditor review of the typed-pullback contract-join probe found
no actionable findings; its finite scope and reported counts match the code.
Independent compiler_referee review of the callable-projection probe found no
blocking or major issue and validated its minimal witness. Its minor finding
was a single `production` label in a finite-model count; the script now says
`candidate endpoint`, and the primary reran the focused checker and
`py_compile`.
The compose-hygiene probe review found no blocking or major issue. Its minor
finding required explicit assertions for resumed response/live-state pairs;
these were added and the primary reran the focused checker and `py_compile`.
Governing direction: [inference research playgrounds](../design/2026-10-04-inference-research-playgrounds.md)
Governing callback design: [production callback endpoint generation](../design/2026-10-04-production-callback-endpoint-generation-draft.md)
Governing principal criterion: [principal scheme acceptance](2026-10-04-principal-scheme-acceptance-criteria.md)

## Callback lift invariant

[`tools/research_callback_lift.py`](../../tools/research_callback_lift.py)
models one fixed `nu,K,D` fiber and finite source-witness relations with
separate argument-origin, body-origin, and result fields. The candidate lift
adds total derived output coordinates from the same witness while retaining
the old tuple and distinct per-occurrence `d-`, `d+`, and `b+` evidence
identities. It exhausts all 16 binary relations on two coordinates. Every lift forgets back
to the exact original witness relation and preserves the complete modeled
observation.

The model also composes a first-child and suffix relation by a shared
`(fiber, intermediate)` join, as a finite `bind`-shaped relational case. It
exhausts all 65,536 pairs of binary child relations under each of two distinct
metadata contexts (63,135 pairs per context have nonempty composition). The
checked lift preserves each complete old tuple, its owners, scope, distinct
call/argument receipts, and selected port-evidence identities.
A mutant that drops the intermediate join has a two-row minimum if empty exact
joins count: one first-child row and one suffix row with a mismatched
intermediate. The exact join is empty, while the mutant admits a result. If a
nonempty exact join is required, the minimum has three rows: one first-child
row and two suffix rows, only one of which matches. The mutant admits an
additional result from the unmatched suffix. These minima are exhaustive
over the stated binary domains. This tests that the link survives composition;
it is not a test of the operational continuation rule, requests, or resumption.

The model also shrinks independent-marginalization failure to two correlated
rows, `(0,0)` and `(1,1)`. Taking the product of the two marginals invents
`(0,1)` and `(1,0)`. Six of the 16 binary relations expose such a mismatch.
This is a concrete finite obstruction to replacing a joint witness relation
with unrelated coordinate marginals. It is not a counterexample to Theorem C:
the model has no source constructors, binders, calls, future use, resumption,
endpoint solver, or actual/checked source correspondence.

## Principal common-support invariant

[`tools/research_principal_support.py`](../../tools/research_principal_support.py)
enumerates 584 assignments of one to three distinct source occurrences over a
three-element finite support universe. For each, it checks that the least
common support admits each original occurrence separately, and that every
candidate support admits all of them exactly when it contains their union.
Original occurrence supports remain an ordered tuple; no equality between
branch/call endpoints is introduced. The smallest two-endpoint witness is
`{0}` and `{1}`, whose common public support is `{0,1}`.

This is only the powerset algebra behind a common-allowance candidate. It does
not define effect-row subtyping, prove that source generation produces these
supports, account for coupled Function ports or subtraction attachments, or
establish either direction of the principal-scheme solution-family theorem.
In particular it does not justify the `compose` hygiene boundary or the
principal `call`/`twice`/`choose`/`higher` interfaces by itself.

## Conditional point-row fresh-use probe

[`tools/research_principal_row_match.py`](../../tools/research_principal_row_match.py)
exhausts the 32 assignments of one receiver and four independently owned
point arguments over two ground equality classes. It checks the conditional
point-row formula `{F<r>} ⊆ {F<a>,F<b>}` as the disjunction `a=r ∨ b=r`,
then alpha-freshens `a,b` separately for two uses and retains both formulas
under one correlated receiver constraint. Explicit occurrence-level witness
search agrees with the formula on all assignments: 18 satisfy the two row
constraints, and 4 remain after the joint receiver restriction.

An eager-left-match mutant selects `a=r` for both uses before the receiver
constraint is applied; it admits none of those four assignments. The
lexicographically least lost assignment in the stated binary universe is
receiver `0`, use 1 targets `(0,1)`, and use 2 targets `(1,0)`. The search does
not vary the number of uses, targets, or constraints.
Each row comparison succeeds, while the client's cross-use constraint requires
opposite choices. The mutant therefore demonstrates why the conditional
finite presentation must retain the disjunction through independent use and
joint restriction instead of committing a local match early.

This is characterization evidence for the exact point-valued fragment in
`coupled-effect-interface-core-draft.md` § “Finite point-row constrained
presentation” and its whole-presentation freshening law. It assumes the
candidate `FamCompat_A` reduces to equality over two ground classes. It does
not establish that Yulang source constraints occupy that fragment, interpret
effect rows, compare complete Function interfaces, or prove the seven
principal acceptance schemes. It adds no semantic rule or implementation
authority.

## Scalar callback abstraction and checked-lift probe

[`tools/research_callback_sat_lift.py`](../../tools/research_callback_sat_lift.py)
combines the local integer-body relation `Sat_j(a,v,C,C')` from
[`callback-local-abstraction-boundary`](2026-10-04-callback-local-abstraction-boundary.md)
§§4–5 with the old-tuple-preserving checked lift. Its finite Force corpus has
548 argument graphs over `Int={0,1}` and two configurations: direct returns,
all response subsets for one request, and every pair of response subsets for
two sequential requests. It retains pending request prefixes and every legal
resumption branch under one fixed `nu,K,D` fiber.

The checker produces 5,800 pending/completed abstract observations. Exact
identity and integer-zero literal bodies each embed all 3,684 of their finite
observations in the abstract relation. The checked extension is a total
function of each complete old tuple; forgetting its added `d`/`b` projections
recovers the entire abstract relation, including pending suffixes, response
histories, receipts, owner labels, one modeled lexical-scope identifier, typed-
path labels, and the distinct `d-`, `d+`, and `b+` identities. Challenge
The finite challenge graph list is fixed before body/query generation; this
does not construct or compare actual/checked challenge domains. The probe
checks copying those modeled fields, but does not model logical quantifier
scope, independent hiding, or movement of joint witnesses.

The `v=a` checked-generation mutant loses 2,116 abstract observations. The
lexicographically least direct-return loss under `(initial state, input,
result, challenge)` is input `0`, result `1`, state `0`. A one-request witness
has response `1` resumed in live state `0`, then `Sat_j` returns `0` for input
`1`; it is absent under the mutant. This concretely tests that the scalar
abstraction's output coordinate stays distinct from its read coordinate and
that a checked lift adds no condition to the old tuple.

The finite domain is `Int={0,1}`, configurations `{0,1}`, at most two request
layers, and all subsets of the four response/configuration pairs per request.
It does not establish the production F5 endpoint denotation, arbitrary integer
or request behavior, higher-order observations, general Handler/State
semantics, Yulang source-wide challenge admission, or logical scope/hiding
transport. Its proof target is only the executable characterization of Theorem
L's bounded scalar fragment, not Theorem L's general statement.

## Typed-pullback complete-contract join probe

[`tools/research_principal_contract_join.py`](../../tools/research_principal_contract_join.py)
exhausts the finite semantic-contract join from
[`common allowance/context preimage`](../design/2026-10-04-common-allowance-context-preimage.md)
§5 for a two-stage source tuple `(g,x)`. The first challenge projection sees
one of two Function-valued arguments; the second sees one of two integer
arguments. Each stage has its own challenge domain and maps each local value
to a closed support over `{Read,Write}`. The generator ranges over all 16
source tuple relations, four domains for each stage, and 16 support maps for
each stage: 65,536 cases.

For each tuple relation `G`, the checker forms the common domain by pulling
both local domains back along their own projections, then unions the two
supports at each retained tuple. All 65,536 cases satisfy the complete-domain
condition and the pointwise least-support property; 24,320 have a nonempty
common domain. A minimized one-row case `(fn0, 0)` is admitted by both typed
pullbacks, while a mutant that identifies the Function-valued and Int-valued
challenge coordinates admits nothing.

This checks the finite contract theorem's typed pullback and closed-support
join, not Yulang's completed `A <: B` resolver or principal-scheme maps. It
does not prove that a shared abstract effect component denotes the joined
views, handle subtraction attachments, or preserve arbitrary higher-order
correlation. The result is evidence for §5's semantic join and for keeping
stage projections attached to the source tuple; descriptor realization and
all-view factorization remain open.

## Higher-order callable projection boundary probe

[`tools/research_callback_callable_projection.py`](../../tools/research_callback_callable_projection.py)
models a source identity callback returning a callable, followed by one
client-side invocation. Two runtime callables share the same structural
Function interface but retain distinct source authority and continuation
identities. Across all four nonempty endpoint-owner sets containing the
actual source owner, full typed-observation membership factors through the
exact identity source iff the endpoint admits no extra owner.

The minimized over-approximation has one source input (`owner-left`), one
future invocation, and two same-interface callable identities. If a candidate
endpoint admits both, the source graph cannot account for the extra
`owner-right` request and continuation. A mutant that erases callable
authority, request origin and continuation owner makes that false factorization
appear to pass; it does so in both source-owner cases. The typed projection
here erases no callable authority: the approved decision only erases concrete
data-value identity/correlation, while retaining authority relationships.

This is a bounded obstruction to applying the scalar integer `Sat_j`
abstraction to callable values without source ownership. It is not a
counterexample to the approved projection or evidence that production admits
the extra behavior. It does not model arbitrary higher-order histories,
subtraction, or production endpoint denotation; production conformance remains
open.

## Annotation-free compose hygiene probe

[`tools/research_compose_hygiene.py`](../../tools/research_compose_hygiene.py)
checks the finite `Force(D_g) >>= (v => RebindResultPath; B_f)` request case
under one fixed `nu,K,D` fiber. Its request-bind relation keeps a pending
prefix and appends the Value-entry suffix. The search covers two operation
kinds, all 16 subsets of two value/state responses, and all four handler
operation sets: 128 cases. It verifies exact response/live-state transport,
request origin/event/path preservation, and the pending/resumed suffix. With
no written capture contract, every caller-owned `g` request remains in
outward `c` even if `f` has a handler for that operation.

A row-match mutant subtracts the request whenever `f`'s handler covers its
operation and both source types print component `b`. It loses the contribution
in 64 cases. The minimized witness is one pending `Read` from `g` at
`J_arg:g-to-f`, an inner `Read` handler in `f`, and no capture contract; the
source-boundary view retains `Read` in outward `c`, while the mutant removes
it. This characterizes the hygiene consequence and refutes subtraction based
only on inferred component reuse. It does not model explicit capture,
multi-request operation execution, complete Function comparison, or production
endpoint projection, so it does not close the `compose` principal-scheme gate.

## Next proof work

The callback main gate still needs a source-to-endpoint correspondence showing
that production source derivations satisfy Theorem C's full finite generator
and preserve its whole-bound inclusion under the same `nu,K,D`. This leaf
model checks only the local total-coordinate extension lemma's basic shape.
The principal main gate still needs one same-fiber factorization argument
through source constraint generation, co-occurrence analysis, complete
Function comparison/evidence, and generalization. The support model identifies
the least finite common support but does not supply that argument.

## Value-entry operational-order probe

[`tools/research_callback_entry.py`](../../tools/research_callback_entry.py)
implements the selected finite `Return`/`Request` bind equations and the
Value-entry path
`receipt; Force(D) >>= (v => RebindResultPath; B(v))` for a prebuilt Pure value
invoked through a callback-slot typed view. It checks argument/body paths with
zero or one request each under two initial states, and enumerates all 18
completed response paths. Each path retains one call receipt, one distinct
argument receipt, one force, one rebind, and one body entry; state passed to
the body/resumed suffix follows the modeled resumed state. The underlying
callable remains Pure/Value while the slot view remains present.

The minimal eager-force mutant has one argument request. The source path orders
call receipt and argument receipt before entry force and the request; the
mutant forces and reaches the request before it establishes the call receipt.
An independent compiler-referee review found no blocking/major issue. Its
minor force-marker placement finding was corrected. A delta review found no
remaining findings. The first review also exposed a
gap between sequential requests and reusing one pending continuation; a
separate explicit witness now resumes the same immutable request continuation
twice with live states 0 and 1, checking that the bound suffix sees each state
and that the pending request remains unchanged.

The finite request table uses a fixed state update and one selected response
per path; the separate repeated-resumption witness covers only two states and
one simple suffix. It does not model general owner activation, shallow handler
dispatch, State semantics, typed `Flow`/`Observe`, callback Function port
interpretation, or production endpoint denotation. Thus it checks source
ordering and finite bind/resumption equations only.

## Verification

```text
python3 tools/research_callback_lift.py
  16 relations; all total lifts preserve old projections and observations;
  six marginalization mismatches; smallest has two correlated rows.
  65,536 bind-shaped relation pairs under each of two metadata contexts;
  minimum bad join has two rows (empty exact join), or three rows when
  requiring a nonempty exact join.
python3 tools/research_principal_support.py
  584 finite assignments; 560 retain distinct endpoint supports.
python3 tools/research_principal_row_match.py
  32 complete assignments; 18 row-formula solutions; 4 after joint receiver
  restriction; eager-left-match mutant retains 0; lexicographically least lost
  assignment shown within the stated binary universe.
python3 tools/research_callback_sat_lift.py
  548 Force graphs; 5,800 pending/completed abstract observations; identity and
  literal embeddings each cover 3,684 rows; total lift forgets exactly; the
  v=a mutant loses 2,116 rows with direct and resumed witnesses reported.
python3 tools/research_principal_contract_join.py
  65,536 typed two-stage contract cases; 24,320 nonempty common domains;
  pullback-domain and least closed-support join checks pass; one-row
  type-collapse mutant loses the admitted source tuple.
python3 -m py_compile tools/research_principal_contract_join.py
  pass
python3 tools/research_callback_callable_projection.py
  4 typed callable endpoint cases; factorization iff no extra same-interface
  owner; authority-erasing mutant false-green in both source-owner cases;
  minimum has one source owner and one extra returned/invoked callable.
python3 -m py_compile tools/research_callback_callable_projection.py
  pass
python3 tools/research_compose_hygiene.py
  128 Force/Value-entry cases; event/fiber/origin/path and suffix preservation
  pass; exact response/live-state transport pass; component-match mutant loses
  outward support in 64 cases; minimum is one pending Read request.
python3 -m py_compile tools/research_compose_hygiene.py
  pass
python3 -m py_compile tools/research_callback_lift.py tools/research_principal_support.py
  pass
python3 -m py_compile tools/research_principal_row_match.py
  pass
python3 -m py_compile tools/research_callback_sat_lift.py
  pass
python3 tools/research_callback_entry.py
  8 argument/body mode and initial-state cases; 18 response paths;
  one pending continuation resumed twice under distinct live states;
  eager-force ordering mutant minimized to one request.
python3 -m py_compile tools/research_callback_entry.py
  pass
```

## Callback B endpoint-trace audit (2026-10-05)

[`tools/research_callback_endpoint_trace.py`](../../tools/research_callback_endpoint_trace.py)
is a bounded executable audit of the finite source/evidence bookkeeping in
the reviewed callback endpoint-generation draft §§2–4. It enumerates 192
tuples of distinct outer/latent owners and operand tuples, binder scopes,
eight independently selected parameter/body/result endpoint triples, and
present or absent witnessed concrete attachments. For every tuple, the
reference trace keeps the callback literal in Handler role, requires the
`d-` Force path and the `d+`/`b+` CallView paths in the same latent tuple while
preserving distinct occurrence identities, forms the completed four-port
Function endpoint with flat covariant `[b+, d+]`, subtracts only a witnessed
attachment, and emits one final ordinary `F_lit <: F_cb` query with that
completed endpoint as its left operand. Nine deliberate mutants (owner,
tuple, role, endpoint assignment, occurrence, attachment, row, query count,
and selected path) are rejected by the audit.

This is a conformance harness for the proposed constructor/evidence trace,
not an independent source-to-production bridge: endpoint terms and the
`d-`/`d+`/`b+` evidence are supplied as inputs. It does not model their
production denotation, complete-bound membership, endpoint inequality
resolution, callback adequacy, or principal solutions. The executable check
therefore exercises the draft's finite audit boundary but does not discharge
the known full-bound realization factorization premise. The raw/HIR bridge
and production endpoint interpretation remain open; no source counterexample
or new semantic choice was found.

## `higher` returned-provider join probe (2026-10-05)

[`tools/research_principal_higher_join.py`](../../tools/research_principal_higher_join.py)
executes the source-core obstruction in
[`callback coverage and source-preserving composition`](../design/2026-10-05-callback-coverage-and-source-joins.md)
§6.3. The finite source has `f y = y`: each challenge supplies one of two
same-interface callable providers, the first call returns that exact provider,
and a later call emits its retained request origin and continuation. The
approved projected observation here keeps the challenge, typed request origin,
and continuation identity; it need not expose an inert callable's scalar
identity before that later call.

The checker exhausts all 16 relations between two challenges and two providers.
Joining stage marginals on the printed Function interface invents cross-owner
histories in six relations. Its minimum witness has the diagonal source rows
`(h0,g0)` and `(h1,g1)`: the type-only join adds
`(h0,request:g1,continuation:g1)`. Joining instead on the original returned
provider incidence exactly recovers the source image for all 16 relations.

This makes the §6.3 lossless-join obstruction executable and gives a minimized
regression against dropping the intermediate provider. It checks a finite
source-core relation only. It does not model production endpoint denotation,
Function comparison, a solver-generated common descriptor, or principal
factorization; the result is characterization evidence, not a new theorem or
a counterexample to every possible shared allowance.

## Callback admission dependency-closure probe (2026-10-05)

[`tools/research_callback_dependency_closure.py`](../../tools/research_callback_dependency_closure.py)
tests the small incidence rule behind Theorem 4 of
[`callback coverage and source-preserving composition`](../design/2026-10-05-callback-coverage-and-source-joins.md): safe hiding must close admission operands through the existing proof that an exposed request was produced and retained. Its certificate is a finite Boolean dependency graph with challenge, producer, retention, owner, and one unrelated private coordinate.

All 64 assignments and 128 assignment-pair comparisons confirm that varying
only the input outside the transitive dependency closure leaves admission
unchanged. The checker then removes the `request_exposed -> request_produced`
edge from the closure traversal and shrinks the failure to one bit: with
challenge, continuation retention, and owner fixed, changing `call_executed`
changes admission. This makes the need to follow request-production
provenance through more than one dependency edge executable.

The model checks a Boolean certificate abstraction only. It does not extract
the dependency graph from production HIR/solver evidence or prove admission
invariance for Yulang's full request, resumption, and future-use schemas. Its
counterexample rejects the omitted-producer shortcut, not the reviewed
complete-closure theorem.
