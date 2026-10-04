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
