# Pure Function production reduction for the recursive name-return bridge

Date: 2026-10-06
Status: independently reviewed research-only source characterization and conditional reduction
Pinned baseline supplied by primary: `080dde430342a64ae1eab90c305e1a1f62bf8d77`
Exclusive write lease: this file only
Method: static owner-path audit and symbolic polarized task derivation
Implementation authority: none

## Objective, authority, and dependency boundary

Reduce H4 of
`2026-10-06-rec-name-return-member-scheme-bridge.md` into production facts and
the remaining semantic premise for `my f x = g; my g y = f`. The comparison
observes one finalized incoming member use at a time. It does not observe the
joint pair of open SCC roots, select intended Yulang semantics, or prove
solver acceptance equivalence.

Governing sections read:

* `rules/design-authority.md`, authority order and approval gate;
  `rules/research-lab.md`, evidence, frozen artifacts, and dependency policy;
  `rules/git-concurrency.md`, leases and primary integration ownership.
* `notes/design/INDEX.md`, relevant locators only.
* `2026-10-03-concrete-compatibility-boundary.md` §§1 and 3: one
  endpoint-dependent inequality, no composition of arbitrary successful
  concrete comparisons, and restricted applicability of preorder results.
* `2026-09-21-f5-general-function-scheme-foundation-draft.md` §§9, 22, 23,
  and 32: fresh substitution, live polarized task algebra, the exact normative
  two-member scheme, and closed/term view contracts.
* `2026-09-29-scc-intrusion-redesign-charter.md` §§1–4: F5 is comparison
  material; scheme formatting/equivalence is not the successor requirement.
* Candidate pure source rules, “Semantic fragment”, and candidate SCC scheme
  rules, “Recursive group generation” and “Graph scheme and use”. These
  remain candidate rules. The reviewed member bridge supplies H1–H4 and the
  algebraic result; its review does not establish H4.

The primary's accepted boundary is retained: candidate RecGroup is not Yulang
authority, and endpoint successes are not automatically a transitive
preorder. No pending question or approval bundle is used. `tasks/current.md`
and `tasks/research-lab.md` were inspected for context; the combined read was
output-truncated, so no exhaustive reading or new dependency on their contents
is claimed. The baseline is supplied by the primary; no Git command was run
to verify its object or compare working files with it. The hashes below pin
the actually read dependencies for primary revalidation.

## Claim classes and exact hypotheses

**Source characterization:** the listed owner paths construct and process the
polarized obligations below, assuming valid finalized handles, valid session
ownership/row indices, the named scheme shape, and successful availability
operations. Static assertions corroborate those control-flow facts; they were
not executed in this lane.

**Finite structural derivation:** for finite acyclic, binder-free live terms
made only of the polarized value atoms and pure Functions, a new comparison
with an initially empty typed-pair memo reaches exactly the recursively
specified value subpairs, modulo duplicate pair elimination and terminal
Bottom/Top shortcuts. It emits no effect-row mutation. This is a statement
about task decomposition and direct mismatch witnesses, not a denotation or
final acceptance theorem.

**Conditional reduction:** if a same-carrier interpretation of the actual
cyclic row obligations is supplied, erasing the matched pure effect leaves
leaves precisely the inequalities used by H4. That interpretation is still
unproved. H1 and H2 of the prior theorem remain assumptions: a reflexive
transitive preorder with total `Fun` satisfying the complete variance law,
and greatest `Top`. “Total” here means the constructor is defined on every
pair in the carrier; it does not mean all values are linearly comparable.

No established production-denotation theorem, independent review of this
note, intended source meaning, or implementation permission is claimed.

## Polarized representation ledger

Write `EB+` for `EffectBottomPositive`, `EE−` for `EmptyEffectNegative`,
and distinguish a row's positive and negative handles by `v+` and `v−`.

| Representation | Argument value | Argument effect | Result effect | Result value |
|---|---|---|---|---|
| Positive Function `P(a,ae,re,r)` | negative | negative | positive | positive |
| Negative Function `N(A,AE,RE,R)` | positive | positive | negative | negative |
| Positive pure `P₀(a,r)` | `a−` | `EE−` | `EB+` | `r+` |
| Negative pure `N₀(A,R)` | `A+` | `EB+` | `EE−` | `R−` |

`yu-types/src/lib.rs:585` and `:599` expose these different typed view
fields. Its positive/negative constructors at `:1822` and `:1881` validate
the corresponding handles and preserve field order; the arena views at
`:788` and `:822` return those fields. Positive effect views have only Bottom
and negative effect views only Empty (`:614`, `:618`).

`yu-solver/src/term.rs:1122` and `:1143` validate all four children's kind,
polarity, and arena lineage through `require_function_children` before
interning a Function. A negative Function with argument effect `EE−` and
result effect `EB+` is invalid. The printed abbreviation
`PureFun(A,B)=Function(A,EmptyEffect,EffectBottom,B)` names the positive pure
shape in the normative scheme; copying that tuple literally into a negative
Function is not a valid polarity erasure.

`closed_parts` at `yu-solver/src/lib.rs:14199` converts positive closed
Functions into `P₀` and negative closed Functions into `N₀` (`:14350`).
It checks the appropriate closed effect views, visits their IDs, and emits
the corresponding collected effect leaf handles in opposite orders for the
two polarities. Value child traversal and results are memoized by closed
handle. In general it flattens Union/Intersection children into part ranges
and builds Cartesian Function parts; that behavior does not establish a
union/intersection denotation. The named scheme has singleton ranges and
uses neither product expansion nor multiple-predicate routing.

## Exact named scheme and incoming-use reduction

F5 §23 records the same scheme for each member:

```text
Q = []
R = [r0]
predicate = P₀(Top−, P₀(Top−, r0+))
r0.lower = P₀(Top−, P₀(Top−, r0+))
r0.upper = Top−.
```

`f5d_productive_function_recursion_and_unproductive_names` at
`yu-solver/src/lib.rs:20476` contains this exact source. For both boxed and
flat candidate modes, it inspects every finalized member: zero Q, one R at
ordinal zero, Top upper, and two nested positive Functions in both predicate
and lower, each with Top argument and the pure effect leaves, ending at that
same R ordinal. The source fixture's definition uses are internal to the
recursive group; it does not itself execute an external incoming use of this
scheme. Incoming behavior is grounded separately in the actual route code.

For incoming occurrence `u` of either member, define

```text
ρu = the new live value-row ordinal for r0
cu = the exact occurrence's use_value_component row
Lu = P₀(Top−, P₀(Top−, ρu+)).
```

| Stage and source owner | Exact production operation | Semantic assignment still required |
|---|---|---|
| `route_incoming_inner`, `:14877` | Select target member's finalized scheme and exact use value component; structured predicate selects instantiation | Meaning of the consuming row as an observed target `U` |
| `instantiate_and_route_closed_inner`, `:14527` | Allocate no Q rows and one fresh value row for r0 at `use_level`; store ordinal→row substitution | One existential carrier value for that row |
| `closed_parts`, `:14199` | Both occurrences of r0 resolve through that substitution; positive r0 becomes `ρu+`; build `Lu` | Interpretation of positive Function and row handles |
| Bound lower restoration, `:14610` vicinity | Call `constrain_live_value(Lu, ρu)`; insert exact Function lower into `ρu` and replay existing uppers | `Fun(Top,Fun(Top,ρ)) ≤ ρ` |
| Bound upper restoration, same method | Call `constrain_live_value(ρu, Top−)`; typed pair is admitted, then Top shortcut causes no row-bound insertion | `ρ ≤ Top`, redundant if H2 holds |
| Predicate route, `:14647` vicinity, then `route` at `:15008` | Admit provenance fact with predicate term as lower and exact use component as upper; constrain `(Lu, cu)`; record structured route | `Fun(Top,Fun(Top,ρ)) ≤ U` |
| Route cleanup, `:14975` vicinity | Clear substitution and node memo maps for the next use; keep allocated rows as session owners | Fresh semantic instance per use, without accidentally sharing assignments |

Fresh row allocation (`:9550`) uses the current bounds length as a checked
ordinal and appends a default row. Scratch `clear` at `:7422` removes the
previous substitution entries. Thus successful distinct incoming attempts
allocate distinct row identities; repeated binder occurrences in one attempt
share the same row. No fresh effect row is allocated by this instantiation
path. The source code does not make a row denote an arbitrary element of a
semantic carrier merely by allocating it.

`apply_value_task` at `:12071` stores non-variable lowers in the receiving
row and replays exact uppers and direct upper rows. The bound restoration
stores `Lu` in `ρu`; the predicate route stores `Lu` in `cu`. Neither stage
replaces the predicate with `ρu`, nor does it create a direct `ρu→cu` row
edge. Fresh `ρu` initially has no upper; `ρu <: Top−` creates no upper bound
because `constrain_live` takes its Top terminal branch first. The graph still
has a cyclic exact structural lower: `ρu` occurs under two Function results
inside its own lower payload.

These are the three initial comparison tasks. Constraints already installed
on `cu` can cause additional replay tasks and diagnostics; this ledger does
not assert that the whole session contains only three tasks or no further
obligations. Extrusion can lower reachable row levels and follow existing
bounds. Any abstraction of those actions requires preservation evidence.

## Symbolic effect elimination and finite structural lemma

`constrain_live` at `:11059` admits a typed pair before decomposition, skips
already admitted pairs, and for a positive/negative Function pair emits,
in the following semantic field order:

```text
P(a,ae,re,r) <: N(A,AE,RE,R)
    value:  A+ <: a−
    effect: AE+ <: ae−
    effect: re+ <: RE−
    value:  r+ <: R−.
```

The children are prepended in reverse iteration to preserve processing order.
For pure Functions this becomes

```text
P₀(a,r) <: N₀(A,R)
    A+ <: a−
    EB+ <: EE−
    EB+ <: EE−
    r+ <: R−.
```

`apply_effect_task` at `:10853` has an empty branch for
`(BottomPositive, EmptyNegative)`. Both effect child positions name the same
typed pair key, so after its first admission the second is a duplicate.
Effects contribute no effect bounds or effect-row propagation here. This is
an actual code-path elimination of these two fixed leaves. It does not
establish the intended complete coupled Function/effect comparison law.

Define the finite polarized grammar

```text
p ::= Bottom+ | Int+ | P₀(n,p)
n ::= Top− | Bottom− | Int− | N₀(p,n).
```

All terms must be finite acyclic arena terms, validly owned, with no Q/R,
live value/effect rows, Component terms, Union, or Intersection. Define a
recursive Boolean task specification `B(p,n)` by

```text
B(Bottom+,n) = true                     for all n
B(p,Top−) = true                        for all p
B(Int+,Int−) = true
B(P₀(a,r),N₀(A,R)) = B(A,a) ∧ B(r,R)
all remaining cases = false.
```

For a comparison started with empty typed memo and worklist, and assuming
every allocation/accounting/diagnostic phase returns successfully, induction
on the sum of term heights gives:

1. Each nonterminal Function task visits the two value subpairs in this
   specification and the two fixed effect subpairs above.
2. The four false atom/head cases are exactly Int/Bottom, Int/Function,
   Function/Bottom, and Function/Int. They produce direct mismatch witnesses
   through `incompatible_value_shapes` (`:12343`) and memo admission.
3. Bottom-lower/Top-upper shortcuts stop that subtree; Int/Int performs no
   bound mutation (`apply_value_task` falls through). No value or effect row
   exists to replay, extrude, or mutate in this grammar.
4. Duplicate elimination collapses identical pair visits without changing
   which reachable pair keys are admitted. Every value child has smaller
   height sum, so the structural traversal is finite.

Consequently `B=false` iff some reached value pair receives a direct
`IncompatibleValue` witness; `B=true` iff none does. This lemma concerns
direct witness generation. It does not independently prove the complete
diagnostic SCC algorithm, its chosen canonical witness, or an end-to-end
module-acceptance criterion. The root comparison invokes diagnostic
completion and witness replay, described below. Finite `B` is not a relation
on every value of a shared carrier: in particular there is no positive Top
constructor, and its polarized grammar does not implement total `Fun` on an
arbitrary `D`.

For the actual incoming scheme, an upper on `cu` such as

```text
Nu = N₀(A0+, N₀(A1+, R−))
```

causes replay of `Lu <: Nu`. Its structural portion reduces to

```text
A0+ <: Top−       two fixed effect subpairs
A1+ <: Top−       two fixed effect subpairs
ρu+ <: R−.
```

The argument tasks are terminal Top successes. The effect positions reduce
as above. The last task is live and lies outside the finite lemma. Inserting
`R−` into `ρu` replays its stored `Lu` against `R−`; that can create further
structural tasks or a mismatch. This is the exact remaining cycle, rather
than a finite tree comparison hidden by the abbreviation `F²(ρ)`.

## Success, diagnostics, and availability

`constrain_live` returns `Result<usize, SolveAvailabilityError>`; the integer
counts summary transitions, not truth of a semantic comparison. A mismatched
value pair records a diagnostic witness and continues the worklist. At the
end it calls `complete_diagnostic_delta` (`:11474`) and `replay_witness`
(`:12048`), which reports an available completed incompatible witness through
`report_incompatible` (`:12367`). Function diagnostic child edges are recorded
for value fields; the fixed effect tasks here have no mismatch branch.

The test `f5b_function_decomposition_ages_variables_and_preserves_incompatible_rows`
at `:21313` explicitly unwraps a mismatched Int/Bottom comparison, checks the
bound rows unchanged, and then checks an appended `IncompatibleValue` error.
`f5b_all_incompatible_shapes_include_function_bottom_direct_and_derived_duplicates`
at `:22559` checks all four mismatch heads and unchanged bounds for each;
these assertions were read only. Thus an `Ok` route/comparison cannot be
identified with a diagnostic-free comparison or accepted source program.

The public `SolvedModule::solve` at `:15665` returns a module or an availability
error, while `errors()` at `:15674` returns the module's local diagnostics.
Source validity, diagnostic policy, and later program acceptance are separate
observations that this artifact does not characterize.

Only an error returned by the operation passed to `with_route_transaction`
(`:8723`) invokes that transaction's rollback; a successful operation commits
its route journal. Later outer instantiation-scratch accounting (`:14700`)
or resource sampling (`:14723`) can still return an availability error after
that commit, without the route transaction rolling back. This paragraph makes
no whole-`route_incoming` atomicity claim. Bad closed lookups/substitutions,
checked identity overflow, allocation, capacity accounting, or diagnostic
reservations can fail with availability errors. A local mismatch may still
return `Ok`; even reporting that mismatch can fail to reserve diagnostic
storage. The static
`f5c_incoming_diagnostic_reserve_failures_restore_and_retry` (`:29959`) checks
rollback and retry over its named reserve lanes. No exhaustive rollback,
availability-envelope, or public-publication proof was attempted here.

Additional static corroboration: `f5c_incoming_restores_recursive_lower_then_upper_with_q_before_r`
(`:28456`) checks separate lower/upper restoration counters, value freshening,
and zero fresh effect variables; `synthetic_identity_incoming_uses_accept_distinct_function_constraints`
(`:22750`) characterizes actual incoming substitutions on a synthetic
identity scheme. Those are different fixture shapes and are not execution
evidence for this exact cyclic scheme in this lane.

## Smallest residual H4 premise

For this specific one-use graph, a proposed remaining premise can be stated
without a global solver-completeness assertion. Supply a carrier satisfying
H1–H2 and a polarity interpretation in which both handles of one live row
refer to one value, `Top−` denotes its greatest element, and a pure polarized
Function denotes `Fun` with its recorded argument/result values. For every
admitted target interpretation `U`, require that the semantic relation of
the retained incoming obligations is exactly

```text
∃ρ∈D.
  Fun(Top,Fun(Top,ρ)) ≤ ρ
  ∧ ρ ≤ Top
  ∧ Fun(Top,Fun(Top,ρ)) ≤ U.
```

This is a **candidate one-use valuation premise**, not a proved meaning of
the solver's rows. It requires both directions: a semantic member instance
must give a single such `ρ`, and every such witness must represent an
admissible instance with no hidden obligation in that declared observation.
Any caller constraints represented outside `U` must remain explicit rather
than being dropped. No equality `ρ=F²(ρ)`, least solution, or coinductive
greatest solution is supplied by the stored lower bound itself.

Under this premise, put `F(t)=Fun(Top,t)`. The audited initial tasks translate
to `F²(ρ)≤ρ`, `ρ≤Top`, and `F²(ρ)≤U`; greatestness removes the middle clause.
This recovers exactly the production side used by the previous H1–H4
conditional theorem. The source audit eliminates uncertainty about predicate
direction, binder freshness, positive effect leaves, and the order of bound
restoration. It does not discharge the valuation premise.

For a theorem quantified over every `U∈D`, one additionally needs a meaning
for those targets beyond the restricted negative syntax or a justified
observation map covering them. The actual use row is a mutable constraint
owner, not by construction a literal arbitrary ground target. The cyclic
row's replay/level/memo discipline does not on its own define a total
constructor or a transitive semantic carrier. H1's Function law is consistent
with the pure finite task directions; consistency is not a proof of H1 or
H4 for production. The accepted non-composition boundary prohibits silently
extending this pure reduction to general concrete compatibility.

## Independence, coverage, and stop boundary

The production owner paths and candidate declarative rules are separately
located inputs. Their common semantic interpretation is the explicit
unproved premise above. There is no executable oracle, differential checker,
frozen Yulang2 run, seed, enumeration range, or mutation execution. No
checker-generated agreement is offered as proof of its own supplied rules.
Static tests share production assumptions and are corroboration of asserted
control flow, not an independent source-semantics oracle.

Coverage: the exact finalized two-member positive scheme, either selected
member and each isolated incoming allocation; the two polarized pure Function
constructors; the four emitted field tasks; the fixed effect comparison;
finite binder-free structural task traversal; and the named availability /
diagnostic distinctions. The symbolic live replay example isolates the cycle
without claiming to solve it.

No probe variants were attempted. The named shortcuts audited are swapping
negative effect ports, replacing the incoming predicate by its R binder,
treating `Ok` as acceptance, and treating a finite tree task specification as
live recursive denotation. Invalid handles or exhaustion invalidate the
successful-path characterization; extra caller constraints invalidate a
three-clause-only interpretation unless represented; non-pure effects,
Union/Intersection products, outer/free anchors, general SCCs, source roles,
source Apply, runtime observations, and final Oracle acceptance remain
unverified. No intended language meaning is reopened.

Recommended next action: give the frozen note a focused independent review,
then construct or refute the one-row existential valuation premise for this
exact cyclic graph and admitted target class. Increasing finite pure-tree
comparison counts would leave that premise untouched.

## Independent review

A read-only compiler-referee review found no blocking or major findings and one
minor precision issue. The rollback description has been narrowed to errors
returned by the transaction operation and now explicitly excludes later outer
accounting/sampling failures. The reviewer otherwise confirmed constructor
polarity, substitution/restoration/predicate routing, pure effect-leaf
elimination, finite-grammar bounds, and the remaining same-carrier valuation
premise. The review establishes no production denotation or acceptance
equivalence. No tests, builds, probes, or Git operations were run for the
text-only repair.

## Frozen dependency snapshot and checks

Direct dependency SHA-256 hashes, checked again before submission:

```text
ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd  rules/research-lab.md
9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29  rules/design-authority.md
e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e  rules/git-concurrency.md
1c826e88b59404d55dbf363081a784359304ef803aa458354385f4de0a90b22d  notes/design/INDEX.md
5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16  notes/design/2026-10-03-concrete-compatibility-boundary.md
781d719ef6ddd458908b61b7b95f49e4c6abec9ffed79595af5fe1e201caac83  notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed  notes/design/2026-09-29-scc-intrusion-redesign-charter.md
beb998aabe285ed026a04cddb90055a6ea579c463457a4f1639e1e6ffc019a73  notes/progress/2026-09-30-intrusion-pure-source-typing-rules.md
78d3a34508b7771701044b7b66d423ed0e7278cb52c9f9f368734bfb524cbdda  notes/progress/2026-09-30-intrusion-scc-constraint-scheme-rules.md
fea42929e591c160d8a92edcb4f103254fb2726feef0be58ca747fb7075cf84e  notes/progress/2026-10-06-rec-name-return-member-scheme-bridge.md
a3a920847b53e745ef17d43cf920c98a425e0d20c46b68524bd9c1d0b1a3fba5  crates/yu-types/src/lib.rs
12ddbeb759e82c753c1674fb204c7344bd781f5f570ef226ac3fdcd57c1a9611  crates/yu-solver/src/term.rs
a2103c6735d7a4efad00231f973544dda59d42219dbf83439fffc17889168e59  crates/yu-solver/src/lib.rs
```

Commands/checks: `cat` for the three rules and named prior note; bounded
`rg`/`sed` for the exact authority, constructor, route, task, diagnostic, and
test owners; `sha256sum` for direct inputs; final read-only Python check of
dependency hash equality and note newline/whitespace/conflict-marker
integrity. No tests, builds, executable semantic probes, formatting, Git
commands, or children. Large combined captures were truncated; narrower
follow-up reads supplied the named relevant owner slices. No claim to a
complete solver-file or whole-document audit is made.

Resource use: at most four simultaneous lightweight source-read shell
commands; zero compute probes, heavy processes, builds, or test processes.
CPU time, peak memory, and total wall time were not instrumented. The packet
provided no numerical CPU/memory/wall-time cap; static-only/no-probe and the
one-file output lease were enforced. No search was started or left running.

## Commit packet

* Exact leased path:
  `notes/progress/2026-10-06-rec-name-return-purefun-production-reduction.md`.
* Baseline SHA: `080dde430342a64ae1eab90c305e1a1f62bf8d77`, supplied by primary;
  primary must compare the pinned hashes with that baseline before integration.
* Changed dependency hashes: none during this lane; thirteen inputs above
  pin the frozen read snapshot. Unrelated branch movement was not inspected.
* Claim/review status: independently reviewed research-only source
  characterization, finite structural task derivation, and conditional
  reduction. H4, solver/source acceptance equivalence, and production
  authority remain open. One minor review finding was closed by narrowing the
  rollback claim; no semantic proof content changed.
* Checks already run: static owner and assertion reads; direct dependency
  hashes and final text/hash integrity check. No tests/builds/probes.
* Proposed one-line research-checkpoint commit message:
  `research: reduce pure recursive member use to polarized obligations`.
* Shared-record deltas intentionally left for primary/curator: record the
  negative pure port order, exact `Lu→ρu` / `Lu→cu` predicate obligations,
  pure-leaf effect elimination, successful-operation/diagnostic distinction,
  and open one-row valuation/target-realization premise. Keep prior H1–H4
  theorem conditional; no task/index/authority/theory/question file changed.

Writing and the one textual review repair are complete. The frozen artifact
remains research-only and conditional; any semantic expansion requires a new
explicit lease.
