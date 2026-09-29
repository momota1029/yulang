# Intrusion bounded-negative erasure counterexample

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Classification: conditional denotational counterexample; no Yulang semantics selected

## Claim

Under a subtype preorder with `Top ≰ Int` and Function subtyping

```text
Arr(A, R) ≤ Arr(A', R') iff A' ≤ A and R ≤ R'
```

a negative-only local argument `x` constrained by `x ≤ Int` cannot in general
be replaced by `Top` while preserving the candidate principal relation. The
constrained relation is `↑{Arr(A,R) | A≤Int}`. `Arr(Top,R)` belongs to
`↑{Arr(Top,R)}` by reflexivity. It cannot belong to the constrained relation:
membership would require some `A≤Int` with `Arr(A,R)≤Arr(Top,R)`, hence
`Top≤A≤Int`, contradicting `Top ≰ Int`.

This counterexample shows that the unconstrained negative-argument lemma cannot
be generalized by polarity alone. It is not an Oracle observation and does not
establish that the Oracle accepts or emits this exact selected graph.

## Frozen Oracle characterization

A temporary Rust source-path test against frozen Oracle `a58eefc3` used:

```text
my expect(x: int): int = 1
pub k x = expect x
```

The lowering completed without diagnostics. In `k`'s first compact view, the
Function argument includes `Int` and `TypeVar(16)`; that variable has an upper
bound record. At the saved `GeneralizedCompactRoot`, the argument contains
`Int` and no variable, and the public scheme is `int -> int`. This is
consistent with the frozen Oracle compactor expanding negative variables
through upper bounds before one-polarity elimination, but this source graph is
not proven identical to the abstract counterexample above.

Probe command:

```text
cargo test -p infer scratch_oracle_saved_bounded_negative_projection -- --nocapture
```

One focused test passed, including an assertion that lowering produced no
diagnostics. Its temporary instrumentation and test lived only in
`/tmp/yulang-intrusion-bounded-arg-probe` and were removed after capture. The
frozen Oracle worktree was not modified. The proof must still compare the
candidate's selected-obligation relation with this ordered Oracle projection;
deleting a bounded variable directly is not a valid shortcut.

Independent `compiler_referee` review verified the counterexample under the
stated preorder and Function rule. Independent `spec_auditor` review confirmed
that its scope is conditional and it makes no Oracle-semantic decision. Neither
review establishes the source graph or the general root-projection theorem.

## Restricted correspondence result

A conditional path theorem is now recorded in the abstract semantics draft.
It covers a pure acyclic structural root `Arr(x, R)` with one negative
occurrence of `x`, a successful projection query whose sole effective input is
one direct concrete upper atom `U`, eligible one-polarity elimination, and
later passes that leave `U` and `R` unchanged. If the candidate separately
stipulates `{A | A ≤ U}` as the nonempty admissible assignment set with greatest
element `U`, both paths produce the same root denotation, `↑{Arr(U,R)}`.

This statement was reviewed conditionally by a `compiler_referee` and
`spec_auditor`. A subsequent semantic review confirmed the interval lemma below
and required further precision for the Oracle-path premise. The draft now
requires a successful per-root projection/restart, a non-bipolar occurrence
census with no other relevant occurrence, the actual level/non-generic
elimination checks, and evidence that the complete retained argument after
merging the self variable and projection input denotes exactly `U`; all later
passes must preserve that argument and `R`. The exact assignment fiber
`{A | A ≤ U}` remains a separate denotational premise. The `expect`/`k` probe
is only an observed `U = Int` path consistent with these conditions. The
structural root `Arr(x,R)` is not claimed to be the complete compact graph:
Oracle's `compact_var_side` merges the source-variable occurrence with its
projected bound before elimination. This is one restricted interpreted-root
correspondence, not diagnostics, later-member state, incoming-use simulation,
Gate C closure, or Oracle equivalence for the source graph family.

The draft now also records a reviewed interval extension of the pointwise
extremal lemma. In a fixed fiber where the admissible assignments are exactly
the nonempty interval cut out by finite lower and upper bounds, the meet of the
uppers is the greatest admissible assignment; compatible lower bounds do not
change the projected root. This still assumes the exact selected fiber and
does not derive it from Oracle evidence or cover shared-variable dependencies.

The selected-edge corollary now derives that exact fiber for a restricted
already-selected graph: after fixing anchors and every other local vertex, all
edges mentioning `x` must be fixed-endpoint inequalities into or out of `x`,
and every other obligation must be independent of `x`. Its nonempty fiber then
has the upper-endpoint meet as maximum, so a negative-only `Arr(x,R)` projects
fiberwise to that meet. A compiler referee found no blocking/major issue and
requested two premise clarifications, now applied: omitted obligations must be
syntactically x-free, and finite meets include the empty meet `Top`. The result
does not establish Oracle evidence selection or global principal-view
representability.

The Oracle's collector/finalizer path for the conditional sole-`U` case is now
audited against frozen `a58eefc3` Rust source and independently reviewed by a
`compiler_referee`. In negative SchemeProjection, the scoped view exposes its
generalized upper records; the collector folds them with negative merge,
compacts a direct concrete constructor, then merges the original `x`
occurrence. The one-polarity pass removes `x` only when the boundary,
non-generic, and root/recursive-bound/role polarity checks allow it. Negative
Function argument finalization preserves the singleton concrete `U`. The
review found no issue in this derivation for the stipulated sole-`U` fragment.
This explains the Oracle side of that conditional path; it still assumes the
query view contains exactly the stipulated record and later passes retain the
result. The source program's creation of that view and saved-root stability
remain the general bridge to prove.

The concrete `expect`/`k` source construction is now traced through the frozen
Oracle Rust lowering and constraint path. The annotated `int` parameter goes
through `connect_parameter_computation_detailed` to `connect_value_detailed`,
which inserts both `Int <: expect_param` and `expect_param <: Int`. Application
lowering inserts `expect_value <: Arr(k_arg, result)`, and Function
decomposition derives the contravariant argument obligation
`expect_param_inst <: k_arg`. Instantiation clones the finalized scheme and
routes its predicate through the direct-lower or subtype insertion path. Given
the finalized scheme's annotated argument relation, these constraints derive
`k_arg <: Int`. A compiler-referee review accepted this as a conditional
source derivation and emphasized that the scheme premise must be backed by the
actual probe. Together with that probe, this closes the source-construction
bridge for this one `U = Int` fixture. It does not establish the selected
scoped query record solely from source code, prove the result for a family of
schemes, or show that restarts and post-loop passes preserve the result in
other fixtures.

The selected-graph fiber analysis now includes a reviewed acyclic upper-alias
chain case. With only `x = v0 ≤ v1 ≤ ... ≤ vn ≤ U` involving the path
vertices, fixed `U`, and a fixed satisfying assignment for all other locals,
the projected feasible set for `x` is exactly `{a | a ≤ U}`; assigning each
intermediate to `U` proves sufficiency. The negative-only Function root then
projects to `Arr(U,R)`. A compiler referee found no blocking or major issue and
requested that the other-local assignment be explicit; the draft now states
it. This is still only a selected-graph theorem: no Oracle evidence selection,
alias collector behavior, source correspondence, or saved-root stability is
proved for the chain family.

The frozen Oracle supports one corresponding unweighted chain through solver
replay. Propagating `x <: y` records `x` as a lower of `y` and `y` as an upper
of `x`; inserting `y <: U` replays the lower/upper pair at `y` and derives the
direct upper `x <: U`. The synthetic test asserts that projected upper on `x`,
then runs the full root generalization path for a positive Function with
negative-only `x` argument and observes only `U` in the saved argument. The
compiler-referee review found this source explanation consistent with the
bounded characterization and requested a direct intermediate assertion; that
assertion now passes. The collector alone still retains a bare `Neg::Var`
upper endpoint as a secondary occurrence, and positive alias expansion does
not run in a negative Function argument. The correspondence therefore relies
on upper replay materializing `x <: U` before compact projection.

Test command in isolated frozen checkout `a58eefc3`:
`CARGO_TARGET_DIR=/tmp/yulang-intrusion-oracle-target cargo test -p infer
scratch_negative_argument_alias_chain_projection -- --nocapture`. It is a
synthetic unweighted, acyclic, isolated chain with unknown internal origins,
all vars at `root.child()`, and a quantification boundary one level below;
the root compacts to a Function argument containing exactly `Con(U)`. It does
not prove source-level reachability, weighted/shared/cyclic path behavior,
arbitrary environment anchors, root-order simulation, diagnostics, or
principal-solution equivalence for a broader graph class. Source locators in
the frozen checkout: `constraints/machine/propagate.rs:104-145`,
`constraints/machine/bounds.rs:815-909,3582-3645`,
`compact/collect/mod.rs:746-844,945-979`,
`compact/analysis/mod.rs:41-59,506-515`, and
`generalize/mod.rs:75-134`.

The candidate fiber result now covers a family of independent upper-alias paths
from one negative-only root variable `x` to fixed endpoints `U_j`. With no
other obligations incident to the disjoint path intermediates and all other
locals fixed in a satisfying assignment, the exact feasible projection is
`{a | a ≤ U_j for every j}`. If the carrier has finite meets, its greatest
element is `∧_j U_j`, so `Arr(x,R)` projects to `Arr(∧_j U_j,R)`.

A second isolated frozen-Oracle Rust probe characterizes two length-two paths:
`x ≤ y ≤ U1` and `x ≤ z ≤ U2`. It asserts upper-bound replay creates both
direct projected uppers on `x`, the generalized compact Function argument has
no local variables and exactly the two endpoint constructors, and finalized
scheme output has a `Neg::Intersection` with one `U1` and one `U2` child in
either order. A compiler referee reviewed the mechanism and graph scope. It
initially found a finalization assertion that could accept duplicate endpoints;
the assertion was strengthened and the focused test rerun successfully. No
blocking or major review finding remains for this topology. The reviewer notes
that the test demonstrates scoped selection indirectly through the final
compact output, not by inspecting selected record IDs.

Focused command in the isolated frozen checkout `a58eefc3`:
`CARGO_TARGET_DIR=/tmp/yulang-intrusion-oracle-target cargo test -p infer
scratch_negative_argument_two_alias_paths_meet -- --nocapture`. This remains a
synthetic unweighted case with separate intermediate vars at `root.child()`,
unknown internal origins, and a quantification boundary one level below. It
does not establish a source witness, weighted/shared/cyclic paths, arbitrary
anchors, later-root behavior, diagnostics, or general principality. The temp
test worktree is removed after evidence capture; frozen Oracle remains clean.
Source locators: `constraints/machine/propagate.rs:104-127`,
`constraints/machine/bounds.rs:888-909,3582-3645`,
`compact/collect/mod.rs:816-845`,
`compact/finalize.rs:415-425,802-820`, and
`compact/analysis/mod.rs:41-57,506-515`.

A third isolated frozen-Oracle probe characterizes one shared-join diamond:
`x ≤ left`, `x ≤ right`, `left ≤ join`, `right ≤ join`, `join ≤ U`. It asserts
replay creates a direct projected `x ≤ U` record, the generalized compact
negative Function argument contains exactly `U` and no variables, and the
finalized scheme argument is exactly `Neg::Con(U)`. For the candidate graph,
the fiber is `{a | a ≤ U}`: transitivity proves necessity and assigning
`left = right = join = U` proves sufficiency. A compiler referee found no
blocking or major issue for this bounded output characterization. The reviewer
emphasized that the final output does not prove both replay routes or the
shared-join identity survive as separate evidence; either route could produce
the same result. Therefore this characterizes one diamond's output only, not
general shared-DAG behavior.

Focused command in isolated frozen checkout `a58eefc3`:
`CARGO_TARGET_DIR=/tmp/yulang-intrusion-oracle-target cargo test -p infer
scratch_negative_argument_diamond_alias_projection -- --nocapture`. As with
the alias-chain probes, the graph is synthetic and unweighted, all local vars
are at `root.child()`, and the quantification boundary is one level lower. It
does not establish source reachability, path-specific provenance, additional
incident constraints, weights, cycles, anchors, later-root simulation,
diagnostics, or principality. Temporary test worktree removed; frozen Oracle
is clean.

The candidate selected-graph proof now covers a finite upper-reachability graph,
not just isolated paths. For finite edges `u ≤ v`, upper endpoints `v ≤ U`, and
fixed lower endpoints `L ≤ v`, define `M_v` as the meet of all upper endpoints
reachable from `v`, with `Top` for none. Under a fixed outer fiber where all
independent obligations hold and assuming graph feasibility, every solution
has `nu(v) ≤ M_v`; a feasible witness proves each lower `L ≤ M_v`; and edge
reachability gives `M_u ≤ M_v`. Thus `v ↦ M_v` is a satisfying pointwise
greatest assignment, even with shared vertices or cycles. A compiler referee
reviewed and accepted the finite-bound, outer-fiber, and greatest-versus-exact-
fiber premises. For a Function root `Arr(x,R)` with fixed `R` and sole negative
`x`, contravariance yields the projected denotation generated by `M_x`.
This is candidate semantics only: Oracle selection, replay closure, and compact
projection for arbitrary such graphs remain unproved.

Source locators in frozen Oracle `a58eefc3`: `lowering/expr/lambda.rs:674,
1244-1280`; `annotation/constraints.rs:124-136,251-281,771-793`;
`lowering/expr/tail.rs:94-124,535-566,630-646`;
`constraints/machine/propagate.rs:213-244`; and
`analysis/session/instantiate.rs:385-519`.

Source locators in the frozen checkout: `compact/collect/mod.rs:166-183,
746-782,816-846,952-976,1132-1155`,
`constraints/structural_kernel/access/legacy_read_view.rs:225-235`,
`compact/analysis/mod.rs:41-58,506-513`,
`compact/analysis/occurrence/substitution.rs:109-130`,
`compact/finalize.rs:136-176,415-425,802-825`, and
`compact/collect/type_nodes.rs:104-119,175-190`.

An attempted scratch Rust source-path probe for a nested captured polymorphic
function application, `pub outer(f: 'a -> 'b) = my inner x = f x; inner`, did
not complete. In an isolated detached worktree at frozen Oracle `a58eefc3`,
`cargo test -p infer scratch_intrusion_anchor_argument_application --
--nocapture` remained inside `prepare_cold` for over 90 seconds at nearly one
CPU core and was interrupted; a second run with `timeout 20s` also timed out
before leaving `prepare_cold`. No diagnostic or type result was observed. The
temporary test and worktree were removed, and no frozen Oracle files changed.
This is not evidence about the source program's type or language acceptance;
do not use it as a fixture or repeat it without a bounded execution plan.

## Oracle alias-cycle probe

An isolated frozen-Oracle probe characterizes one two-variable alias cycle:
`x ≤ y`, `y ≤ x`, `y ≤ U`. It asserts replay creates a direct projected
`x ≤ U` bound, generalized compact projection removes both local variables
and contains exactly `U`, and finalization produces exactly `Neg::Con(U)` in
the negative Function argument. In the candidate graph, `x ≤ y ≤ x`
identifies the two values in the subtype preorder, so the projection onto `x`
is `{a | a ≤ U}`. A compiler referee found no assertion flaw for this narrow
output claim. The Function is only an acyclic wrapper; the cycle itself
contains variable aliases, so this does not characterize productive recursive
Function SCCs. It also does not establish selected scoped-record identity or
behavior for broader cyclic graphs.

Focused command in isolated frozen checkout `a58eefc3`:
`CARGO_TARGET_DIR=/tmp/yulang-intrusion-oracle-target cargo test -p infer
scratch_negative_argument_alias_cycle_projection -- --nocapture` (1 passed).
Source locators: `constraints/machine/propagate.rs:104-131`,
`constraints/machine/bounds.rs:888-900,3582-3645`,
`compact/collect/mod.rs:816-845`, `compact/analysis/mod.rs:41-57`, and
`compact/finalize.rs:415-425,802-820`. The temporary test worktree was removed;
the frozen Oracle checkout remains clean.

## Oracle anchored alias/lower probe

An isolated frozen-Oracle Rust test characterizes the synthetic graph
`l ≤ e`, `l ≤ x`, `x ≤ y`, `y ≤ x`, `y ≤ e`, with `l` and `e` registered at
the outer level and `x`,`y` initially one level inside. It checks that a
successful `scheme_projectable_lowers_in_scope` query selects the exact
`PosId` for `l ≤ x`, and the same scoped view exposes upper endpoint `e` for
`x`. The solver lowers `x` and `y` to the outer level. Generalization then
retains `x`,`y`,`e` in the compact and finalized negative Function argument,
with no local quantifiers; `l` is absent from that negative argument. Under a
fixed outer assignment satisfying `l ≤ e`, the selected graph's projection
onto `x` has greatest value `e` (assign `x = y = e`).

An independent compiler-referee delta review closed the earlier vacuous
quantifier and mistaken nominal-lower assertions. It confirmed this is only a
synthetic current-path characterization: lower selection and upper-anchor
visibility coexist in a successful scoped query, while final argument
retention follows the upper alias path. The test does not show lower evidence
is transported into the final argument, that it causes retention of `e`, or
that provenance is carried through an intrusion parent map. It also has no
source-level witness, diagnostics-path assertion, or later-root stability
claim.

Focused command in isolated frozen checkout `a58eefc3`:
`CARGO_TARGET_DIR=/tmp/yulang-intrusion-oracle-target cargo test -p infer
scratch_negative_argument_alias_path_to_outer_anchor_with_lower -- --nocapture`
(1 passed). Frozen-source locators: lower selection in
`constraints/structural_kernel/access.rs:862-890`, upper-record visibility in
the same file `:897-905`, negative scheme collection in
`compact/collect/mod.rs:833-845,941-949`, and quantifier selection in
`generalize/mod.rs:900-915`. Temporary test worktree removed; frozen Oracle
remains clean.

## Next action

Find a source-level witness for the anchored lower/upper graph, or establish
which source restriction prevents that graph shape. Trace its selected lower
decision and retained outer identities through root preparation; separately
prove lower-evidence transport if the replacement representation needs it.
The general denotation, ordered root simulation, use simulation, and
implementation gates remain open.

## Source-level anchored alias probe (2026-09-30)

An isolated temporary test was added to a detached worktree of frozen Oracle
`a58eefc3`, in `crates/infer/src/lowering/tests/case_05.rs`, and passed once
after its final assertions. The source is:

```yulang
my outer(l: int, sink: 'e -> int) =
  my inner(x, y) =
    sink x
    inner y x
    inner l y
    1
  inner
```

The first post-lowering probe was misread: an `x` lower endpoint `y` and a `y`
upper endpoint `x` are two views of the same inequality `y ≤ x`, not opposite
alias directions. There is no evidence for a cycle in this source. This
correction supersedes the earlier sentence claiming both raw directions.

An initial temporary hook in `lowering/expr/tail.rs::generalize_local_binding`
ran an auxiliary scoped query immediately before `inner`'s generalizer. It
found `x=TypeVar(18)`, `y=TypeVar(19)`, `l=TypeVar(2)`, `sink=TypeVar(4)`,
selected lower records 47 (`y ≤ x`), 84 (`l ≤ x`), and 94 (`int ≤ x`) for
`x`, and upper records 37 (`x ≤ e`), 48 (`y ≤ x`), and 56 (`y ≤ e`). This was
not the generalizer's own query and must not be described as its edge
selection.

A second instrumentation moved observation into the actual
`compact/collect/mod.rs` scheme collector. At `inner`'s compact root, both
arguments occur in negative polarity, so the collector queries upper records:
for `x`, it visits record 37 (`x ≤ e`); for `y`, it visits records 48 (`y ≤ x`)
and 56 (`y ≤ e`). It makes no lower-projection query for `x` or `y` at this
root. The resulting compact function arguments contain `x` with `e`, then `y`
with `x` and `e`; `l` is absent. Witness capture for this root records
`BoundRecordId(37)` at the FunctionArgument path as the UpperBound witness
(alongside the root's bound record 273). It does not record lower records 47,
84, or 94. The lower-query trace for those records occurs later in the test;
given the source lowering order it is consistent with the enclosing `outer`
generalization, but this trace does not tag each collector call with its root.
Thus this source fixture reaches the
anchored lower in the solver, but it does not show that lower entering
`inner`'s negative argument projection or being transported into that saved
root. This is the key distinction needed for the intrusion proof.

The environment-gated test and instrumentation were confined to a detached
Oracle worktree, then removed; frozen `a58eefc3` remained clean. Focused
command:
`YULANG_INTRUSION_TRACE_INNER=1 CARGO_TARGET_DIR=/tmp/yulang-intrusion-oracle-target
cargo test -p infer scratch_inner_generalization_boundary_trace -- --nocapture`
(1 passed). The captured trace directly observes collector record IDs,
polarity, compact root, and witness drafts. It is a source-to-Oracle-view
characterization, not a proof of evidence transport, parent semantics, or
root/use simulation.

## Positive-result lower projection source probe (2026-09-30)

To put an outer lower endpoint in positive polarity, the source body was
changed to:

```yulang
my outer(l: int, sink: 'e -> int) =
  my inner(x) =
    sink x
    inner l
    x
  inner
```

The focused Rust test resolves the source `l` parameter and asserts its solver
identity is `TypeVar(2)`. Actual scheme-collector instrumentation records a
positive-polarity query for the Function result variable `TypeVar(24)` while
building `inner`'s compact root. It returns replay-qualified lower records:
136 (`TypeVar(18)`, the `x` identity), 138 (`TypeVar(2)`, the source `l`), and
140 (`int`), as well as auxiliary local endpoints 132 (`TypeVar(38)`) and
134 (`TypeVar(36)`). The compact
Function result stores `TypeVar(24)` as primary and retains `TypeVar(2)` and
`Int` among its secondary lower components. The formatted schemes are
consistent with the enclosing `'a` remaining shared:

```text
inner = ('a & 'b & 'c & 'd & 'e) -> ['f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q] 'e | 'd | 'c | 'a | 'r | int
outer = ('a & int) -> (('a | int) -> ['b] int) -> 'a -> ['b] 'a | int
```

These strings are printed observations, not expected-value assertions; the
AST-to-TypeVar assertion and compact-root trace identify the `l` occurrence
directly. Witness capture omits lower record 138 (and 140): its existing
top-level Function path deliberately traverses only the root argument, not
the root return. This omission is separate from compact-root collection and
does not undo the observed lower inclusion. The replay-qualified records do
not establish direct source provenance or a complete parent-transport proof.
Independent compiler-referee review confirmed the polarity and record
interpretation and this witness-coverage limitation.

Focused command in the isolated worktree:
`YULANG_INTRUSION_TRACE_INNER=1 CARGO_TARGET_DIR=/tmp/yulang-intrusion-oracle-target
cargo test -p infer scratch_inner_generalization_boundary_trace -- --nocapture`
(1 passed). This probe advances source-to-compact characterization for a
positive Function result. It does not establish equivalence with the
intrusion candidate, principality, finalization/use simulation, or the broader
Oracle capability envelope.

## Conditional finite lower-graph lemma (2026-09-30)

The abstract-semantics draft now states the lower dual of its finite
upper-graph projection theorem. For a finite selected graph with variable
edges `u ≤ v`, fixed lower endpoints `L ≤ v`, and fixed upper endpoints
`v ≤ U`, define `J_v` as the join of every lower endpoint that reaches `v`
along variable edges. Under a carrier with finite joins including `Bottom`, a
satisfying witness shows `J_v` obeys every fixed upper; join and edge
monotonicity show it satisfies every lower and variable edge. It is therefore
the pointwise least satisfying assignment. A standalone positive variable
root `v` has upward denotation `↑{J_v}`.

An independent compiler-referee review checked edge direction, the upper-bound
argument, cycles, and the denotation equation; it found no issue within the
stated assumptions. This is conditional graph algebra, not proof that Oracle
selects this graph or that its result applies directly to a Function root.
The positive source fixture has a shared variable in both Function argument
and result positions plus recursive/effect endpoints, so its full member-root
denotation still requires coupled polarity reasoning. No compiler code or
tests changed for this lemma.

## Next action

Extract the full selected graph for the positive source fixture and state its
mixed-polarity Function-root denotation, preserving the shared argument/result
identity and outer `l`. Then compare that relation against parent intrusion
through finalization and independent uses. The finite lower lemma is only a
single positive-variable fiber and does not discharge this coupled case.
Ordered root simulation and the general denotation proof remain open;
implementation remains gated.

## Mixed-polarity relation setup (2026-09-30)

The abstract-semantics draft now records the candidate joint relation induced
by the compact trace, with `x` shared between `Arr` argument and result paths,
`r` as the result root, `a,b` as local replay endpoints, and outer `e,l` fixed:
`x ≤ e,a,b,r`, `a,b ≤ r`, `l ≤ r`, and `int ≤ r`. The duplicate `x ≤ r`
record is one edge. This makes the coupling explicit and rules out reasoning
from independent argument/result fibers. The lower records are replay-qualified,
so this remains conditional: the trace does not establish completeness of that
selected graph or direct source provenance. The Oracle formatted schemes are
still observations, and no principal representative has been proved.

The abstract graph's joint image is now reduced algebraically: `a` and `b` can
be existentially eliminated, leaving exactly
`{ Arr(x,r) | x ≤ e, x ≤ r, l ≤ r, int ≤ r }`. Necessity follows by
transitivity; sufficiency sets `a = b = x` and uses reflexivity. This preserves
the shared `x` and outer anchors. It is a graph projection fact, not evidence
that Oracle's saved root has this denotation. Next compare it with the
compact/finalized root, then carry the same source-identity map through two
independent incoming uses. Do not infer a Function representative by combining
the marginal least argument and greatest result. No Python model is used as
evidence; the only runtime characterization cited here is the focused
Rust-path Oracle probe above.
