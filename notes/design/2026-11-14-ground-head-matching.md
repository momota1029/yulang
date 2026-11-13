# Ground-root termination from actual head matching

Date: 2026-11-14. Status: proved for the ground-root boundary stated below.
Integration baseline: `68580451a5cb61b38fccde899ee47d83fc29fc86`.

This closes the remaining producer in §5 of
[the normalized capture assembly note](2026-11-14-normalized-capture-assembly-progress.md).
The Step relation, checked declarations, inspection algorithm, emission,
normalization and existing guards are unchanged.

## 1. Closed statements and exact source class

`GeneralNominalGroundHeadMatching.reachable_head_matching` constructs
`ReachableHeadMatching roles registry context root` with no hypothesis.
Its local producer, `packet_matching`, applies to any actually prepared packet
with current model satisfaction, shared generation, finite input labels and
constructor/interpretation agreement. It does not need to assume reachability
or the actual-position K2 guard separately.

`ground_class_p_accessible` proves

    Checked registry → InitialSource registry context root →
    PointSource context root → GroundRoots context root rootLabels →
    Acc (fun next current => Step registry root current next)
        (initial context root).

Here Step is exactly `GeneralNominalActualInspectionSteps.Step`.
There is no remaining producer, installation-order, finite-cover, source-budget,
or depth hypothesis. GroundRoots supplies a fixed finite closed Pattern label
for each unnamed root input whose meaning is the same in every source model.
This is the existing ground-root boundary, not arbitrary point inputs with
unknown holes or merely a model-dependent family of unbounded finite terms.
The registry is arbitrary subject to the existing Checked predicate: no new
restriction on compound heads, role arity, where-child syntax, associated
outputs or output-only binders is added.

A stronger wrapper, `ground_point_root_accessible`, requires only literal
pointness of each **root argument**; it does not require all initial internal
intervals to be point pairs. The remaining premises are Checked, InitialSource
and GroundRoots. Thus strict intervals elsewhere in a source are covered when
its root still satisfies this ground point boundary. General nonpoint roots
and roots with unknown meanings remain outside these statements.

The separate theorem `installed_depth_bound` gives the explicit bound

    InstalledDepthBound registry context root (mass rootLabels).

It uses InitialSource, point root endpoints and GroundRoots. Checked registry
is needed by the existing finite installation/administrative accessibility
reduction, not by this local ancestry bound.

## 2. Simultaneous positional invariant

For one query/subtree pair the new `Input` predicate carries:

1. A source Pattern witnessing `ClosedTerm context pattern term`.
2. `Fits` between the actual pair of inspection slots and the finite term's
   denotation in the current model.
3. For every retained optional origin, an exact actual meaning at that origin
   equal to this same denotation.

`InputsAt` aligns a whole interval list with finite terms and the real origin
function at its current inspection offset. Capture occurrence inclusion is a
separate invariant: every capture in the current recursive report belongs to
`inheritedReport packet`. It does not identify intervals by overlap, endpoint
values or a chosen representative inside the interval.

`inspect_matched` and `many_matched` are simultaneous well-founded recursions
on the actual query syntax/list size. Their conclusions are `Matches` and
`Aligned (Matches ...)` for the existing `CapturedPart` relation. They consume
completion of the actual inspection and the positional invariant above.

### Completion, arity and supported variables

`inspect_status` / `many_status` prove that blocked positions, conflicts and
arity errors are independent of the origin parameter. Consequently
`finished_origins` transfers Prepared's original report completion to the
inherited report. Completion of an appended report implies completion of both
reports; `finished_length` recovers exact query/interval list alignment,
including empty and nullary cases.

`translated_single` derives singleton variable capture queries from the
checker's coverage certificate for the normalized declaration head. It handles
flattened/sorted record payload positions and the variant translation shortcut.
It imposes no additional condition on the registry. Deferred queries remain
possible syntactically, but Finished excludes their execution branches.

### Variable positions

For an optional origin that is present, `variable_match` uses the source
Pattern and exact local origin meaning. The occurrence-inclusion invariant
puts this precise capture in the original inherited report.
`recorded_capture_part` then transports its meaning to the usable representative
through `Captured.2`. The local occurrence itself need not be proved Usable.
The agreement certificate quantifies over **all** report occurrences of the
same variable, including both nominal endpoint reports and repeated head
positions.

If the origin is missing and the variable is Needed, the existing generation
guard produces a usable representative. Its capture certificate would require
this very occurrence to have a present origin, a contradiction. If the variable
is unused by the where-children, its closed subtree is sufficient for
CapturedPart; the identity capture costs one and the finite subtree has
positive weight. No missing-origin guard was added.

### Structural positions

Finished yields the actual lower and upper structural head observations and
agreement of their shapes with the query. `structural_inputs` applies the
previous turn's `structural_interval`: the finite input has exactly this
constructor, and each finite payload fits the corresponding pair of real
child slots. This applies to strict structural intervals as well as point
ones, and includes canonical record signatures and exact-empty distinctions.

The paired child interval list is related to the actual zip of the two endpoint
child arrays, allowing different observation shape IDs for the same shape.
`closed_child` reifies the finite child using the parent source Pattern, so
constructor keys are inherited, not recovered by choosing catalogue inverses.
`retained_child` projects a present parent origin through the exact constructor
position. If the parent origin is absent, structural descent retains absence.
The recursive list proof consumes these same intervals, origins and finite
children, with the offset advanced exactly once per position.

### Nominal positions and both endpoint reports

The nominal carrier is invariant. `nominal_finite` proves that a nominal value
below a closed finite term has the same nominal name and arity, and is equivalent
to the entire finite term. Its proof handles the root directly, so it includes
nullary nominals. `descriptor_finite` combines this with the actual descriptor's
Denotes witness and typeArguments inversion. It produces the finite children,
an exact meaning for the endpoint source, and Fits for every finite child in
the descriptor's own argument interval. Arbitrary row parameters cannot slip
through: successful typeArguments recovers precisely the list of type intervals.

`nominal_inputs` preserves the inherited parent origin when one exists. With
no inherited origin it resets to the actual lower endpoint source, whose exact
finite meaning was just proved. Both cases project the same finite children.

For distinct endpoints, `both_nominal_inputs` also derives the corresponding
upper traversal. Unpacking the two Denotes witnesses and composing the input
Fits yields a value between two nominal endpoints. The existing
`nominal_sandwich` proves equivalence with both endpoints. The theorem constructs
both finite child lists, each with its real argument intervals and its correct
inherited-or-endpoint origin function, and with the **same parent term**.
This is semantic equivalence in the current model, not equality of source IDs.

The syntactic matching derivation uses the lower report once. `nominal_left`
extracts it only from completion of the full inspector, and proves its captures
are included in that full report. When the endpoints differ, both reports must
be complete. Counting both reports as two syntax trees would duplicate the
same declaration positions; instead the full Usable agreement certificate
controls every repeated capture, while Matches has one node per syntax
position. The separate both-endpoint theorem validates the common finite
meaning without duplicating the matching cost.

## 3. From actual packets to accessibility

`packet_matching` supplies every premise of the simultaneous recursion:

* Installable supplies Prepared and the exact located interval list. The
  existential Prepared bounds equal the packet bounds by functionality of
  argument location.
* Current Models transports to the packet's actual context via Installable's
  context equality.
* A nonempty requirement list supplies checked coverage of the normalized
  head. This is the same condition needed by the old assembly interface.
* Inputs supplies one finite term per root position. `locate_sources` ties
  each actual inspected slot pair to the corresponding demand argument pair.
  The original retained-origin entries provide exactly the optional-origin
  clause of the positional invariant.
* The full inherited report contains all of its captures. Its completion,
  positional alignment and singleton capture property are established above.

The matching output is aligned back to the complete normalized source head
and the original input-label list. Only constructor and interpretation fields
are transported between the packet context and the original label context;
no equality of their evolving source snapshots is assumed.

This proves ReachableHeadMatching, and the existing `assembly_of_matching`
now gives `normalized_capture_assembly` without a producer hypothesis. The
previously proved child assembly and conservative instantiated Paterson
inequality then give, along every actual ancestry edge,

    mass(child labels) < mass(instantiated normalized head)
                       ≤ mass(parent labels).

Retrospective labels may depend on the model. The established trace induction
restricts a later model to earlier states and carries the same local inequality;
it yields depth + current-label mass ≤ root-label mass. Actual model existence
at installation supplies the depth bound for installing packets. The existing
finite invocation/allocation/report and administrative-step reductions finish
Acc from Checked and InitialSource. No new ranking assumption is introduced.

## 4. Show sanity instance and remaining boundary

`GeneralNominalGroundHeadMatchingExample.show_pair_list_int_accessible`
instantiates the general ground Class P theorem with the existing Show fixture
for `pair (list int) int`. `show_depth_bound` specializes the general bound to
4, the checker's mass of this closed root label. `inhabited_ground_instance`
packages Checked, InitialSource, PointSource, GroundRoots, an actual source
model, and accessibility. This instance uses no fixture-specific branching or
peeling accessibility theorem. It proves termination/accessibility, not
construction of a completed Show dictionary or a new execution trace.

No semantic or implementation obstruction was found, and no guard repair or
owner decision was required. The requested ground-root target is closed. The
full Class P target with unknown source holes still requires its genuine
elimination/producer simulation; unrestricted B4(1) is not claimed here.

## 5. Proof ownership and checks

The yulang-proofs skill was used. The host has no registered callable prover
role, and the checkout has no prescribed prover routing configuration. The
primary constructed the derivations directly; no prover agent ran. A separate
reviewer inspected the original producer boundaries and all final theorem
quantifiers, including both endpoints and the stronger point-root result,
and found no blocking issue. The reviewer independently ran the standalone
audit and printed the final theorem/fixture types, both with exit code 0.

All six new modules are imported by appended lines in `lean/Yulang.lean`.
The new standalone audit is `lean/Audit/GroundHeadMatching.lean`. Earlier Lean
files, the frozen audit and README, specification, planning notes, lake
configuration and git refs are unchanged. Final validation is recorded below.

Commands run with working directory `lean/`:

| Command | Exit code | Result |
| --- | --- | --- |
| `lake build Yulang.GeneralNominalGroundHeadMatchingExample` | 0 | All six new modules built transitively; 799 jobs. |
| `lake build Yulang` | 0 | Full aggregate build; 2270 jobs. |
| `lake env lean Audit/GroundHeadMatching.lean` | 0 | All 17 audited declarations use only `propext`, `Classical.choice`, `Quot.sound`. |

A read-only Python scope check exited 0: HEAD equals the recorded baseline,
the only tracked change is exactly six appended aggregate imports, the new
files are exactly the six modules plus this note and the audit, and the new
modules contain none of the prohibited proof tokens. No existing Lean line
was edited. No Rust or parser behavior changed, so no Rust tests were run.
