# Cycle58: retain graph inspection under source allocation

Status: Draft. Date: 2026-11-09. Scope: B4 source-identity/generated-work boundary.

## Objective and boundary

Close executable graph extension for arbitrary finite old graphs and appended source
occurrences: reconstruct every old structural/nominal edge, preserve every finite
observation, and preserve exactly all paths, direct structural cycles and old-node
bisimulation. With newly allocated storage initially unresolved, preserve the actual
K2 regularity test and the complete existing graph-inspection entry point.

Data: a source Table, an appended Table and an old Graph. The general `grow`
operation additionally takes arbitrary nodes for new slots. The concrete `allocate`
operation initializes those slots unresolved. Old nodes cannot acquire new outgoing
edges during allocation alone. New aliases use canonical old roots; fresh names use
the first corresponding new occurrence, as established by cycle57.

Execution: retain numeric old indices and map every old edge through retain;
select a supplied new node only outside the old range. No root or graph preservation
property is assumed from the caller. Canonical old roots commute with the operation
by cycle57's canonical_retained.

Quantifiers: every finite table/suffix, old graph, old root/target, finite observation
depth, pattern, role and ordered visible-head list. No acyclicity, determinedness,
source-name uniqueness or externally proved graph invariant is required.

## Proof chain

1. Reconstructed old nodes give an exact successors map. Forward path transport and
   path-origin recovery give an iff for all old paths, then StructuralCycleAt and
   the actual recursiveAt equality. Nominal argument edges are included.
2. Induction on depth preserves every finite graph observation, including arbitrary
   turns around a cycle. Canonical old-root observations commute as well.
3. Lift/restrict finite relation witnesses to obtain exact old-node Bisimilar for
   general `grow`, even with arbitrary fresh graph contents.
4. For `allocate`, every structural candidate belongs to old storage, so the global
   bisimulation-based regularAt check is preserved, including finite unrollings.
5. Mutual structural induction preserves inspect and inspectAll, including captures,
   later siblings after mismatch, head order and duplicates. This yields exact
   inspectSnapshot preservation and the canonical-source-root specialization.
6. New aliases immediately reuse old canonical observations. Genuinely fresh names
   have an unknown snapshot at their computed canonical root.

The initial design identified step 4 as a possible boundary. The finite witness
construction and unresolved-allocation invariant closed it during this cycle.
The remaining boundary is declaration-driven allocation and later updates to old
nodes. Such updates can change regularity, as the existing
CommonRoleGraphBisimulation.graph_update_changes_regularity example demonstrates.
Raw alias storage is not required to have identical contents; canonical roots are
the source-identity interface. No final language rejection is inferred from a cycle
encounter, and no result on whole-resolver classification is claimed.

## Prior evidence and remaining bridges

Cycle57 supplies retained numeric roots and captures, but not reconstructed edges.
CommonRoleRegularGraph supplies exact direct-cycle checks; GraphBisimulation supplies
finite observations and K2; GraphInspection supplies the unchanged actual inspector.

Read work/dots-audit notes/audit/x-oracle.md X13-X17 and C3-PARENT. They support
shared source constraints, not an internal graph allocation algorithm. No new
Yulang2 execution or language-semantics choice was needed for index retention.

General B4 still has five open bridges: source_boundary_adequate,
generated_work_closed, saturate_terminates_and_closes, saturated_frontier_exact,
resolve_dictionary_order_sound. This closes a substantial allocation/inspection
subgoal, not any entire bridge. Declaration-produced child source names and graph
updates must still be connected to this verified interface.
