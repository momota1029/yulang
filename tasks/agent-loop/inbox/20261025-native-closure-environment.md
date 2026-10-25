# NATIVE-CLOSURE-ENVIRONMENT author handoff / revision 1

Outcome: CANDIDATE, unverified Lean construction. No theorem certification or
production authority. Original RESPONSE-ENCODING-1 / POI-TRACE-1, full callable,
native execution and Simple-sub A/B parents remain OPEN with original quantifiers.

Sprint LEAN-NATIVE-CLOSURE-ENVIRONMENT-20261025/r1.
Contract SHA256 2630ec7db277777bf4e0fb8e99a665cdd65d842471264a736a079c122a1f073f.
Baseline 657d688fc022261fa1013f7eb4f2b323d6cfd4a6.
Author /root/native_closure_environment_astra_r1. Requested Astra/medium;
observed model UNKNOWN, observed effort UNKNOWN. Current session is this exact
parent-issued task; supported NEW_TASK receipt received. No descendants.
Primary /root supplies complementary source audit; not an independent reviewer.

## Constructed result and parent application

NativeClosureEnvironment defines an actual finite chronological root/append log,
optional full binder identity and cell address, dispatch payload, and Valid with
arbitrary strictly older parent. It does not restrict parents to the previous
index. lookup computes structurally; lookup_node connects it to the native
same-arena nearest-matching parent step; parent_decreases and node_bound give
finite native walking. Old node/address lookup survives arbitrary append histories.
Dispatch-only append is transparent. Full identity shadowing/preservation,
saved-versus-caller entry, finite cell push and current-store observation have
explicit equations. There is no captured-value snapshot. Malformed cycles are
outside Valid; the unvalidated datatype is not claimed source reachable.

CallEnvironmentRealization defines resolved lexical references and direct global
cell addresses, a finite typed layout, Option-valued actual lookup/read traversal,
and a total substitution with explicit filler. Captured and captured_index prove
that every context-typed index reads a successful actual value. CellsTyped demands
ValueTyped only for the exact layout entry/address/current-cell-read combination;
no invariant says arbitrary stores are typed. realized_substitution_typed derives
the existing hs premise from the read construction. close_body APPLIES
TypedCall.substituteCallComp_typed; close_parameter_body and
close_computation_body apply it under parameter A and delayed argument UA.
The existing traversal includes bind/request binder lifting. Existing syntax,
Function/Value separation, Simple-sub inference and all ordinary semantics remain
unchanged. No foreign continuation/F1/FK1 claim is made.

## Source and representation boundaries

Source owners: machine.rs Environment175, root447, lookup2585,
with_dispatch2596, substitute_environment2606, extend2626, bind2635;
Lambda864 captures environment and Callee1224+ selects it. Source inspection of
lookup/append/bind supports the candidate equations. Primary owns exhaustive
source producer reachability and branch audit. Source dictionary helpers may fail
and may mutate metadata before error: no global rollback theorem is claimed.
Cell writes1543/1739/1760 and allocations2524/2637 require current-store reading.
Name785 ModuleDef goes through program.definition_indices (global Reference);
Parameter/Local/Catch/Case go through lexical lookup. Imported/Unresolved/Ambiguous
failure is not a successful layout. dispatch_name and NameConsumption semantics
remain separate from raw represented stored-carrier observation.

Computation1316 binds the actual delayed carrier; ValueEntry1468 record staging
and1471 unit validation differ from ordinary parameter binding. RecordDefault1491
sees earlier introduced fields. These branch-to-layout equations belong to the
primary source note, not an assertion that every source pattern binds one formal.
Formal close_parameter_body applies exactly where an actual parameter is bound.

Remaining original premises and owners:
- LAYOUT-COVERAGE: primary source/proof lane must construct resolved layouts for
  every represented open source body, including global identity resolution and
  captures/shared resources. Falsifier: a free source occurrence absent/misbound
  in its typed layout, particularly a record default referring to an earlier field.
- CURRENT-CELL-REPRESENTATION: source readback/typing lane must produce the exact
  represented Value and per-cell ValueTyped at observation time. Falsifier: later
  initialization/write or dispatch/consumption invalidates the claimed value/type.
- RECURSIVE-GRAPH/CALLABLE: native recursive graphs, closures-as-values, code/body
  representation and dispatch meaning remain unrepresented in finite Value.
  Owner primary future authorized proof packet; no syntax extension authorized.
- VERIFY-CANDIDATE: primary runs allowed Lean/axiom checks and repairs only after
  this writer-stop receipt; fresh nonauthor reviewer inspects fixed final bytes.

## Prior work and checks

Reused CoreSyntax/CoreSubstitution exact APIs and substitution theorem in their
represented finite Call domain. Native template/literal suppliers are retained
only for their reviewed structural/literal premises, not used to infer arbitrary
callable typing. No previously failed force or foreign continuation premise was
renamed or assumed solved. No new external dependency.
All 59 contract dependency pins were recomputed using Python3 and matched before
freeze. Contract hash matched. Python executable `python` was unavailable on an
initial hash-only command; corrected to python3. This is not a Lean failure.
Lean/build/test/native checks NOT_RUN by assignment. Axiom report NOT_RUN;
no sorry, new axiom, native_decide or Classical introduced in candidate source.
Distinguishing examples cover full-key/same-spelling, shadowing, unrelated append,
missing/uninitialized cells, current contents and successful direct global reads.
They are supplemental candidate declarations, not executed evidence.

## Freeze, resources and ownership

Allocation <=300 seconds wall from spawn; frozen before limit. No renewal.
No subprocess remains, no descendants, no Git or production edits. All writes
STOPPED after this handoff. Primary may take the two module leases for verification
and mechanical repairs. This author is ineligible to independently certify the
combined result. Next in-scope step is primary verification then fresh review;
parent closure still requires the named source/representation owners.
Only new paths are the two modules below and this exact inbox path. No scratch.

Frozen artifacts:
- `notes/theory/lean/YulangClosure/NativeClosureEnvironment.lean` SHA256 `382fa841c56fbf04ae3fd5dd6a45a7c8cf5801608b73a622c5d30dd2c8f97a90`; author `/root/native_closure_environment_astra_r1`.
- `notes/theory/lean/YulangClosure/CallEnvironmentRealization.lean` SHA256 `90703c9625ac55d341375a37bdcf8edcb00b48e8020e33fcd9465128a73b2f7f`; author `/root/native_closure_environment_astra_r1`.

Direct API dependency hashes:
- `notes/theory/lean/YulangClosure/CoreSyntax.lean` SHA256 `c5a25cb7d935159b62f377b7fa88b3e92e4cdf429118d566e53f7859f6ea5375`.
- `notes/theory/lean/YulangClosure/CoreSubstitution.lean` SHA256 `ae1dfd4947d9e87c05dfa893b93067175d860ed3b5da000d61257d7789208b55`.
- `tools/inference-playground/src/runtime/machine.rs` SHA256 `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e`.
- `docs/yulang-operational-type-safety-ja.tex` SHA256 `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.

Freeze UTC 2026-10-25T06:02:50.020934+00:00.
