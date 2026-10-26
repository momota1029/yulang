# Computed native parameter-bind readout

> **Source-generation update (2026-10-26).** The
> [formal Shared migration](2026-10-26-original-formal-shared.md) supersedes
> the statements below that the current Lambda builder lacks formal Shared
> or that the standard Parameter consumer inserts it into a separate tree.
> The current builder emits the original formal Shared and the Parameter
> consumer uses that exact tree. Earlier theorem inventories, hashes and
> missing-generation claims below describe their recorded baseline. The
> actual Build-description tie, complete decoded-event correspondence and
> whole original inference-soundness obligations remain separate.

Status: a partial constructor supplier is constructed, module-checked, and
fully origin-audited. Complete source-owned post-bind PhiW and B_H.W remain
open. Fresh independent review and integration are primary-owned.

Implementation: `YulangClosure.OriginalWorldReadout`. The module reads the
accepted `OriginalRecursivePair`, `OriginalSourceEnvironment`, and their frozen
native dependencies. It changes none of those definitions.

## 1. Actual source and native operation

The selected [native recursive interface §§2–3](../design/2026-10-08-native-recursive-interface-definition.md)
and [original interface embedding §§3–6.3](2026-10-08-recursive-original-interface-embedding.md)
retain the actual returned parameter value, current world, saved lexical
environment, original rebind path, and complete shared witness. The completed
entry case in [simultaneous immutable introduction §4](2026-10-08-simultaneous-immutable-root-introduction.md)
requires the actual Return value certificate, every old value/carrier binding,
original rebind evidence, and independent joint guards. Raw cells or native
view handles alone supply none of those semantic certificates.

The inspected native `tools/inference-playground/src/runtime/machine.rs`
implements the relevant operation as follows:

- `Frame::ValueEntry` can preprocess the actual Force return before binding.
  In its callback branch, `receiving.callback_entry` creates a new callback
  view and formal receipt, mutates receiving, and replaces the incoming view
  in the received record (`machine.rs` lines 1458–1464; `receiving.rs` lines
  300–335). The incoming Force-return view and receiving state therefore need
  not survive the entire entry transition unchanged.
- Record patterns branch to `bind_record_parameter`, whose projections and
  dispatch composition precede individual field binds. Unit patterns validate
  the returned value and retain the environment without adding a formal cell.
  The ordinary formal branch selects the Value role and calls `Machine::bind`
  with the record resulting from any actual preprocessing.
- `Machine::bind` itself appends its supplied record to `cells`, then extends
  the selected lexical environment with the new cell address.
- `extend` copies dispatch from that selected parent. The parent need not be
  the latest environment node.
- Existing closures retain their actual `ExecutableValue::Closure.environment`.
  Resolved Name lookup follows that saved environment and its parent links.
- Bind itself does not update receiving or the dictionary machine. Name
  dispatch can update dictionary/dispatch information and is a separate action.

`SourceIdentityWorld.bindValue`, `NativeClosureEnvironment.Store.push`,
`extendNode`, `lookupKey`, and the accepted Pair entry suffix expose the plain
Value bind substep. Their supplied world and received record represent the
state at that substep, after any actual entry preprocessing. This packet
proves the projected append, environment, and readout equations. Identifying
the actual post-preprocessing world/record, callback view and receipt creation,
record/unit-pattern behavior, and the subsequent body-evaluation transition
with the complete source and Rust entry remains a separate correspondence
obligation. Preservation of receiving/rest and selected-parent dispatch is a
claim about bind itself, not the entire `Frame::ValueEntry` transition.

## 2. One joint logical assignment, indexed by binding address and view

`ViewAssignment` contains descriptor and interface coordinates indexed by
**actual cell address and native view handle**, plus raw value/carrier/root
projections. It is one joint data assignment. It is not a semantic typing
certificate and is not reconstructed from a native tag.

Address indexing matters. Two actual cells can contain the same received
value and view while retaining different source contracts. Equal native view
handles must not collapse those contracts. Conversely, a capture must retain
its actual resolved address, not merely the captured cell's view.

`ViewAssignment.received` reads the actual entry role. A Value cell becomes an
Installed.value with the assigned descriptor and actual projected value/root.
A retained Computation cell becomes an Installed.carrier with its assigned
interface and actual carrier/root. `bindingReadout` maps every Some cell at
its actual address. It does not restrict the interpretation to indices below
Store.size, infer membership from the role, or discard unrelated old cells.

The assignment-to-original-source-contract connection remains with the source
owner. In particular this module does not assert that an already fixed foreign
interpretation is equal to this readout. The distinction between a missing
native meaning and a fixed original meaning follows embedding §6.2.

## 3. Finite native support is constructed

An arbitrary Lean Store can contain Some values outside its declared size.
Changing the original all-Some world quantifier to ignore them would weaken
that interface. The readout therefore keeps all of them.

For an actual native vector snapshot, `vectorStore` is the direct list/Vec
projection. `vector_cell_beyond` and `vector_some_bound` prove its finite
support from that constructor. `vector_store_push` proves that native append
of a received record is exactly Store.push. `interpreted_some_has_native_bound`
derives the bound for an interpreted Some entry of this actual vector.

`parameter_bind_every_old` applies this actual-vector invariant to preserve
every pre-existing interpreted Some entry. The consumer is not asked to add
a count guard to the original meaning. This is an immutable append result;
mutation, overwrite, Var, and State transitions remain outside its conclusion
and remain obligations of the full parent language.

## 4. Computed parameter-bind and actual Return fields

`parameter_bind_readout` proves the equation

```text
bindings(bindValue(world, savedParent, formal, actualReturn))
  = extendBindings(bindings(world), world.cells.size,
      Installed.value(
        assignment.descriptor(world.cells.size, actualReturn.view),
        actualReturn.value, actualReturn.root)).
```

The value/root notation above stands for the explicit raw projections in the
assignment. The equation is proved from Store.push and the actual received
record. No actualRegistry equation, rebind law, complete-world predicate,
KernelSound, or LocalLaws record is a premise.

`parameter_bind_actual_return` reads the exact new cell.
`parameter_bind_native_vector` identifies the corresponding actual appended
vector. `parameter_bind_preserves_other_fields` retains receiving, control,
dictionary/rest and the selected parent's dispatch.
`parameter_bind_preserves_old_environments` retains every old environment node,
including nonlatest branches and all its stored metadata.

`pair_parameter_step_readout` applies the equation to the accepted Pair's
actual `suffixStep (.entry world returned)` and its resulting body state. It
uses that actual returned world and the suffix's captured environment. It
assumes no eventual Return from a pending or divergent carrier.

`parameter_bind_recursive_fields` consumes the old installed binding fields
and the certificate of the actual Return row at the same event. It constructs
all recursive binding fields of the new readout. This is precisely the
installed-binding conjunct needed by PhiW, not a proof of full PhiW. Alias,
capture, Shared/EventField, coherence and independent guard requirements are
not renamed as this theorem's conclusion.

`returnRow` separately accepts an arbitrary checked descriptor. The theorem
`checked_return_descriptors` proves that two distinct checked descriptors
retain the same raw value/root/event while their decorated rows stay distinct.
It does not assert either row's membership.

## 5. Actual saved captures and their physical bounds

`captureAddress` uses the actual Closure.savedEnvironment and the body's
resolved reference key, then performs the original lookupKey. `captureReadout`
reads the resulting actual cell under the joint assignment. Absent references,
unresolved addresses and uninitialized cells do not become certificates. The
address readout remains separate from the optional decorated payload readout.

`AddressesWithin` is a physical arena invariant: every stored binder address
names an allocated cell. It contains no type or safety predicate.
`addresses_root`, `addresses_extend_existing`, and `addresses_parameter_bind`
prove its actual constructor cases. `lookup_address_bound` and
`capture_address_bound` derive bounds from those existing arena records.
The theorem does not derive allocator freshness from distinct provider IDs,
nor site freshness from SourcePair.Hygienic.

`resolvedCaptureData` constructs the exact accepted Pair CaptureData record
from a raw saved lookup and an actual populated cell. Its address bound and
object/readout equation are derived. They are not supplied as desired
semantic correspondence laws.

`capture_address_parameter_bind` preserves every old saved lookup.
`capture_readout_parameter_bind` preserves its complete decorated contents,
even when the new formal shadows the same name in the current environment.
`every_registered_capture_preserved` applies this to all entries of an actual
provider/closure table satisfying the ordinary saved-index invariant. That
table and its source registration are inputs; the theorem does not invent a
provider registry or prove all native allocator invariants.

## 6. Existing Shared projection and the exact missing owner

`sharedFrames` projects the entire original Shared frames, retaining their
binder, actual event, entry path, bindings, installed records, and witness.
`actual_return_preserves_older_shared_frames` proves that the current raw
Return decoder preserves this older projection. The scalar witness projection
and its readback/distinguishability theorems are also included.

`actual_return_current_witness` reads the current witness from RuntimeReadout
at the actual Return and complete original prefix. It does not equate that
current witness with the earlier witness or freeze the whole witness map.

These are preservation equations for existing data. They do not establish
that formal binding introduces no new Shared evidence. In fact,
[SG §3.3](2026-10-08-source-generalize-definition-and-proof.md#33-owning-rules-declarations-and-event-telescopes)
explicitly assigns retained initializer/rebind evidence to Shared, operational
return/response fields to EventField/OneShot, and description-owned proofs to
EventProof. Call-input realization §4.1 separately requires original typed
rebind evidence at the new actual world.

The frozen generation/environment interfaces do not yet supply the complete
formal-rebind output:

| Existing representation | Present data | Missing connection |
| --- | --- | --- |
| Lambda sourceRules | Formal description, invocation, receipt, returnRebind execution suffix, pattern/body EventProof | Retained formal-rebind Shared evidence output at its original scope |
| bindingsRulesK initializer | Actual Return suffix followed by an explicit Shared binder | This is a different source introduction and cannot silently stand in for the formal rebind |
| Runtime.Outcome | Raw observation, result, current history/configuration, endpoints and bindings | Original retained evidence and EventField-position projections |
| LocalAdmissions.returnRebind | An independently interpreted predicate | A constructor returning the actual scoped retained evidence tuple |
| RuntimeReadout | Current eta/witness/scope/authority/incidence/dictionary maps | Their declaration-owned EventField registration and assignment linkage |

Thus the absence of a Shared binder in the current Lambda builder is a
source-to-generation/readout gap, not semantic authority for omitting its
retained evidence. A standalone record that merely assumes the desired
source-to-record correspondence would not close that gap.

The primary is constructing the disjoint OriginalSourceEvents metadata packet:
raw-source occurrence routes, actual formal receipt/rebind owners, and a
separate scoped retained evidence packet whose values come from an independent
joint assignment. Its precise linkage into the old core remains a later
reviewed change. This module imports no provisional version of that packet.

Complete post-bind world construction can then combine the computed binding
and capture suppliers here with those actual scoped outputs and independent
original guards, applying canonical_world at the resulting current event.
It must preserve older Shared coordinates while permitting genuine new
EventFields/current witness values. Equality with `WorldRegistry.rebind`
preserves both entire witness functions. Such an equality can be a valid
sufficient premise for particular lawful assignments, but this packet has not
derived it as a universal original bind law; imposing it universally may
exclude assignments with genuinely changing current fields. The computed
partial constructor here does not assume that whole-registry equality.

## 7. Discriminating evidence and scope boundary

The checked probes cover a nonlatest saved environment, formal shadowing,
all retained raw cell contents, selected-parent dispatch, unchanged rest,
and exact decorated capture contents. One probe uses identical raw values and
views in two cells but different assigned contracts; another proves their
captures retain the exact distinct addresses and therefore distinct contracts.
Two checked descriptions of one raw Return remain distinguishable. Different
actual Shared assignments produce different witness projections.

A newly registered EventField combined with preserved older Shared evidence
is deliberately not claimed: constructing that new owner is the precise open
source case above. Current RuntimeReadout equations alone cannot certify it.
No source receipt is identified with a native ValueEntry RootComp receipt;
the native receiving implementation and the accepted Pair's separate source
phase receipt remain distinct. No Name dictionary transition, overwrite,
mutable State, general recursive initializer, arbitrary foreign interpretation,
or full original inference theorem is established by this partial supplier.

## 8. Verification

Final code SHA-256:
`edb82b9ecc62be486e057ee50152e30dad709f9a90196f78cab803838f08fb00`
(31,012 bytes). Check 8 compiled those exact bytes with pinned Lean 4.35.0 and
Lake 5.0.0-src+eb6cafb. Check 9 audited all 120 originating declarations,
including 67 theorem constants and all 40 authored roots, with complete types
and axiom dependencies. The actual standard axiom union is propext,
Classical.choice, and Quot.sound; no project axiom or unchecked proof mechanism
was used. All failed attempts and exact snapshots are retained in the paired
handoff's isolated evidence directory.
