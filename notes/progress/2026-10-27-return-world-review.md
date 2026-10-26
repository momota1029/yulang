# Independent review: original Return world at the consuming source event

Date: 2026-10-27. Reviewer: `/root/soundness_hygiene`.
Producer: `/root`. This review did not modify either target.

**Verdict: PASS for the stated local native Return/readout construction and
its original source-entry consumer. No blocking proof or claim defect remains
in the frozen targets below.** This verdict does not close original
whole-language soundness, Effect hygiene, principality, inference termination,
or the remaining source/native interpretation obligations.

## Frozen targets and review boundary

| Target | Reviewed SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalReturnWorld.lean` | `0710f5d969af927c8f42b42f4972ba4f53ddce4ddb082e9d3d360e90c9ccf12b` |
| `notes/theory/2026-10-27-original-return-world.md` | `d06b25783ebcb911a9b6e9b2051a60493feccfb528da40a94bf6d02ef9098d26` |

I read the complete 522-line proof module and its paired note, compared the
critical elaborated theorem types, and followed their original definition
owners. Those owners include `OriginalFormalShared`, `OriginalForcedParameter`,
`OriginalParameterWorld`, `OriginalParameterSemantics`,
`OriginalSourceEnvironment`, `OriginalSourceInterpretation`,
`OriginalRecursivePair`, and `SourceIdentityWorld`. The governing source text
was `2026-10-08-source-generalize-definition-and-proof.md`, especially its
scope and L1–L4 boundary, the complete Value-entry account, and §3.3's owning
rules and one original Shared binder.

The first reviewed note hash was
`8784d98730e267e32671dbd04c36830202f47edd48475601a953bf96389c5b7a`.
I reported three qualified-name errors. The producer corrected only those
references: `OriginalParameterWorld.delivered_native_bind_readout`,
`SourceIdentityWorld.bindValue`, and
`OriginalParameterSemantics.installed`. Reversing exactly those three
substitutions in the final note reproduces the initial hash. The proof bytes
did not change. These documentation findings are resolved.

## Semantic findings

### 1. The computed event contains the actual native bind

`Packet.outcome` calls the existing `SourceIdentityWorld.bindValue`. That
constructor appends `raw.asValue` at the previous cell count and extends the
environment using the supplied successful saved-parent lookup. The packet
retains the complete post-Force snapshot. Its binding list appends the same
formal name and fresh address, so `packet_address` selects that binding even
when the earlier list contains the same name.

`computed_return_event` proves equality of whole Events. It unfolds the
original `RuntimeReadout.event` and computes the matching Return branch of
`valueReadout`; it does not take the desired event equality as a hypothesis.
The target is exactly the existing `bindEvent` on `beforeBind` and the same
packet. The latter event uses the packet's post-Force current snapshot and
this Return's field readout, retaining the original static fiber and entry
assignment. It is not identified with the earlier receipt event.

The inspected `return_current_native_fields` and `bindValue` definitions
retain the packet's residual configuration, provider table, aliases,
receiving state, control and rest. Current assignment/witness fields come
from the same base Return readout. The scoped Shared strategy is inherited
from the incoming decoded event. No equality of receipt and returned worlds
appears in the relevant theorem types.

### 2. Complete registry equality is at the delivered state's own event

`decoded_return_event` applies the event calculation to the actual original
`returnState`. `delivered_event` then uses original Shared decoding, which
changes the retained installed map and formal binding without replacing the
event. The private `objects_keep_installed` induction covers both value and
carrier endpoint objects and every list length; Return's endpoint fold does
not silently allocate or replace the decoded installed registry.

The old representation premise of `delivered_registry_at_own_event` is
precisely:

```lean
state.installed = bindingReadout (liftViews views) packet.snapshot.world.cells
```

This is the actual post-Force, pre-bind world. It is not merely an invariant
at `state.assignment.event.current`, and it is not the desired post-bind
equation. Together with the explicit finite-vector representation, it allows
the already proved native one-cell allocation theorem to derive the complete
function equality:

```lean
post.installed = OriginalParameterSemantics.installed post.assignment.event
```

The fresh descriptor is the same `selection.valueDescriptor mode` throughout
the readout, retained evidence and native installed map. The conclusion
covers every address, not only the new cell. The missing preservation of the
old representation through arbitrary Force effects is explicitly retained as
a separate obligation in the paired note.

### 3. The original source existential is reused without a new witness choice

`PairData.packet` overwrites the supplemental snapshot's `world` with
`raw.world`. Thus an independently supplied supplemental snapshot cannot
replace the actual returned world. `PairData.presentation` makes the same
native bind when the actual saved-parent lookup succeeds. Its absent-parent
branch is total data; both identification lemmas and the source application
require the genuine successful lookup.

`PairData` still supplies history, observation, residual/provider/alias data,
endpoints, bindings and views independently. The module does not derive those
fields from `OriginalRecursivePair.Returned`, which contains fewer fields.
This limitation is accurately stated in the note.

`actual_entry_return_world` calls the existing
`OriginalFormalShared.entry_actual_return_consumer` with the original entry
judgment, decoded state, active invocation, actual `execution.Returns raw`,
and the designated occurrence. Its proof obtains one `witness` and one
`sharedOccurrence` from that consumer. `pair_outcome` and `pair_evidence`
rewrite the same raw packet and the same witness; they do not invert a
semantic projection or choose another successful packet.

Following `source_anchor_delivers` confirms the witness is the actual
admitted Shared payload's `data.witness`, and the occurrence is the actual
anchor occurrence. The resulting decode equation and original
`checkedBody parameter` judgment concern the same extended source environment.
The theorem then adds its registry equality for that same delivered state.
Neither a body derivation nor the post-registry equality is a field of the
new packet, readout, or local admission definition.

This remains an application under the explicitly displayed local kernel and
the existing `PairExecution` operational relation. It does not manufacture a
source-entry judgment, identify an arbitrary global catalogue with that local
kernel, or establish all-source execution correspondence.

### 4. Actual Force supplies membership through the original operators

`delivered_phiW_at_own_event` rewrites by the proved event equality and applies
the existing `bind_phiW`. Its old-world clause, candidate restriction, returned
candidate membership and independent guards remain visible. That theorem is
an event-level application, not a discharge of those generic candidate
premises.

`delivered_meaning_from_actual_force` is stronger at the indicated seam. It
uses `bind_after_force_return_meaning`, whose proof unfolds the same complete
carrier's genuine demanded Force observation and its `PhiT` Return clause.
This derives both world membership at the observation event and membership
of the actual returned value. The observation event is the exact `beforeBind`
used by the delivered event equality. There is no separate assumed old-world
Meaning or returned-value membership in this new theorem.

The Background variant calls `bind_after_force_return_background`, which uses
`background_force_prefix`, unfolds the original `RelativePhi`, rules out
world/trace/carrier holes, and uses Background's own hereditary restriction.
The explicit `holeFuture` premise remains. No completed Meaning or finite
Checking result is cast to arbitrary candidate membership or Background.

Both variants retain the real `force` and `traceForm` equations at the exact
observation, saved-provider and alias bounds, compatibility, event coherence
and world guards. They do not derive these equations merely from
`PairExecution.Returns raw` or from arbitrary `PairData`.

### 5. The construction is scoped honestly

`valueReadout` supplies a concrete local interpretation for the selected
Return binder. It does not prove that an arbitrary previously fixed opaque
readout already has those fields. The paired note states this correspondence
gap explicitly. `OriginalParameterSemantics.inputs` keeps the independent
force, demand and trace fields; the new module does not replace the original
membership operators with a weaker successful predicate.

The original source pattern/body and the preselected descriptor remain
parameters of the consumer. No special body shape, newly assumed source
safety atom, copied Shared binder, postcondition admission, or narrowed
checking conclusion appears in this module.

## Independent verification

Pinned executable:

```text
/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake
```

The direct check ran from `notes/theory/lean`:

```text
lake env lean -j1 -M1024 YulangClosure/OriginalReturnWorld.lean
```

It exited 0 with an empty diagnostic log. No `-o` was used.

For an independent origin audit I prepended Lean's command/axiom inspection
imports to an exact byte copy of the frozen target and appended the audit.
It selected every current-source-origin constant, including generated and
private declarations. The selection did not rely on a name-prefix filter;
it also captured the generated `RuntimeReadout.event.eq_1` owned by this
elaboration. It emitted every selected constant's complete type and transitive
axioms, rejected any new axiom declaration or unapproved dependency, and
required all 14 public theorem roots. Separate `#check` and `#print axioms`
commands covered those 14 roots as well.

Results: **96 declarations: 38 theorems, 52 definitions, 2 constructors,
2 recursors and 2 inductives.** The 38 include the 14 authored public roots,
the authored private induction, and 23 generated/projection theorem constants.
Every dependency is a subset of `propext`, `Classical.choice` and `Quot.sound`.
The private induction is axiom-free; `decoded_return_installed`, `pair_outcome`
and `pair_evidence` use only `propext`; the other public roots use the standard
three. No `sorryAx`, project axiom or extra evaluator trust was accepted.

The exact-source audit first exhausted the 1 GiB cap and exited 134 with
`lean::memory_exception`. That failure is retained. The same audit source
passed with `-j1 -M2048`, exit 0 and no diagnostics. Only the audit's memory
cap changed; no proof source, project configuration or compiled artifact was
written. This failure is not treated as a successful check.

Evidence directory: `/tmp/yulang-return-world-review-20261027/`.

| Evidence | SHA-256 |
| --- | --- |
| `Audit.lean` | `f3cdb58e576c8f07b9fabd86acb22b4104e7909aaa8be2a0e4f513295fd61c0d` |
| `audit.log` — failed 1 GiB attempt | `48bc2200174632932b9ea98fd0a0c30e6dc353ce535531045f1c7efc7b79940a` |
| `audit-m2048.log` — successful complete audit | `15933f98a3e508c6453f21152247be108778e505cd407c98ecf08b2e1bf60e23` |
| `complete-census.json` | `44b0f794e6e030eca41335cd992da90a7a9f58b147b3be523b3968b7038b6558` |
| `input-manifest.json` | `2179a873c7ca0f3d291475cafa61f37d387cfd1daba1a56a5bdb51bbc4fc95d7` |

The standalone successful diagnostic log is
`/tmp/yulang-return-world-review-20261027-source.log`. The manifest also hashes
the inspected Lean dependencies. The parent owns integration builds; this
review did not invoke `lake build` or substitute the parent's earlier audit
for its independent checks.

## Remaining original owners and stopped receipt

The first remaining owners are the genuine catalogue/readout identification,
the post-Force old-registry invariant, the correspondence from actual pair
execution to the full supplied observation, and the original semantic proofs
of compatibility, guards and native environment bounds. Original recursive
callable realization/L4, whole-source soundness and Effect hygiene remain
open beyond these local results. Principality's concrete original source
problem/order and complete inference termination are separate open goals.

All review checkers have exited. Review writes stop with this receipt and its
scratch freeze record. The only repository file written by this reviewer for
this task is this review note. No target edits, Git operations, shared status
changes, import-root changes, builds, `.olean` output, or child agents occurred.
