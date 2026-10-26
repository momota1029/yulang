# Parameter semantics stage 2 — producer receipt

Owner `/root/checking_semantics_route_r4`; primary `/root` owns independent
review, integration and Git. Status: source frozen and checked; full evidence
freeze accompanies this receipt; independent acceptance is pending.

## Lease and budget

Exactly three new repository outputs:

- `notes/theory/lean/YulangClosure/OriginalParameterSemantics.lean`
- `notes/theory/2026-10-26-original-parameter-semantics.md`
- `tasks/agent-loop/inbox/20261026-original-parameter-semantics-r4.md`

Private scratch: `/workspace/scratch/f98087c7ac1a/parameter-semantics-r4/`.
Release 2026-10-26 16:29 UTC, within the original packet begun at 16:07:10 UTC.
Absolute deadline 17:07:10 UTC. Maximum 24 author checks total across stages;
stage1 used ten, stage2 used six (11–16), combined 16. Each check has a 120-second
limit, one CPU/thread, Lean `-j1 -M1024`, and 1280 MiB group RSS cap.

No old module/note/producer, core/config/root-import/shared-status, Git,
Rust/native compiler, expectation or descendant writes occurred. Stage1 prose
repair remained primary-owned. Stage1 source `73af381d...` was never changed.

Code frozen after clean check 14 at 2026-10-26T16:45:04.468840+00:00:

```text
OriginalParameterSemantics.lean
SHA256 733c5b05e0db226f95d14ff2161c46e9a389b43d86b365b000a9656ec4fd0bd2
bytes  45481
authored theorem roots 38
```

No source edits followed that freeze. Exact note/receipt/artifact hashes and
the stopped-writer receipt are separate non-self-referential metadata.

## Inputs, authority and provenance

`input-manifest.json` SHA256
`b95e6724db72c4480b0e23e28e11ec246feffe3902a78326271d182daa5e8a10`
pins 19 inputs: sixteen source modules and three project files. The isolated
project/cache was copied from the exact stage1 frozen project; source and
configuration hashes were checked before every run. This stage did not claim
an independent empty-cache dependency build.

The added stage1 dependency is
`73af381dcf6796a06d9508b8c7725ce6b3dfc0c84c3193246a3db5d8bbc1dc64`.
It began as the primary-authorized frozen draft input, then was independently
accepted and published unchanged at checkpoint23,
`1e6d1cfcca1a653d3bfd16193adc2e7e70aaa648` (primary verification 16:38:19 UTC;
review prefix `3e609622`). No input was silently refreshed after acceptance.
All other frozen hashes are in the manifest, including SourceEvents
`df3469e9...`, Pair `1069c185...`, WorldReadout `edb82b9e...`, Generation
`0f25e533...`, Environment `0e12d33d...` and Interpretation `feddd815...`.

The exact AGENTS/base/rules, lean-prover fallback, Lean proof skill and original
authority snapshots were inherited into this stage's private authority
inventory. Governing mathematics: SG §3.3; Entry-Value/Entry-Retained in
call-input construction §3.2; call-input realization; simultaneous immutable
root §§2–5; recursive embedding §§3–6.3, especially the §6.2 distinction between
missing native meanings and already fixed original meanings.

## What was actually constructed

### Source and local frame data

`Telescope` retains complete actual Frames with their binder/kind evidence;
`Telescope.values` extracts the same typed prior values. The actual event and
entry-path metadata are preserved. This is not a first-invocation search.
`selected_at_original_formal` constructs the local descriptor equation after
replaying those frames. `source_formal_description_binder` unfolds the actual
root-Lambda source binder, and `decode_formal_description` applies the original
`decodeFrame` to that exact constructed Description frame.

This strengthens the local constructor but does not authenticate arbitrary
enclosing source occurrences or event parents. The full source-incidence claim
is deliberately not inferred from binder/kind agreement.

`SharedPosition` retains the original owner, full typed prior `ScopeValues`
and separate complete raw key. A proof-use route is not part of raw identity.
Different typed priors remain distinguishable even at the same raw key.

### Missing-native presentation and readout

`Snapshot` retains the complete represented native World, raw provider table,
alias references and opaque residual configuration. `NativeAssignment` retains
full address/view data; `NativeWitness` separates current fields from the scoped
strategy. Neither stores a WorldRegistry or desired semantic proposition.
`pack`/`unpack` prove both actual record inverse equations.

`inputs base references` is one fixed function before Force. It computes every
installed `Some`, saved-reference alias lookup, actual provider capture address
and same-cell capture value. It keeps every nonworld primitive, guard, domain,
raw Force relation, trace form and observation field unchanged. A dangling raw
capture is explicitly still visible; no success/safety filter discards it.

`initialRoot` constructs the initial decoder/native installed equation rather
than receiving it as a law. It is a new presentation root, not a reset of an
old environment. Arbitrary later replay still needs its own preservation
correspondence.

### Full native parameter-bind world

`bindEvent` uses actual native bindValue, the actual allocator address, the
given existing parent and the preselected descriptor. It accepts current raw
history and independent current fields, preserves fiber/eta0 and plain-bind
native residual fields, and changes only the fresh address's derived contract.

`bind_installed` and `bind_old_installed` derive the complete readout update and
all-old-Some preservation from real vector support. `bind_capture_value` proves
complete capture preservation under that changed assignment, including
nonlatest saved environments and formal shadowing. `native_alias_same_cell`
constructs both raw alias handles at one existing cell, and `nativeAliasData`
reads the same complete contract at that actual address.

`bind_phiW` proves every conjunct of the computed native PhiW from the prior
clause, actual recursive returned field, candidate restriction action, real
saved-environment bounds and independent post-event guards. It has no
post-registry equality or desired post-world premise.

`bind_meaning_world` constructs restriction by unfolding Meaning's actual
value/carrier clauses and folds the new world. `bind_background_world` uses
Background's distinct hereditary action and source hole-future law. It does
not reuse completed Checking on B_H. `source_formal_phiW` uses the constructed
formal endpoint and the actual source name instead of an unrelated descriptor
or native key.

## Exact boundaries requiring independent review

1. **Base-sort versus native scoped witnesses.**
   `NativeWitness b View.shared` takes `SharedPosition b View`, including
   `ScopeValues b View`. The native sorts replace Configuration, Assignment
   and JointWitness. No full dependent correspondence with arbitrary
   `ScopeValues (NS b ...)` was constructed. Event/Presentation product
   roundtrips do not repair this. The native scoped strategy theorem must not
   be promoted to all-original/native Shared ownership or overlap coverage.
2. **Source/frame authenticity.** Telescope validates binder/kind and retains
   full metadata, but does not derive authentic enclosing source routes or
   event-parent incidence. The Description-frame consumer is local to the
   computed root-Lambda binder, not a successful legacy-generation theorem.
3. **Force and Return provenance.** The actual returned-field certificate is
   still a premise of the Meaning/Background bind constructors. The old world
   is unfolded by the correct eliminator; the source Force-to-formal result
   certificate is not constructed. No arbitrary traceForm premise, changed
   traceForm definition, altered return-rebind admission or pending erasure
   was added to simulate that result.
4. **Exact earliest Entry gap.** Generation's Lambda parameterEntry emits
   `sourceFormalRole`, `receiptFormation`, `entryForceReturnRebind` atoms. It
   has no explicit payload B-to-formal A CheckGoal or actual same-port trace
   equation. The original Entry-Value theory supplies the intended complete
   port ownership; it still needs a genuine formal constructor/readout. If B
   differs from A, the B_H comparison is separate from completed Checking.
5. **Existing original meanings.** The new native sorts and world fields are
   missing-native definitions. They do not identify arbitrary old sorts,
   Inputs, native machine states or provider/State meanings. Residual fields
   are retained but their global identification is not inferred.
6. **Physical native invariants.** Real vector support and old saved-environment
   bounds remain explicit. Neither source hygienic names nor distinct provider
   IDs proves them. Invalid raw records remain data, rather than being deleted.
   The fixed body-reference map is raw interpretation data; its agreement with
   every original source Body/provider remains a separate registration.
7. **Legacy Shared/anchor application.** The existing source generator and
   Outcome/anchor consumers are unchanged. This packet does not yet execute
   the original invocation/Force history and then consume the actual retained
   anchor in a fully linked post-bind source world.

No full inference-soundness, general recursive L4, all-future Function,
mutable-State or complete original-world closure is claimed. This is a real
computed native world constructor with named source-application residuals.

## Discriminators

The paired note's eight-row table records exact coverage. New checked roots
include same-view/different-cell contracts; current-witness change with old
scoped Shared values preserved; identical native cells with different scoped
assignments; distinct typed priors at one raw key; explicit dangling-capture
visibility; and impossibility of equating a pending Outcome with Returned.
Nonlatest captures are covered by the general changed-assignment theorem.
Stage1's repeated-Site, raw-operation collision and description/key results
remain unchanged dependencies. The B-to-A and full dependent native-scope
rows remain explicitly partial.

## Complete audit

Clean final module check 14, complete origin/current census check 15, compiled
audit closure check 16. All originating constants are selected by module index,
including private/generated declarations; this is not namespace-only sampling.

| Inventory | Count |
| --- | --- |
| Originating constants | 267 |
| Originating theorem constants | 86 |
| Authored theorem roots | 38 |
| Actual current census-module constants | 0 |
| Compiled ParameterSemanticsAudit origin constants | 0 |
| Final current closure-audit constants | 0 |
| Project or unapproved transitive axioms | 0 |

Full types and axioms are retained for every originating constant and authored
root. Across all 267 constants, standard axiom dependencies occur as follows:
`propext` 42, `Classical.choice` 1, `Quot.sound` 10. Across the 38 authored roots:
20, 1 and 9 respectively. No `sorryAx` or project axiom occurs in the final
checked module output. The first failed elaboration's generated sorry diagnostics are
retained in check11 and are not final evidence.

Authored roots under `YulangClosure.OriginalParameterSemantics`:

```text
telescope_keeps_binders
telescope_keeps_payloads
selected_at_original_formal
declaration_uses_entire_prior
source_formal_description_binder
decode_formal_description
description_keeps_actual_metadata
scoped_shared_keeps_owner
different_proof_uses_share
shared_position_keeps_typed_prior
unpack_pack
pack_unpack
every_native_some
native_inputs_keep_domains
native_inputs_keep_force
native_inputs_keep_trace
dangling_capture_not_erased
initial_decoded_readout
bind_keeps_static_fiber
bind_current_fields
bind_uses_current_history
bind_existing_shared
bind_installed
bind_old_installed
bind_capture_address
bind_aliases
bind_phiW
bind_capture_value
native_alias_same_cell
native_alias_reads_same_contract
meaning_installed_restrict
bind_meaning_world
bind_background_world
source_formal_phiW
changed_current_keeps_old_shared
same_native_cells_different_scoped_values
same_view_distinct_cell_meanings
pending_has_no_returned_constructor
```

## All attempts and evidence

Checks11–16 and every actual snapshot remain in this private cone. Check11
failed: ActualEvent constructor/type issue, transparent-native-sort rewrites,
untyped object argument and local rewrite reductions. Checks12,13,14 passed;
checks15,16 passed the complete inventories. No failure or attempted snapshot
was removed. Source bytes stayed fixed through both final audits.

The previous stage's normal sandbox Lake installation error remains in the
immutable predecessor evidence. This stage used the same native binary and
explicitly authorized bounded require_escalated wrapper, not a path/toolchain
or configuration workaround. Commands, elapsed times, RSS, snapshots, exit
statuses and log hashes are in `checks.json`. No running checker or source
writer is retained after the final stop receipt.

Key evidence paths under the scratch root:

- `input-manifest.json`, `authority-manifest.json`, `baseline/`, `authority/`.
- `checks.json`, `11-module.log` through `16-census.log`, matching `snapshots/`.
- `code-freeze.json`, `required-roots.json`, `census-summary.json`.
- `origin-inventory.json`, `origin-types-axioms.txt`, `root-types-axioms.txt`.
- Exact `ParameterSemanticsAudit.lean`, compiled audit module and
  `ParameterSemanticsClosureAudit.lean` inputs/results.
- Final complete artifact manifest, three-output freeze and stopped receipt.

The author is stopped at this concrete boundary. Primary may independently
review and publish the constructor while the actual source/anchor/telescope
owner migration proceeds in a separately authorized packet. This receipt
does not certify its own acceptance.
