# Selected recursive pair: raw constructors and complete background worlds

Date: 2026-10-26. Author: `/root/whole_soundness_route_r4`.

Status: **constructed and checked; awaiting independent review**. This packet supplies source-owned constructors and a complete local `PhiW` application for the selected immutable pair. It does not close the original recursive introduction obligation, general L4, or original inference soundness.

Implementation: [OriginalRecursivePair.lean](lean/YulangClosure/OriginalRecursivePair.lean), namespace `YulangClosure.OriginalRecursivePair`. The sole direct import is the accepted `OriginalSourceInterpretation`; no active Environment or Checking module is imported.

## 1. Authority and selected result

The governing sources are [contextual Function membership](../design/2026-10-08-contextual-function-membership-definition.md), [the native recursive interface selection](../design/2026-10-08-native-recursive-interface-definition.md), [the original-indexed embedding](2026-10-08-recursive-original-interface-embedding.md), and [simultaneous immutable-root introduction](2026-10-08-simultaneous-immutable-root-introduction.md). In particular, embedding §§3–5 prescribe receipt, designated Force, actual parameter rebind, captured opposite Name, and own invocation return. Embedding §6.2 and the native-interface selection distinguish a definition of a genuinely missing native field from correspondence with an already fixed interpretation. This packet preserves that distinction.

The selected source is the mutually recursive pair whose first member returns the second and whose second returns the first, after their respective Value-entry argument computations have returned. The argument computations remain arbitrary. An argument can perform administrative steps, request effects, accept independently permitted responses, remain pending, diverge, or return an arbitrary actual value. The pair's body suffix is fixed by the source constructor; the returned argument does not choose a new body.

The principal new semantic result is `world_after_actual_force_return`. It unfolds an existing **whole** declared-hole background carrier certificate at an actual Force return, obtains the complete current world and returned value certificate, transports every installed value/carrier field to the actual compatible later event, and constructs the full result-extended background world. It does not take the new world's validity as a premise. Its remaining readout, guard, and scope-action inputs are exposed in §7 below.

## 2. Exact source constructor and binding incidence

`SourcePair` retains distinct group, binding, lambda, formal, and body Name sites, plus resolved member and formal names. Its `member`, `bindings`, and `statement` build the original raw `OriginalSource.Source` constructors, rather than accepting a caller-supplied typing tree. `source_value_entry` and `source_body_opposite` identify the selected lambda and body constructors.

Source name resolution matters: a formal with the opposite member's resolved name would shadow the intended capture. `SourcePair.Hygienic` therefore records the actual selected pair's distinct member names and disjoint formal names. This is a premise about this selected constructor, not a restriction introduced into the whole language. `generated_group_context` and `generated_body_context` compute the original recursive-group and lambda-body contexts. `source_opposite_lookup` then proves that original `lookupBinding` selects the opposite member. `source_opposite_rule` expands the original Name rule and proves that its same-binding and fetch-once atoms refer to that member.

`source_pair_joint_obligation` also expands the original recursive statement rule. It locates the exact `recursiveJointMemberWorld` atom that the original source rule requires. This theorem is an incidence theorem; it does not prove that atom.

| Source or semantic clause | Constructed declaration | What is supplied |
| --- | --- | --- |
| Two Value-entry lambdas and opposite Name bodies | `SourcePair.member`, `SourcePair.statement` | Actual original syntax with retained sites and resolved names |
| Recursive group and formal scopes | `generated_group_context`, `generated_body_context` | Exact original context computations |
| Captured opposite binding | `source_opposite_lookup`, `source_opposite_rule` | Original resolved lookup and generated atom incidence |
| Actual current receiver | `enter`, `enterWorld` | Fresh active invocation, previous delimiter, preservation of older invocations |
| Argument receipt | `receiveWorld`, `source_receipt_fields` | Selected source receipt with owner, view, site, and formal fields |
| Complete raw Force/Bind sequence | `Move`, `InvocationMove`, `constructor_prefix_iff` | Every constructor prefix and its execution witness |
| Actual parameter rebind and opposite Name | `suffixStep`, `selected_pair_suffix` | Native-shaped bind, opposite capture read, new Name receipt, owned return |
| Complete observation obligations | `canonicalObservation` | Original residual positive fields plus phase-specific world/result/Force/continuation queries |
| Full world | `canonical_world` | All `PhiW` fields, including every installed `Some` entry |
| Two declared value holes | `PairAssignment.holes`, `exact_pair_holes` | Exactly the two registered value tuples; no world or carrier holes |
| Initial joint background world | `pair_background_world` | Full `B_H.W` from the two holes and all old background fields |
| Actual post-Force world | `world_after_actual_force_return` | Full result extension from the whole carrier, actual return, and exact data readout |

## 3. Raw heap, captures, Name receipt, and own return

`Heap.install` constructs a native-shaped immutable capture knot. It allocates two different value handles, cells, and view entries, then two lexical nodes. Both closures capture the same completed environment. Their bodies remain the original source Name expressions. `installed_provider`, `installed_packet`, `installed_view`, `installed_lookup`, and `installed_capture` prove the resulting raw data equations. Older receipt and rest data are retained. `distinct_installed_values` rules out collapsing both providers to one test value.

`Suffix` retains the saved capture environment, distinct formal/opposite keys, actual Name site, dispatch, current owner, and previous delimiter. `suffixStep` performs the existing `bindValue`, `observeName`, and `returnOwned` operations. `bind_captured_read` proves that binding the returned argument preserves the captured opposite lookup. This uses the old-binding preservation theorem, not the identity function's formal read theorem. `opposite_suffix` and `opposite_suffix_executes` construct the actual read and return, including the newly emitted Name receipt. A generic returned packet is explicitly converted through the actual own-return `asValue` behavior.

`SourcePair.actualSuffix` supplies the fixed body plan from the selected source. `selected_pair_suffix` supplies its concrete lookup, view, packet, and delimiter facts from `Heap.install` and `enterWorld`. It takes an arbitrary returned argument packet; it does not assume the body already executed successfully.

This application is an entry-current native-shaped projection. It does not prove that an arbitrary later Rust world has the same capture/environment readout. In particular, `receiveWorld` is the selected original **source** receipt constructor. It is not asserted equal to the Rust Value-entry branch, which does not emit the same native RootComp receipt at that point. The body Name receipt is separately constructed by the actual existing native Name operation. A full source/native phase correspondence still must account for this distinction.

## 4. Every raw prefix, effect, response, and fixed suffix

`Carrier` contains raw state, request, and response types, together with internal, requested, resume, and returned relations. These are independent operational inputs, without safety, typing, or eventual-return conditions. `Carrier.Move` retains internal steps and every related raw request/response pair.

`Returned` carries the actual returned world, value, dispatch, current owner, and previous delimiter. `Returned.suffix` combines these actual data with the fixed `BodyPlan`. The caller cannot discard a Force return merely because it fails a newly introduced body-plan predicate. `Move` embeds every carrier move and every actual Return, then executes the native suffix. `ConstructorPrefix` describes its two exhaustive cases: still in the raw Force prefix, or a raw Return followed by a suffix prefix. The forward and reverse directions of `constructor_prefix_iff` are proved by finite induction. `resume_keeps_suffix` preserves the fixed source suffix across a raw resume.

`InvocationMove` adds actual begin/receipt/start phases around this construction. `invocation_every_prefix` classifies every finite invocation prefix, and `running_stays_running` excludes a fabricated jump back into entry. Zero-length and administrative prefixes are included. Divergence contributes all finite raw prefixes. No successful-return subset is substituted for the original carrier input.

These are constructors of a selected raw pair execution relation. They are not an assumed classification axiom for an independently fixed opaque `Inputs.execute`. Equality or relational correspondence with such a pre-existing execution relation remains a separate proof obligation.

## 5. Complete positive phase obligations and descriptor-sensitive returns

`ObservationReadout` separates raw execution from its decorated semantic interpretation. It supplies raw state/world to event and trace projections, the raw observation, the phase/checked-descriptor interface, and actual value/root readouts. It contains no whole source-typing or safety predicate. These projections are nevertheless real remaining inputs; this packet does not prove that an arbitrary map is the original readout.

`canonicalObservation` retains event coherence and the independent original observation guards, a complete current-world query, any actual result query at its checked descriptor, the full Force trace query while forcing, **all original `inputs.observationFields`**, and every remaining actual transition target. `canonical_retains_original_fields` and `canonical_every_continuation` expose this retention explicitly. Extra original positive fields are not dropped merely because the selected pair body is small.

The raw returned object and its checked result descriptor remain separate. `canonical_return_uses_checked_descriptor` and `return_descriptors_distinguished` ensure that the same actual return can demand different recursive membership at different result descriptors. The prior descriptor-erasure defect from the Function interpretation is not reproduced here.

The result is a constructed canonical positive phase program. A full identification of this program with the original complete interface's fixed `P_F` or `checkedObservation` has not been proved. Adding the original residual field to this program is not, by itself, a proof of that identification. Any fixed-original use must establish the complete interface/readout correspondence, including typed paths and current-event data.

`background_force_prefix` does apply the existing selected operator directly: from whole `B_H.Car`, an independent designated demand, and an actual raw Force observation, it obtains the Force incidence, full `B_H.T` trace, and full current `B_H.W`. It retains unfinished, pending, administrative, and complete observations through the unchanged original Force relation.

## 6. Full world construction and exact declared holes

`WorldRegistry` provides raw installed objects, alias/capture addresses and object equations, shared-witness references and values, and the complete original `WorldGuards`. `AliasData` and `CaptureData` contain raw bounds and lookup equalities, not recursive membership. `worldInputs` constructs the missing-native world interpretation from those data. Its other fields, including original checked domains and raw execution, are unchanged; `world_readout_keeps_domains` and `world_readout_keeps_raw_execution` prove the corresponding equalities.

`canonical_world` proves the full original `PhiW`: event coherence, all immediate world guards, aliases, captures, shared-witness agreement, and recursive validity of every installed entry. It quantifies **every** `bindings index = some object`, including indices beyond `count`. The count is allocation/bounds metadata, not a cutoff that can hide installed certificates. Alias, capture, and witness equations are derived from registry data. Recursive validity of installed values and carriers remains explicit.

`WorldRegistry.rebind` constructs the actual raw result-binding extension. `rebind_binding_fields` constructs all recursive fields from the old complete fields and the actual returned object. `rebind_world` combines them with the raw data readout equation to construct full `PhiW`. Freshness is explicit when claiming preservation of every old installed object: `rebind_preserves_every_old` requires that the fresh address was empty.

`PairAssignment.fromHeap` reads the two actual allocated handle values and roots through independent typed readouts. `PairAssignment.holes` permits only those two value tuples at their independently registered event positions. `exact_pair_holes` proves this inventory. There are no world, carrier, continuation, authority, or guard holes.

`pairRegistration` installs both values and both providers' complete lexical capture environments. The environment includes both new members and every old parent capture, not only the body Name that happens to be used. `FreshProviders` is the authentic raw freshness condition needed to preserve old provider captures; `pair_registration_old_capture` proves that preservation. A caller who supplies colliding provider identities has not thereby constructed the selected original source registration.

`pair_background_world` uses the exact two holes and all old background binding certificates to construct full `B_H.W`. It assumes the exact registry data equation and independent immediate guards, not ordinary completed opposite membership or a completed own-root world. It is a background theorem, **not** a `Meaning` theorem.

At an arbitrary actual Force return, `world_after_actual_force_return` obtains both the old complete world and the actual returned value by unfolding the whole background carrier and trace. `background_installed_restrict` transports every old value/carrier field; `pair_holes_future` supplies the hole action when original registered-position action is available. `returned_background_world` then builds the complete result extension. This is a direct operator application at the actual return, rather than an initial-installation-only argument.

## 7. First exact remaining construction

The next supplier is an actual raw-state to decorated-world readout with this equation at each original parameter binding:

```text
registry (readout.event (actual bindValue returnedWorld returnedValue ...))
  = (registry (readout.event returnedWorld)).rebind
      (Installed.value returnedDescriptor returnedValue returnedRoot)
      actualPostBindWorldGuards
```

This is a data equality, not a whole validity premise. It must retain the complete original `nu, K, D, eta`, current configuration, aliases, captured objects, and shared-witness positions. The matching Return readout must prove that the actual observation at the full carrier interface has `traceForm = pureReturn returnedTuple`, with the tuple's event equal to that observation's event. Current primitive/profile/world guards remain independent leaf obligations. The event action must be an actual lawful original future action, and it must preserve the two registered hole positions.

The existing raw heap and suffix equations provide the operational side of this construction. What is still missing is their full decorated interpretation at arbitrary post-Force/resumed worlds, including provider freshness and all old captures. Defining a convenient registry and asserting it equals an independently fixed one would leave this seam untouched. A missing-native interpretation may be constructed under the selected authority, but an already fixed interpretation requires its actual commutation proof.

After this readout construction, the complete canonical phase/interface interpretation must be connected to original `P_F` and original raw execution. Only then can the finite source phase argument supply the required postfixed source cases and hole replacement for `simultaneous_introduction`. This module neither assumes nor proves whole `sourceCases` or `replace`, and it does not apply that final theorem. The original `recursiveJointMemberWorld` atom, full Kernel, general Checking/L4, full Call, State, full native inference correspondence, and whole-language soundness remain open. No unsupported form in the parent language was removed or relabeled by the selected-pair scope.

## 8. Checked evidence and frozen inputs

The packet used 17 of 28 authorized focused calls. Every call used one CPU/thread, Lean `-j1 -M1024`, a 120-second wall cap, owned cache/TMPDIR, and a 1280 MiB aggregate RSS cap. Lean was 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. No shared build, Rust change, or repository import index was modified.

Final module check 15 and final audit check 17 exited zero with no diagnostics. The audit enumerated all 643 originating declarations, including private/generated declarations, and printed full types and axiom dependencies. It counted 240 theorem declarations and 69 public theorem roots. The only axiom dependencies were `propext`, `Classical.choice`, and `Quot.sound`; no project axiom or sorry dependency was accepted. Maximum observed audit RSS was 1,158,705,152 bytes, within the authorized cap.

The audit contains 13 probe/scaffolding theorem declarations. The substantive probes use nonconstant values: closures 80 and 81 and argument 77; an older nonempty lexical capture; genuine opposite-name resolution; the native Name receipt; arbitrary divergent prefixes; one request admitting two distinct responses; full parent/member captures; an installed entry at index 99 beyond count 3; and two checked result descriptors for the same raw return. These examples check discriminating behavior, not language completeness.

All failures and intermediate successes remain in `recursive-pair-r4/attempts` and `check/checkNN.log`. Checks 1–2, 5–6, 8, 10, 13–14, and 16 failed and are not counted as acceptance. Check 12 succeeded with deprecated-simp warnings, subsequently repaired. Check 16 failed only in audit probe elaboration; the corrected audit is check 17. The exact commands, resources, exit codes, source hashes, and log hashes are in `checks.json`.

| Frozen artifact | SHA-256 |
| --- | --- |
| `OriginalRecursivePair.lean` | `1069c185c6fa190c2a0dd776ebf4efc7bfab8ece7e36f2f4049d480e50fa65e7` |
| Final module olean | `58747837be01e03ae787b6fbd3db1aaead8eaddaf830aa42f525ddffb5730e00` |
| Audit source | `b821a5db9e56193d96cccffbce26ce92d50c1855b60714d464bd6e62ecf1efc5` |
| Full census/check 17 output | `9be3f5acd7593a32366e5cf584d62ac2124c8c70685a2487d5bf1caa14b437be` |
| Input manifest | `f1e5c12aa365b17e060c4d11da68c0770e001b8132db10f5b85ea5c14065e387` |
| Checker ledger | `a8aaab5fbb80aec39f417c881ed9362b16ea52cde387bf2afc6ad751c7046f8e` |

The parent baseline was `45d307a0`. The only deliberate dependency refresh was the parent's released Generation `0f25e53350edf9c452fd3c0f461602437ca2adf979859fda5e2492bcc403ae55`, published as `4c5fff3b2`; it was rebuilt in check 3. Byte-identical Interpretation `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` was rebuilt against it in check 4. The previous Generation and manifest are retained under `inputs-before-generation-release`. No later mutable sibling source was incorporated. The complete authority/dependency hashes and final olean hashes are in the input manifest.

Scratch evidence root: `/workspace/scratch/f98087c7ac1a/recursive-pair-r4`. The handoff and final freeze manifest identify the final prose bytes. Independent review must assess the source correspondence and exposed readout boundary as well as the checked theorem types; passing the Lean checker alone does not establish the missing original interpretation.
