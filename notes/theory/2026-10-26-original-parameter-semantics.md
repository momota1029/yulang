# Computed native parameter-world semantics

> **Source-generation update (2026-10-26).** The
> [formal Shared migration](2026-10-26-original-formal-shared.md) supersedes
> the statements below that the current Lambda builder lacks formal Shared
> or that the standard Parameter consumer inserts it into a separate tree.
> The current builder emits the original formal Shared and the Parameter
> consumer uses that exact tree. Earlier theorem inventories, hashes and
> missing-generation claims below describe their recorded baseline. The
> actual Build-description tie, complete decoded-event correspondence and
> whole original inference-soundness obligations remain separate.

This checkpoint constructs a missing native world presentation and proves its
complete parameter-bind `PhiW` update. The installed map, aliases and captures
are computed from native cells and saved references. The proof no longer needs
a post-bind `WorldRegistry` equation. Separate `Meaning` and `Background`
consumers use their own hereditary eliminators.

This is **not yet the full original source-owned post-Force world theorem**.
The full dependent correspondence between original source telescopes and this
new native presentation, authentic enclosing frame incidence, the actual
Force-to-formal result certificate, and legacy generated Shared delivery remain
open. Those boundaries are part of the result, not future assumptions hidden in
the world theorem.

The checked source is
`lean/YulangClosure/OriginalParameterSemantics.lean`, namespace
`YulangClosure.OriginalParameterSemantics`, SHA-256
`733c5b05e0db226f95d14ff2161c46e9a389b43d86b365b000a9656ec4fd0bd2`.
The 45,481 source bytes were frozen at 2026-10-26T16:45:04.468840+00:00.

## 1. Original source authority and scope

The selected immutable constructor case is governed by
`2026-10-08-simultaneous-immutable-root-introduction.md` §§2–5 and
`2026-10-08-recursive-original-interface-embedding.md` §§3–6.3.
Embedding §6.2 distinguishes two obligations:

- A genuinely missing native meaning can be defined on its complete data.
- An already fixed original meaning remains unchanged and needs its actual
  full-argument correspondence before identification with the native meaning.

The new `nativeSorts` and `inputs` belong to the first category. The product
roundtrips proved here do not supply the second category automatically.

SG, `2026-10-08-source-generalize-definition-and-proof.md` §3.3, places the
Parameter description above its invocation and retains rebind evidence at its
original Shared owner. It also distinguishes actual EventFields from
description-owned EventProofs. The Entry-Value and Entry-Retained rules in
`2026-10-07-call-input-construction-proof.md` §3.2 retain the original formal
endpoint, receipt, designated Force/result and binding ports. None of these
rules permits choosing a new formal contract after observing the Return.

The implementation preserves the accepted old core. It does not change
`sourceRules`, `Kernel`, `Checking`, `Inputs`, `Phi`, old decoder signatures,
Force/return-rebind admission, native Rust, or any earlier source module. No
old arbitrary `Inputs` is identified with the new world interpretation.

## 2. Replaying a typed prior telescope and reading the formal declaration

`Telescope s View scope` stores actual complete `Frame` records. Each frame has
the binder and payload kind of its indicated `ScopeEntry`. The frame's actual
event metadata and entry path remain untouched. `Telescope.values` extracts
the dependent `ScopeValues` from those same frames, and `replayTelescope`
feeds those frames to the original `decodeFrame` fold.

This supplies a concrete relation between the selected prior values and the
frames actually replayed. It does **not** authenticate that an arbitrary input
`scope` or those event parents were generated at an arbitrary enclosing source
occurrence. Binder/kind agreement is weaker than original source/event-parent
incidence. No first-invocation truncation, empty-parent fabrication or replacement
of an old Environment is performed.

`declareValueFormal` computes its selected contract from the full extracted
prior tuple and puts it at the original formal descriptor endpoint. Thus
`selected_at_original_formal` proves the endpoint equation rather than assuming
it. `declaration_uses_entire_prior` retains the complete explicit ambient list.

Two further roots tie this local operation to real syntax and decoding:

- `source_formal_description_binder` unfolds the actual root-Lambda source
  constructor and proves that its outer Description binder is the original
  formal's binder, before invocation.
- `formalDescriptionFrame` constructs that logical frame with supplied actual
  metadata; `decode_formal_description` proves that the original `decodeFrame`
  consumes it to produce `declareValueFormal`.

The root-Lambda constructor is the accepted `Parameter.source`, whose outer
Lambda mark has no annotation; its actual Formal annotation and entry mode
remain present. This is a local Description-frame consumer. There is no claim
that an unchanged legacy successful generation/execution derivation already
supplies all of these frames or the later formal Shared delivery.

## 3. Full typed Shared arguments, and the exact native-scope boundary

`SharedPosition s View` contains:

1. The original retained source owner.
2. All typed `ScopeValues s View` in that owner's telescope.
3. Its complete raw `SharedKey`, kept separately from the typed predecessor
   tuple.

`SharedReference` adds the use route while retaining that target. Two uses of
one target read the same supplied `ScopedShared` strategy. Conversely,
`shared_position_keeps_typed_prior` proves that different typed predecessor
tuples are not erased just because the raw key is equal. This does not require
raw-only reconstruction of Shared evidence.

There is a material boundary in the new native presentation:

```text
NativeWitness b View.shared : SharedPosition b View -> b.WitnessValue
```

but `nativeSorts b ...` replaces Configuration, Assignment and JointWitness.
Therefore this field does not automatically range over every preceding
`ScopeValues (nativeSorts b ...)` containing the new native snapshots and
logical fields. The native Event/Presentation product roundtrips below do not
construct that full dependent telescope correspondence. No theorem here
identifies all original Shared references, compatibility overlaps or arbitrary
native scoped strategies through that missing map.

Within its stated base-sort position domain, the strategy is fixed and its
arguments retain the complete typed prior. The current native witness field is
separate and may change. Preserving a fixed scoped strategy is not a proof that
the whole event witness, or the entire original pointwise world witness map,
must stay equal across arbitrary execution events.

## 4. A computed missing-native presentation

`Snapshot` retains the entire represented native `World`: environment arena,
cell store, receiving state, control and `Rest`. It also retains the provider
closure table, raw alias-reference records, and an opaque residual original
configuration field. Native alias references retain their declaration,
introduction route, saved environment and the two resolved names.

The data type permits arbitrary stores, dangling references and other
guard-failing records. It is not a subtype of successful decoding, safe states,
reached histories or source-image membership. An actual finite native vector
representation is a separate premise of the parameter-allocation constructor.

`NativeAssignment` contains the independent original assignment and the full
address/view interpretation. `NativeWitness` contains the independent current
witness plus the scoped strategy described above. No semantic membership
certificate or `WorldRegistry` is stored in these records.

`Presentation` gives the explicit complete native Event fields. `pack` and
`unpack` are actual record constructors/projections, and both inverse equations
are proved. These are roundtrips between `Event (nativeSorts ...)` and this
presentation. They are not a total identification with arbitrary pre-existing
world universes or with the whole Rust machine beyond the represented fields
and explicit residual data.

`initialRoot` constructs the initial decoder installed map from those native
fields. `initial_decoded_readout` proves the representation equation by
computation. This is a newly constructed native root. It is not a reset or
re-rooting of an existing original Environment, and it does not establish that
arbitrary later telescope replay preserves that equation without its own
constructor correspondence.

## 5. One fixed world readout

`inputs base references` defines the selected missing-native world fields once.
Its function does not take an eventual returned value or fresh address as a
parameter. The later bind changes event data, not that operator.

| World field | Actual computed source |
| --- | --- |
| Installed count | The current native store's allocator size. |
| Installed object at any index | `bindingReadout` of the actual cell using its address and view. Every `Some` is read, with no count or ownership-success filter. |
| Alias relation | Original alias-reference records and lookup of their two names in their saved native environment. |
| Captured address | The actual registered provider closure's saved environment and the body's resolved reference. |
| Captured value | The same installed-cell interpretation at that exact address. |
| Shared-position relation | Equality of the complete retained target, allowing distinct use routes. |
| Shared value | The supplied scoped strategy at that same complete target. |

No equality of raw values is used to establish a shared monomorphic contract.
`native_alias_same_cell` proves the actual native alias-append operation keeps
both handles at one existing cell. `nativeAliasData` then constructs the full
alias readout from that same cell and the real vector bound. The connection of
arbitrary publication identifiers to native addresses is not assumed or proved
by this helper. Source alias registration remains its own original incidence.

The capture readout deliberately leaves a dangling raw capture visible.
`dangling_capture_not_erased` proves that a resolved address with no cell still
appears in `capture`, while its `captureValue` is `none`. The proof does not
delete that record to make `CapturesAgree` true.

The `references : Body -> Nat -> Option Name` argument is the fixed resolved
body-reference data map used by these native operations. Its agreement with
every original source Body/compiled provider is not constructed here; that is
a separate source/native registration, not a semantic safety predicate hidden
in the readout.

Every nonworld field of the supplied operator is unchanged. In particular,
`native_inputs_keep_domains`, `native_inputs_keep_force` and
`native_inputs_keep_trace` retain the independent checking domain, raw Force
relation, trace form and complete observation fields. This packet does not
modify traceForm to obtain a desired result descriptor, purify a complete
effectful entry, erase pending observations, or add a source-image admission
restriction.

## 6. Native bind, old fields and the complete PhiW clause

`bindEvent` applies actual `SourceIdentityWorld.bindValue` with the given
existing parent node. It updates the derived contract at the fresh allocator
address, using the already selected formal descriptor. The current history and
independent eta/witness/scope/authority/incidence/dictionary fields come from
the current constructor data. The static fiber and eta0 remain fixed. Native
receiving/control/rest and the residual configuration are retained by this
plain bind substep; whole callback/receipt/pattern/ValueEntry behavior is not
identified with it.

`bind_installed` derives the full post-bind installed-map equation. It uses the
actual vector representation to prove that the fresh address was empty, applies
the native append/readout equation, and shows that changing the fresh address's
contract leaves the old populated readout unchanged. `bind_old_installed`
therefore preserves every old installed `Some`, including all original value
and carrier cases. The semantic quantifier remains unbounded.

`bind_capture_address` retains the actual saved lookup. More strongly,
`bind_capture_value` proves the complete captured-value readout is unchanged
under the changed derived assignment. It uses the old world's actual capture
equation and the new installed-map theorem. It is not an application of an
unchanged-assignment theorem to a changed assignment. Nonlatest saved
environments and formal shadowing are covered.

The actual raw existing-environment bounds are explicit:

- Every registered provider closure's saved environment predates the append.
- Every recorded alias's saved environment predates the append.

These are physical constructor invariants. They are not inferred from distinct
provider IDs, `SourcePair.Hygienic`, semantic typing, or a `PhiW` conclusion.
No provider or alias is erased when its invariant is unavailable; the local
preservation theorem requires the real invariant.

`bind_phiW` proves all conjuncts of the complete native world operator:

| PhiW conjunct | Proof source |
| --- | --- |
| Event coherence | The original independent current-event coherence evidence. |
| Registry/scope/current-authority/incidence guards | The original four current guard groups, unchanged by the readout definition. |
| Alias agreement | The old agreement, saved-reference lookup preservation and complete old-cell readout preservation. |
| Capture agreement | The old saved-address/cell equation, the new allocator bound and changed-assignment cell preservation. |
| Shared agreement | Applying the same scoped strategy to equal complete targets. |
| Every installed value/carrier certificate | Native append/readout: restrict each old actual certificate and use the actual returned-field certificate for the fresh cell. |

Its recursive premises are the prior `PhiW`, the candidate's restriction action
and the actual returned field. It does not assume the desired post-`PhiW`, a
whole `KernelSound`/`LocalLaws` package, or any post-registry commutation equation.
It is a computed world constructor, not the complete original execution proof.

## 7. Meaning, Background and the formal endpoint consumer

`meaning_installed_restrict` unfolds the selected greatest fixed point and
derives hereditary value/carrier restriction. `bind_meaning_world` unfolds the
old world certificate, calls the actual bind constructor and folds the
resulting `PhiW`. Thus its generic candidate restriction premise is discharged
by the actual `Meaning` clauses.

`bind_background_world` does the corresponding operation for `B_H`. It uses
`background_installed_restrict` and the original hole-position future action.
It never applies completed `Checking.sound` to a hole-relative interpretation.
There are no world holes: the prior Background world unfolds to the ordinary
world clause, and the post clause is folded through that same ordinary arm.

Both semantic consumers still require the **actual returned value certificate**
at the preselected descriptor, as well as the real compatible-event and
independent current guards. This file does not derive that certificate from an
actual Force observation. A prior world certificate is a natural recursive
input to the bind constructor; it is not a proof that the actual source Force
has produced that world and returned field.

`source_formal_phiW` removes a free target-descriptor choice from the local
source consumer. It selects `A` from the extracted complete prior tuple,
constructs the formal declaration, proves that its original endpoint reads
that same `A`, uses this Parameter's actual name, and proves the computed
post-bind `PhiW`. Its source/frame authenticity and returned-field premises
retain precisely the limits stated above.

## 8. Earliest missing original consumers

The original Lambda branch in `OriginalSourceGeneration.lean`, at the
`sourceRules` branch beginning with `.lambda mark formal pattern body`, emits
`sourceFormalRole` and, for Value entry, `receiptFormation` plus
`entryForceReturnRebind`. It opens the original receipt and Return suffix.
It does not emit an explicit `B <= A` CheckGoal or a semantic equation fixing
the actual designated Force result descriptor to the formal `A`.

The source theory's Entry-Value rule does fix the formal port and result rebind
at `A`. A genuine implementation must construct that port interpretation from
the complete Entry interface and its original Parameter owner, with the
contract fixed before Force. For an already fixed trace readout, its actual
same-port equation must be proved. This packet intentionally leaves the
existing `traceForm` unchanged; it does not invent a convenient equation or a
new observation restriction to apply the carrier eliminator.

If the actual Return instead supplies a certificate at `B`, an ordinary finite
check can only be used with its genuine original source incidence and completed
Meaning interpretation. A `B_H(B) -> B_H(A)` comparison needs its own
hole-respecting construction. Neither is supplied by a bare declaration that
the formal has descriptor `A`.

The other exact next consumers are:

1. A full dependent original/native telescope correspondence, including all
   Configuration, Assignment and JointWitness arguments. In particular it must
   address the `SharedPosition b` versus `ScopeValues (NS b ...)` boundary.
2. Authentic source-occurrence and event-parent incidence for the entire
   enclosing replayed telescope and the actual invocation/Force history.
3. Legacy source generation of formal Shared and consumption of the same
   actual retained anchor value, including pending histories without a
   fabricated Return. The current additive Description-frame theorem does not
   perform that migration.
4. A source-owned application connecting the newly installed Shared payload,
   Event-indexed native world readout and actual post-bind environment under
   the full dependent correspondence. The native world constructor alone does
   not identify every old decoded installed map with the new Event projection.

These are constructive representation/owner tasks. Their absence is not a
proof that the original theorem is impossible. General recursive L4, future
Function registration, arbitrary fixed old worlds and mutable State are not
closed by this local immutable constructor.

## 9. Discriminating coverage

| Required discriminator | Result and exact scope |
| --- | --- |
| Repeated Sites | The accepted stage1 coordinates distinguish original declarations and routes. This stage preserves the full owner/key; it does not repair every legacy Site lookup. |
| Same view, different cells | `same_view_distinct_cell_meanings` retains distinct address-indexed contracts for identical raw received values/views. |
| Nonlatest capture plus shadowing | `bind_capture_value` gives full changed-assignment readout preservation for every old registered saved environment. The actual source-formal name is used by `source_formal_phiW`. |
| Erased operation collision | Stage1's complete-key discriminator remains an unchanged dependency. No injectivity of legacy Runtime erasure is introduced here. |
| Two descriptions / proof uses | Different use routes retain one complete Shared target. Typed predecessor data remain separate and can distinguish actual scoped positions. No unproved base/native scope identification is claimed. |
| New current EventField, old Shared | `changed_current_keeps_old_shared` permits a different current witness while preserving each old base-sort scoped strategy value; `same_native_cells_different_scoped_values` shows that equal raw cells do not determine logical witnesses. |
| Payload B to preselected A | The formal endpoint equation and complete replayed prior are constructed. Actual semantic Entry-result incidence/comparison remains open. |
| Pending/divergence | `pending_has_no_returned_constructor` proves that an Outcome with no result cannot equal the actual Returned constructor. Force, trace and observation domains/fields stay unchanged. No eventual-return claim is made. |

## 10. Checks and evidence

The second stage was released at 16:29 UTC within the original 16:07:10–17:07:10
packet and the original 24-check total budget. This stage used six focused
checks, numbered 11–16; the combined author count is 16. Checks remained bounded
by 120 seconds, one CPU/thread, Lean `-j1 -M1024`, and 1280 MiB aggregate
process-group RSS. No timeout or RSS termination occurred.

Check 11 failed during local first-draft elaboration: an ActualEvent constructor,
sort transparency/rewrite issues and an untyped installed-object binder.
The failed snapshot is retained. The frame constructor was repaired to retain
complete supplied metadata rather than fabricate empty event paths. Checks
12–14 passed. The source was frozen after check 14. Checks 15 and 16 passed
the full origin and compiled-audit inventories without changing source bytes.

The complete originating inventory has 267 constants, including private and
generated declarations, 86 theorem constants and all 38 authored roots. Every
constant has its full type and transitive axiom report. Only the standard
`propext`, `Classical.choice` and `Quot.sound` occur. No project or unapproved
axiom was found. Current census, actual compiled census-module and final
closure-audit inventories are all zero.

The new isolated project/cache was copied from the exact frozen stage1 project,
then every source/config input was pinned and verified before checking. It was
not a new empty-cache proof of the entire dependency cone. The original
packet's empty-cache build and normal sandbox Lake startup failure remain in
the immutable stage1 evidence. Subsequent bounded calls used the explicitly
approved native Lake escalation; no toolchain/configuration workaround was
introduced. Independent acceptance requires the fresh nonauthor review.

All snapshots, failures, full reports and non-self-referential freeze metadata
are retained under `/workspace/scratch/f98087c7ac1a/parameter-semantics-r4/`.
No existing source, core, root import, configuration, shared status or Git state
was edited by this producer.
