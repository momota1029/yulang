# Cycle 227: semantic first-introduction footprint for V8

## Status and recovery

Started 2026-11-16T23:31:55Z. Latest user instruction overrides the older
25-minute inbox cap: 55 minutes inclusive, with proof/review work until about
45 minutes and final verification/publication reserved afterward.
Read standing orders and inbox from integration/m1-final df788d507, including
I-42 and I-43. No STOP. Cycle226 was completed and published at43ee67402;
there was no held226 artifact to recover. Cycles220/222–225 were already public.
Integration was merged; the barrel and heartbeat conflict retained prior new
imports and the current cycle state. Audit.lean and README are byte-identical
to df788d507, as I-43 requires; the old freeze repair was not repeated.

**Result: 24 new modules, 222 audited constants, four independent audits.**
The actual V8 boundary now has a trace-selected finite semantic footprint,
and the first p0/p1 occurrence is localized to an actual enabled installation's
explicit residual sources. This is progress toward I-41(4), not EvidenceNode
completion. No language decision, new selected-input gate, or new transition.

## Proved statements and their hypotheses

All statements quantify over arbitrary well-typed roles, registry, context,
root, assignments, plans and traces unless restricted below. Names in the
module index below identify every new declaration.

1. LiveDelta/ClassDelta/NameDelta: on an actual installation, total packet plus
   old/new live classes is exact. Historical class transport only reads newly
   requested names and targets whose name class changed. Existing-name body
   obligations transport through equal targets. Both old class interpretations
   and request inclusion are explicit premises; no-new-requests gives no delta.
2. ReachableRest: given a current Frame and Models state model, total packet
   Holds iff raw merge equations and Rest (head/emitted/child schemas/sites).
   Input site and capture Fits follow from the existing model/head schema,
   rather than remaining separate obligations. No source, point-root,
   ground-root, coverage or path assumptions are needed for this local result.
3. HistoricalBody/OriginClass: Finished and headSchema in both assignments
   turn equality on origin roots into Equivalent input values, then total
   expression equivalence. Explicit bodies retain all output binders; defaults
   retain positional reads. The new list is not claimed a subset of the old
   syntactic list. Registered plans obtain the schema premises from Models.
4. OriginJournal/SemanticTrace: actual Step traces yield a finite Footprint
   whose agreement preserves the entire Models predicate, including live and
   snapshot effects. Initial support includes raw semantic sources and the
   root site. Administrative/refresh steps add no delta. No point-root premise
   is needed. First-introduction returns the actual contributing event and
   prefix/suffix, not only an abstract occurrence in a list.
5. FootprintCenters/RequestSeparation/EffectProvenance: on InitialSource plus
   an actual trace, requested output targets are separated from fresh purposes
   other than2/5. For p0/p1, class/delta reads already belong to registered input
   centers, themselves in the old pool. Output-equality merges also introduce
   none. Every first p0/p1 occurrence therefore belongs to an installation
   packet. No InstalledDepthBound is used.
6. PointCaptureSupport/BinderProvenance/HeadFootprint: given Footprint, current
   Frame, Models and a headSchema witness, a nonzero point capture is already
   protected. An absent lower endpoint forces semantic top; an absent upper
   endpoint forces semantic bottom. Non-eight fresh input binders and the
   actual-mode current headSchema sources are therefore already protected.
   The top/bottom exceptions are retained, not dismissed.
7. CaptureDichotomy: for any current capture with both endpoint sources
   nonzero, at least one endpoint is protected. The headSchema supplies its
   observation. CapturePatch: any simultaneous change outside pool+[0]
   preserves the full journal and Fits for each observed current capture.
   The changed assignment is not assumed to satisfy the headSchema separately.
8. EmittedFootprint/FirstPacketTail/FirstResidual: any actual-mode total RHS
   read of a p0/p1 identity is old-pool protected, even for unscoped names.
   The precise remaining list is raw merge atom sources, emitted equation
   targets/nonactual reads, and child site/schema sources. Enabled.common
   supplies the needed model/head witness in the first-introduction theorem;
   no extra satisfiability premise is imposed on the global trace statement.
9. V8Footprint/V8Residual: for every actual B4TargetV8.Reachable state of the
   HeadSharingBoundary220 boundary, one context/pool is selected before any
   assignment or p0/p1 identity query. The pool preserves Models and every
   protected p0/p1 has an actual first enabled installation in the residual
   list, with prior absence and original suffix trace. This is not yet a
   local-ownership or ProtectedOverlap theorem.
10. FootprintRegression: the real Default206 installation still retains the
    int model and rejects the bottom model. The unchanged historical default
    class contributes an empty delta. Existing199/202/204/206/218 regressions
    were included through the focused regression roots, not replaced.

## Verification

All builds used Lean4.35, --wfail and bounded focused targets. Successful
commands and complete compact outputs are recorded below. Counts are Lake's
cached dependency-graph counts, not newly rebuilt modules. Full repository
build/verify-lean.sh was deliberately not run per standing orders. No CI PASS
is claimed. Separate trust=0 audits scan every constant in each new module and
reject dependencies other than propext, Classical.choice and Quot.sound.

Intermediate namespace/type elaboration errors (including the final wrapper's
ResidualSources capitalization and Agree namespace) were corrected before
publication. No proof holes, new axioms or native_decide. git diff --check
passed. Previously published Lean files remain unchanged; Yulang.lean only
has imports appended. Prior audits were not edited. Integration's frozen
Audit.lean/README bytes were checked directly.

### `lake build Yulang.GeneralDictionaryHistoricalLive227 --wfail`

Exit0.
```text
Build completed successfully (1342 jobs).
```

### `lake env lean --trust=0 Audit/Cycle227Delta.lean`

Exit0.
```text
CYCLE227-DELTA-PASS: 56 constants in 5 modules
```

### `lake env lean --trust=0 Audit/Cycle227Origins.lean`

Exit0.
```text
CYCLE227-ORIGINS-PASS: 98 constants in 7 modules
```

### `lake env lean --trust=0 Audit/Cycle227Final.lean`

Exit0.
```text
CYCLE227-FINAL-PASS: 54 constants in 8 modules
```

### `lake env lean --trust=0 Audit/Cycle227Residual.lean`

Exit0.
```text
CYCLE227-RESIDUAL-PASS: 14 constants in 4 modules
```

### `lake build Yulang.GeneralDictionaryV8Residual227 Yulang.GeneralDictionaryCapturePatch227 Yulang.GeneralDictionaryFootprintRegression227 Yulang.GeneralDictionaryHeadSharingPrior220 Yulang.GeneralDictionaryHeadSharingRegression220 --wfail`

Exit0.
```text
Build completed successfully (1430 jobs).
```

## Publication and remaining obligations

Checkpoint1: remote035a9371, 12 changed paths, matched the fetched tree.
Checkpoint2: remote2a6b89be, 10 changed paths, matched the fetched tree.
Checkpoint3: remote3c35e56c, 12 changed paths, matched the fetched tree.
Heartbeats were independently published at start/10/20/30/40-minute intervals;
40-minute head2b5ecd6d. The initial ten-minute timestamp estimate was corrected
in the subsequent heartbeat. Final publication includes every remaining verified
module, its separate audit, the design/report and completed heartbeat. No
publication hold and no approval/error block occurred. Only work/dots-main was
written. Final SHA/tree equality is checked after publication and reported to
the parent; repository-wide CI remains unverified here.

Next obligations:
1. Reconstruct/replay historical same-key merge extrema for the residual's
   merge atoms, emitted targets and lower/upper reads. Pool monotonicity does
   not prove absence or local ownership of those identities.
2. Carry that simultaneous extension through child site/schema support,
   retaining total explicit/default outputs, live effects and snapshots.
3. Close ProtectedOverlap/ChoiceCompatible and the unconditional selected V8
   EvidenceNode, using registered certificate replay where appropriate.

No new closed counterexample and no semantic question requiring the user were
found. A raw bottom-to-int obstruction is already rejected by Prepared;
journal-only refinements are a risk to analyze, not a proved refutation.
Full EvidenceNode and B4 completion remain open. No Yulang2 execution.
Usage quota unknown. Focused proof work, review and tests continued through
approximately45minutes; final report/publication/verification are within the
55-minute inclusive cap.

## New declaration index

Each row lists declarations in its new module; namespaces and hypotheses are
in the source and the statement summary above. Compiler-generated constants
are also covered by the audits.

- `GeneralDictionaryBinderProvenance227`: `point_singleton`, `binder_mem`, `fresh_binder_mem`, `merge_binder_mem`.
- `GeneralDictionaryBodyProvenance227`: `externalSources`, `head_roots_subset`, `body_subset`, `fresh_ne_zero`, `output_separate`, `external_provenance`, `body_provenance`, `class_provenance`, `delta_provenance`, `merge_body_provenance`.
- `GeneralDictionaryCaptureDichotomy227`: `top_not_bottom`, `endpoint_mem`, `captured_endpoint_mem`.
- `GeneralDictionaryCapturePatch227`: `capture_fits`, `finite_capture_fits`.
- `GeneralDictionaryClassDelta227`: `newRequests`, `mem_new`, `affected`, `mem_affected`, `deltaSources`, `body_support`, `target_support`, `class_forward`, `class_iff`, `delta_subset`, `no_new`.
- `GeneralDictionaryEffectProvenance227`: `history_prior`, `install_prior_or_packet`, `output_atoms_separate`, `merge_prior`, `first_packet`, `first_merge_packet`.
- `GeneralDictionaryEmittedFootprint227`: `nonoutput_binder_mem`, `any_binder_mem`, `actual_reads_mem`, `schema_residual`.
- `GeneralDictionaryFirstPacketTail227`: `tailSources`, `packet_prior_or_tail`, `first_merge_tail`.
- `GeneralDictionaryFirstResidual227`: `emittedResidual`, `ResidualSources`, `tail_prior_or_residual`, `first_merge_residual`.
- `GeneralDictionaryFootprintCenters227`: `site_center`, `emitted_center`, `centers`, `registered_input_centers`, `frame_input_centers`.
- `GeneralDictionaryFootprintRegression227`: `pool`, `footprint`, `dependency`, `strict_default_change`, `unchanged_delta`.
- `GeneralDictionaryHeadFootprint227`: `roots_mem`, `head_mem`, `merge_head_mem`.
- `GeneralDictionaryHistoricalBody227`: `headRoots`, `input_equivalent`, `explicitSources`, `bodySources`, `explicit_value_equivalent`, `body_iff`, `registered_body_iff`.
- `GeneralDictionaryHistoricalLive227`: `historySources`, `history_iff`, `installDelta`, `install_depends`, `mergeDelta`, `merge_depends`, `history_subset`, `history_empty`.
- `GeneralDictionaryLiveDelta227`: `installation_iff`, `installDelta`, `install_depends`, `delta_subset`.
- `GeneralDictionaryNameDelta227`: `body_target`, `newNames`, `mem_newNames`, `newNames_new`, `deltaSources`, `body_support`, `target_support`, `equal_forward`, `class_forward`, `class_iff`, `delta_subset`, `names_covered`.
- `GeneralDictionaryOriginClass227`: `classSources`, `class_iff`, `deltaSources`, `body_support`, `target_support`, `equal_forward`, `relative_forward`, `relative_iff`, `delta_subset`, `names_covered`.
- `GeneralDictionaryOriginJournal227`: `historySources`, `history_iff`, `installDelta`, `install_depends`, `mergeDelta`, `merge_depends`.
- `GeneralDictionaryPointCaptureSupport227`: `point_capture_mem`, `fresh_point_capture_mem`, `absent_capture_fits`, `absent_lower_top`, `absent_upper_bottom`, `lower_mem_of_not_top`, `upper_mem_of_not_bottom`.
- `GeneralDictionaryReachableRest227`: `centered_projection`, `raw_projection`, `head_iff_merges`, `capture_fits`, `Rest`, `restSources`, `rest_iff`, `packet_characterization`, `packetSources`, `packet_iff`.
- `GeneralDictionaryRequestSeparation227`: `child_target_separate`, `raw_target_separate`, `request_separate`, `class_reads_center`, `delta_reads_center`, `body_reads_center`, `merge_delta_reads_center`.
- `GeneralDictionarySemanticTrace227`: `Contribution`, `Contribution.step`, `classify`, `Contribution.depends`, `initialSources`, `Footprint`, `Footprint.path`, `Footprint.depends`, `from_path`, `Footprint.introduced`, `Contribution.nonempty_kind`, `Footprint.first_introduced`, `initial_fresh_absent`, `Footprint.fresh_first`.
- `GeneralDictionaryV8Footprint227`: `reachable_footprint`, `uniform_pool`, `uniform_tail_pool`, `patch_preserves`.
- `GeneralDictionaryV8Residual227`: `uniform_residual_pool`.
