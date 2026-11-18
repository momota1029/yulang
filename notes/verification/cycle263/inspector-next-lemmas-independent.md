# Independent next-cycle interface review: inspector, prospective selection, projection

Read the coordinator's current `next-source-obligations.md` (shared tree, read-only) and the actual named interfaces below. This is a research note, not a new theorem or runtime change. Highest priority is distinguishing current-candidate discovery from historical live-effect bookkeeping before claiming a finite-state source decoder.

## Two concrete obstructions to a direct decoder/install claim

1. `GeneralRebaseMultiSource263.selected source = source.plans.map Selection.ofPlan`. Actual source Initial is a lifted legacy initial with versioned plans empty. Therefore, if inspect(finite initial) is required to equal that source initial, UniversalObserver.observe is empty and its checked run returns immediately. It cannot discover the first Plan. The coordinator is adding the tiny initial-boundary audit; no duplicate code is proposed here.
2. Every selected registered Plan in a source-reachable snapshot is already committed: `GeneralNominalVersionedMixedPlanLedger235.reachable_plan_committed`. `MixedKernel234.At.install` requires `¬ Committed before effect.plan`. Thus a strict finite write for the same retained Plan CANNOT be identified with a fresh source installation of that Plan. Current writes account for live ClassEffects of past installations, not prospective source candidate discovery.

A finite-state-to-source function selected by arbitrary reachable witnesses does not solve either obstruction. Likewise, equality of finite projections need not identify source states: the universal address state omits raw source context, aliases/edges, retained Plan snapshots, Effect frames, and journal ordering. At minimum, one must prove the selected abstraction is sufficient for next-observation functionality or expose a simulation relation instead of assuming a decoder inverse.

## Suggested next 3 lemma packages, in order

### 1. `prospective_frame_checked_effect` (proposed name)

Start with an actual reachable source state and an actual current local selected frontier for demand/key/children, rather than a member of `state.plans`.

Use:
- `GeneralNominalVersionedMixedSelectedFrame235.source_frame`: Reachable + source Local(.selected key children) yields an actual current Plan Frame and the exact ordered children.
- `GeneralNominalVersionedMixedFrameSelection235.selected_identifies`: current Frame yields selected key/children identity; this does NOT prove Plan uniqueness.
- `GeneralRebaseClassCheck261.actual_ready`, together with `GeneralRebaseExecutableRequests262.requests_eq`: checker success on the actual root's requests yields actual Ready.
- `GeneralNominalVersionedMixedFrameSelection235.effect_of_selected`, `effect_registry`, `effect_snapshot`, `effect_plan`: package the actual Frame/selected/Ready into a versioned Effect with exact provenance.

Target: an Effect whose registry, current snapshot, Plan, root and ordered children exactly match the actual current selection, with no assumption that the Plan was already registered. Keep `Generated` explicit where finite prospective-owner coverage needs it.

This is a proof-level candidate construction: `source_frame` and `effect_of_selected` do not provide an executable search procedure. The source frontier interface is noncomputable. Do not call this an executable enumerator, and do not use `FrameFunctional232.frame_plan_unique` globally: it requires singleton declaration/raw-site/center storage.

### 2. `prospective_effect_current_install` (proposed name)

Connect the Effect from lemma 1 to an actual source install only after producing the missing fields of `GeneralNominalVersionedMixedCurrentCandidate235.Current`:

- exact registry/snapshot/occurrence;
- translated complete emitted schema;
- ChoiceCompatible;
- selected Plan's cycle/inspection positions and all alternatives safe;
- a joint model of `GeneralNominalVersionedInstall232.InstallationModels`.

Then `GeneralNominalVersionedMixedCurrentCandidate235.source_installable` obtains mixed Installable from Current + source Reachable + source Local. It already derives cache via `GeneralNominalVersionedMixedEmbedding234.source_cache` and safety via the selected frontier. There is no need to reprove those two guards independently. With actual Generated and novelty, construct `.install` and the actual source Step.

The candidate's finite owner coverage should use `GeneralNominalSourceOwnerCandidates252.mixed_finite_owners`, which is explicitly prospective but requires Generated + Installable + novelty. The cycle263 `RegisteredOwners263` theorem alone covers historical membership and is not a replacement. Request coverage comes from `SourceRequestPool262.mixed_finite_requests` at the actual pre/post reachable snapshots.

Do not mistake output checking for full packet completion. `GeneralRebaseBodyDecoder260.compile/successful` compiles one requested body. `GeneralRebaseOutputDecoder260.compile/successful` checks capture-report compilation plus emitted equations, not complete source guards or a journal model. For semantic assembly, `GeneralNominalVersionedPacketFrame236.holds_shape` lists HeadModels, input holds, captures, head schema, nonactual emitted equations, child obligations and Outputs. `VersionedInstall232.InstallationModels` additionally preserves all old legacy/versioned live effects. The concrete `GeneralRebaseMergeFrame261.frame` and `GeneralRebaseMergePacket261.packet_holds/evidence` are useful fixture bridges but not general source installation theorems.

### 3. `live_projection_transition` (proposed name, start relationally)

Before attempting a pure decoder, define the finite abstraction of an actual source snapshot by accumulating current proposals for its retained Plans:

`liveFacts s := (selected s).flatMap (proposal s.core)`

`alpha s := write (initial universalBasis) (liveFacts s)`

Use source_bounds to prove every live fact lies in the one source-derived basis. Then prove the concrete transition square on this abstraction, separately by source action:

- **Install:** old Plans persist; old requests are included in the new current requests (`GeneralNominalVersionedInstall232.requests_included`), and a new Plan is consed. StableClass monotonicity and `GeneralRebaseWriteAlgebra259.append/commute/batch_exact` should give `alpha after = write (alpha before) (liveFacts after)`. This is potentially a batch of finite writes, not necessarily exactly one. The batch must rescan historical Plans at the after-snapshot because new sites can introduce new live requests. Do NOT equate it with just the new Plan's before-snapshot proposal.
- **Refresh/reobserve:** actual Plans are unchanged; `GeneralNominalVersionedRefresh232.refresh_requests/reobserve_requests` prove request-membership equivalence, so the live-fact abstraction should stutter. Ordering differences, if any, must be handled by membership/filter equality, not assumed list equality.
- **Equate:** current implementations preserve sites/aliases and registered Plans, so the live-request abstraction should stutter, although raw constraints changed.
- **Merge:** aliases grow and requests can expand for multiple old Plans. Prove projection growth and a rescan batch; do not classify every merge as stuttering.
- **Enqueue:** on a generated actual source path, use the existing generated-registration/absence contradiction as in `RegisteredSites263.origin`, rather than assuming arbitrary enqueue changes nothing.

This gives a source-transition-to-finite-projection theorem, not an executable new solver. To turn it into `inspect : finiteState -> sourceState`, additionally prove that the abstraction/retained finite source data determines the relevant prospective observations and install successor, or specify a canonical reconstructed machine and prove a simulation relation. Neither independent snapshot reachability nor arbitrary witness choice establishes this functionality.

## Exact stopping boundary

The projection can strictly grow or stutter on a source step. Only its strict changes consume the finite K*(N+N*N) budget. Refresh/reobserve stuttering can continue indefinitely in the old machine; the existing 239/240 phenomena are not removed by this square. No old Acc, fairness, complete source compiler, EvidenceNode, or source acceptance decision follows automatically. The useful next-cycle result is an actual candidate/Effect/current-install interface plus a correctly directed projection square, with these limitations explicit.
