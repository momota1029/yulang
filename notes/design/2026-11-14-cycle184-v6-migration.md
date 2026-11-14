# I32: evidence migration map, not a completed transfer

Late integration0b2a6b482 supplies I32. Target for the next bridge is
`GeneralNominalCenteredHeadWFBoundary.boundary` / `B4TargetV6`.
I32 explicitly permits finishing current originalG work. Cycle184 ends with
its originalG local mechanism proofs intact, not relabeled as V6 proofs.

## Verified type distinction

`HeadWFBoundary.reachable_old` targets HeadStepBoundary, not original
`CenteredGroundBoundary.groundBoundary`. `HeadStepEffects.State` wraps a
centered core plus an effect list. Its Models requires core Models AND, for
every recorded effect, both installation-snapshot Holds and current-state Live.
The latter includes output equations that can acquire new requests after
class growth. `RootExtension184.root_extension_iff` only preserves the old
centered Models and core fullSources, not this stronger model predicate.

The strict type inspection is `Audit/Cycle184MigrationTypes.lean` and
`notes/verification/cycle184/migration-types.txt`, exit0. Focused WFTransfer
build also passed. This checks existing APIs, not a new transfer theorem.
V6.Local.selected additionally excludes OutputConflict; that condition is
not erased into a V5 selected constructor by this cycle.

## Three next proof families

1. **head_trace_packet_support** (proposed, not defined): induct on actual
   HeadStepKernel.Step traces from HeadStepEffects.initial. Prove packet
   context/private-source pool inclusion, seed identity and Linked. Use
   HeadStepTrace.configuration_trace, HeadStepAncestry.installed_depth_bound /
   reservations_finite, HeadStepEnumeration.source_pool. Installation uses
   enabled.frame.context_eq, registry_eq and visible. Do not assume a core
   simulation to old FeedbackSteps.Installable / DecisionGuard. This should
   supply WF-specific purpose≥7 raw exclusion.
2. **head_trace_site_producers** (proposed): registered core sites are initial
   rootSite or emitted by registered core plans; plans retain input
   registration, seed and declaration visibility; root identity is a lower
   bound. Induct the actual HeadStepKernel.At, using frame.center_recorded.
   Pure syntactic ChildCoherence184 and HeadTransport184.head_schema_eq can
   be reused only after these new trace premises are supplied. Recover root
   occurrence uniqueness before reusing the root-overlap proof pattern.
3. **head_effects_models_frame** (proposed): define/support all recorded
   Effect.Holds and Effect.Live output schemas, then prove agreement on that
   support preserves HeadStepEffects.Models. Show whether core fullSources
   already covers this support; do not assume it. InstallationModels also
   needs post-install output equations and old effects' post-install Live.
   A finite binder extension alone is not that common witness.

Independent read-only review agreed with these obstacles. Existing
HeadWFTransfer proves Exact/saturation/order transfer and other structural
facts; no claim here converts them into general DictionarySound or closes
EvidenceNode. This is a proof decomposition, not a new language semantics
choice, so no question note is required.
