# Cycle 181: next provenance proofs (read-only analysis)

## Exact finite footprint

`GeneralNominalRawFrame179.fullSources s = rawSources s.erased.current ++ GeneralNominalCenteredFrame179.ledgerSources s`.

Raw part:
1. Current `GeneralNominalState.sources`: slot type/row names, reservations, names in ordinary atoms.
2. Each historical packet: private-context sources; report-context sources; root names of report anchors/tests/capture origins; generated-schema test roots; each generated use's origin root plus total capture output and input endpoint names.
3. Raw sites: argument endpoints and root names of their optional observed inputs.

Ledger part:
4. Centered sites: argument endpoints and actual centers.
5. Each registered plan's equations: its input site; capture endpoint/binder names for input or Needed names; head/input/named schemas (test roots and each use's origin root, binder, total capture output, input endpoints); every requirement's child site and child schema.

## Purpose-8 cases

For `c = fresh seed invocation declaration 8 name 0`, current raw source membership is ruled out by `GeneralNominalCenteredAllocation.fresh_outside_raw_sources`, given InitialSource, InstalledDepthBound and a centered path. Supporting facts: `GeneralNominalCenteredEnumeration.source_pool`, `.slot_pool`, `GeneralNominalCenteredAllocation.outside_pool`, `.key_purpose`, `.fresh_namespaces`. Initial names are below seed; ordinary allocation purposes are <=6. Seed alignment is essential.

This does NOT immediately rule out the whole raw footprint: historical report/generated roots and raw-site observed roots are separate lists, not current raw state sources. Raw observed sites can carry centered binder roots after emission. Trace facts `GeneralNominalCenteredTrace.centered_site_registered`, `.raw_site_centered`, `.generated_centered`, `.recorded_trace` recover origins of these sites. Historical private source support can use `GeneralNominalAllocationSupport.private_sources`, `.checks_sources`, `.merges_sources`, `.extend_sources`, applied at its installation snapshot; historical report/generated roots still need a syntax-support induction.

Ledger centers can be an input binder (purpose8), reused point source, or emitted compound center (purpose9); initial root centers are purpose7 or reused endpoints. `GeneralNominalCenteredAllocation.compound_center_identity`, `.fresh_namespaces`, and `GeneralNominalBinderIdentity181.binder_fresh`/`.binder_collision_iff` separate the allocated cases. Reused centers require ancestry, not only namespace arithmetic.

Important: `variableSources` includes `plan.binder entry.name` even for lower/upper-mode uses whose semantic clause never reads that binder. `captureSources` likewise includes Needed names, not just actual head uses. Therefore fullSources membership is an overapproximation of semantic dependency. A blanket claim “every purpose8 member is an actual head use” is not justified by the definitions. First classify all binder mentions; then either prove well-formed actual-use coverage or sharpen the frame to remove irrelevant binder mentions.

## Three concrete next lemma targets (not yet proved)

1. **Reachable purpose-8 footprint provenance.** Under InitialSource, depth bound, seed agreement and centered path to `s`, if `fresh seed inv decl 8 name 0 ∈ fullSources s`, then `∃ old ∈ s.plans, ∃ oldName, old.binder oldName = fresh seed inv decl 8 name 0`. Prove by state-step induction, with cases for retained historical packets and raw/centered site provenance. Do not strengthen conclusion to actual head-use membership without a separate proof.

2. **Registered binder mention coverage or frame pruning.** For a registered plan, a non-output/non-point `oldName` contributing a binder to equationSources, establish either an actual use in one of the registered head/input/named/child schemas at that binder, or a frame theorem showing this particular binder occurrence is semantically irrelevant and may be omitted. A head-only conclusion needs an additional syntactic justification. This addresses the lower/upper-mode overapproximation explicitly.

3. **Current nominal candidate origin linkage.** For a current linear Candidate and a registered actual-use witness at the same purpose8 identity, prove existence of `rename` with `currentOrigin = mapSource rename use.origin` and `RootRecorded currentState rename use.origin`, using refreshed/merged ordinary equations. Namespace collision gives invocation/declaration/name only, not this projection-path or root-alias fact. Once it holds, `GeneralNominalLedgerReadback181.registered_alias_readback` discharges overlap without any execution-path premise.

The old registered readback itself is now path-free: `Models s m` already carries every registered Plan.Equations. Reachability is required for the missing syntactic classification and origin-linkage producers, not for evaluating an already supplied actual-use witness.
