# Cycle182: ordinary packet-report origin provenance

Status: proved bounded origin-support lemmas; original G EvidenceNode remains open.
Date: 2026-11-14 UTC.

## Diagnosis

`GeneralNominalCenteredAllocation.fresh_outside_raw_sources` excludes center
names from `GeneralNominalState.sources current.context.state`, not from the
larger `GeneralNominalRawFrame179.rawSources current`. The latter additionally
reads every historical packet's private state, report, generated schema, and
registered raw sites. These components must not be silently conflated.

A useful narrower fact can be proved for historical packet reports. Their
consumer is `GeneralNominalRecursiveCandidates.report`, not centered actual
inspection. This report starts `inspectMany` with all origin positions `none`.
Recursive nominal inspection can recover missing origins only from its state's
source slots. Structural and nominal projections retain the same origin root.

## Statements and proof

`GeneralNominalRawOrigin182.ReportRoots result names` bounds the source roots
of every report anchor/test and every captured `some origin` by a finite list.

- `inspect_roots` / `many_roots`: for any state, query family, bounds and supplied
  origins, if every state source slot and supplied origin root belongs to names,
  all resulting report roots do too. Mutual structural induction covers scalar,
  structural and nominal branches, both nominal endpoints, and missing origins.
  It does not require Finished, a model, reachability, or source completeness.
- `report_roots` / `report_sources_subset`: ordinary packet report support is a
  subset of its historical context's full `GeneralNominalState.sources` list.
  Its captures are not assumed absent: any recovered origin is explicitly bounded.
- `packet_context_pool`: given InitialSource, InstalledDepthBound and an actual
  original centered Steps trace, every registered packet's historical context
  sources lie in the finite allocation pool. The proof inducts over the trace;
  a new packet uses the pre-installation context, and old packets retain their
  historical context through administrative/refresh/install/merge transitions.
- `packet_report_pool`: combines these two independently proved facts.
- `fresh_outside_packet_report`: under the same source/depth/trace premises and
  packet membership, purposes >=7 are absent from that packet's report support.
  In particular this discharges the purpose8 report-origin branch.

The depth-bound premise is explicit. These lemmas concern the original centered
Step, not a hidden simulation of the successor HeadStep. The structural report
support theorem itself is state-generic and can be reused for another trace.

## Limits

No theorem here excludes center names from all of RawFrame179.rawSources.
Generated request target provenance, capture allocations, private-state support,
and raw-site observed origins remain separate obligations. Centered actual
inspection can start with center origins, unlike this ordinary packet report;
its support is not covered by the all-none specialization. Historical trace
pool containment is not an observation readback or a joint-model extension.

## Validation

Lean4.35.0 focused compile with `-j1 --trust=0 -DwarningAsError=true`, exit0.
`Audit/Cycle182RawOrigin.lean` audits the seven public theorems; dependencies are
only propext, Classical.choice and Quot.sound. The generic proofs retain no
unproved report provenance premise: only the explicit input-root/slot conditions,
discharged by the ordinary-report specialization. Initial local build needed
explicit reductions of the mutually recursive inspect/inspectMany branches;
subsequent build and final audit pass. No existing source was modified.
