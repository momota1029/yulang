# Cycle182: historical/live head-effect finite frame

Status: Draft, proved local support laws, not a completion of I-30.
Date: 2026-11-14 UTC.

## Scope and source

The additive `GeneralNominalCenteredHeadStepEffects.Models` predicate strengthens
core Models by every recorded effect's historical Holds and current Live
class equations. The centered-16/17 notes require these extra conjuncts;
cycle181's core frame alone does not preserve them. No target, Step, refresh,
readiness, coverage, or source-language rule is changed here.

`GeneralNominalHeadLedgerFrame182` builds finite lists from actual semantic
consumers: input-site endpoints/centers, head input-name capture endpoints and
binders, mode-sensitive schema support, and every retained output request target.
Historical support uses each Effect's own snapshot; live support uses the current
core. Full support includes cycle181's entire raw/core footprint and all these
effect lists. Lists may contain duplicates and need not be minimal.

## Exact claims

For all role declarations, arbitrary centered states, roots, plans, effects, and
assignments (no reachability or model inhabitation premise):

- `head_iff`: equality of assignments on `headSources plan` preserves exactly
  HeadEquations.
- `equal_outputs_iff`: equality on the targets of all class requests preserves
  EqualOutputs, including requests with no explicit schema entry.
- `output_iff`, `holds_iff`, `live_iff`, `effect_iff`: equality on the specified
  finite support preserves OutputEquations, historical Holds, live equations,
  and their conjunction respectively.
- `models_iff`: equality on `fullSources state` preserves the entire successor
  Models predicate in both directions. Its proof separately transports the
  core predicate and every historical/live effect pair.
- `models_assign`: for any finite indexed names/values, if every name is outside
  fullSources, updating those names preserves any given successor model.
- `request_target_mem`: every retained class-request target occurs in the output
  footprint, irrespective of explicit-schema coverage.
- `merged_target_mem`: for an actual merge function, an empty-output first site's
  class retains a registered second site's request target in this footprint.
  This does not prove the merge Step is enabled or that its models are inhabited.

Equality of complete assignment entries is sufficient; this is not claimed to
be a necessary or minimal frame. A frame does not construct models satisfying
new head/child equations, and it does not discharge selected availability,
LiveEffectsReady, or the original G EvidenceNode. Historical and live sources
are explicitly included, not inferred from agreement on the core journal.

## Nonempty regression

`GeneralNominalHeadLedgerFrameExample182` constructs an initial class with two
requests for the same output name, at targets 1 and 2. It proves its request
list is exactly those two entries. One assignment gives both the same nominal
carrier value; changing only target 2 to a provably distinct tower value breaks
EqualOutputs while target 1 is unchanged. Thus the full target support cannot
be replaced by the first request's target.

For any plan with no explicit associated equations, this class's output schema
and schema footprint are empty, so agreement on that schema footprint is
vacuous despite the failed EqualOutputs component. Both targets are nevertheless
in the new output footprint. The concrete class and assignments are constructed;
no Effect instance, enabled install, source-formation certificate, or reachable
merge is claimed. The generic plan lemma is explicitly conditional on its empty
associated list and is not used to assert an operational counterexample.

## Verification

Both new modules compile with Lean 4.35.0, `-j1 --trust=0
-DwarningAsError=true`, using the cycle182 dependency cache. The separate
`Audit/Cycle182HeadLedgerFrame.lean` checks all 20 public theorem declarations;
only propext, Classical.choice, and Quot.sound occur. No whole-library build
was run for these local additions.

Initial local checks failed on a simplification/transparency issue, an outdated
cache overlay, and a guessed empty-schema constant. These were corrected without
altering the statement. Successful final logs are `build-add.log`,
`example-build-final.log`, and `audit-complete.log` in the worker's verification
output, to be copied into cycle182's published evidence by the coordinator.
