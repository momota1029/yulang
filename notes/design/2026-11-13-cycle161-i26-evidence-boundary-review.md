# Cycle 161: I-26 delayed-output guard and dictionary boundary

Read-only review after integration `62cba43b5` / I-26. This note changes no
Astra definition, guard, Step, Stable, or Evidence judgment. The new I-26
operational guard is not yet supplied by this documentation update.

## Existing exact boundary

`GeneralNominalSupportBoundary.SupportPending` is absence of any
`GeneralNominalSupport.DecisionGuard`. The Value counterpart is
`GeneralNominalValueBoundary.SupportPending`, using
`GeneralNominalValueSupport.DecisionGuard`. In both `fields` definitions,
`InspectionPending` includes `SupportPending` as its right disjunct.

`GeneralNominalLocalBoundary.SafeKnown` excludes `InspectionPending`.
Consequently, by eliminating `Local.selected`, existing `SupportPending`
already contradicts a selected local frontier, without extra assumptions
about K2 or root readiness. Each boundary's `support_pending` gives the
positive `.pending` frontier with root-ready, no-root-K2 and no-candidate-K2
premises. These premises matter: full-journal K2 retains rejection priority.
`local_correspondence` transfers these facts to `B4TargetV3.Local`.

Likewise `B4TargetV3.Classify.selected` requires `SafeKnown` at the root and
selected classification of every child. Existing support-pending therefore
excludes a selected completed dictionary at that demand. A parent with a
pending child cannot obtain selected completed classification through that
child. This is a classification/readback exclusion, not a negation of the
independent semantic Evidence predicate.

The guards currently in source do NOT implement the new delay policy merely
because they mention support. In particular,
`GeneralNominalValueSupport.Grounded.provisional` and `provisional_source`
allow certain unresolved producers with independently justified available
heads; `DecisionGuard` combines the older decision guard with `Supported`.
I-26's unsettled-output restriction must be mapped to Astra's new definitions
when they arrive. It must not be silently identified with existing
`SupportPending`, nor implemented by editing the existing guard here.

`GeneralNominalValueSteps.At.install` requires `PacketGuard`; its `Stable`
excludes enabled `At` actions at generated demands. `stable_committed` still
requires an explicit packet guard. Stability alone does not supply the guard
or discharge pending children. Ordinary constraints and administrative
transitions remain distinct from the installation guard.

## Why semantic witnesses are not forbidden emission

`GeneralDictionaryRecursiveEvidence.Instance` is model-indexed source
semantics with Finished, RequestReady, Metadata and BranchModels, and canonical
children. `Evidence` is `ErasedEvidence` over that Instance. Neither definition
requires Local.selected, a DecisionGuard, or an operational run.
`GeneralDictionaryFeedbackEvidence.evidence` is this same predicate; both
Support and Value boundary `remaining.Evidence` retain it unchanged.

Thus the proposed claim “guard pending implies no semantic Evidence in any
model” is not justified by the current definitions. Semantic possibility and
permission to construct a selected runtime dictionary are different. Adding
a guard to Evidence to force that claim would replace the independently
specified source judgment and is outside this work.

Cycle 161's request-identity lemmas and nonterminal BranchModels witnesses do
not invoke guarded installation or return an execution dictionary. The named
where-output fixture proves two actual-mode source requests and private
BranchModels only. The Evidence adapters require genuinely current child
Evidence explicitly. `NonterminalRecordedRevision.instance_from_trace`
obtains old Instance from a restricted trace and uses Certified backward model
preservation; it does not prove a new I-26 guard, unrestricted Value reachability,
or permission to select an unsettled demand. None is an operational bypass of
I-26, and none should be reported as completing that new obligation.

## Concrete next obligation after Astra publishes its guard

1. Identify the new guard-pending predicate, boundary `InspectionPending`,
   actual guarded Step, and any revised Stable definition by exact source name.
2. Prove guard-pending implies that boundary's InspectionPending. By existing
   SafeKnown exclusion, derive no Local.selected and no Classify selected
   dictionary. Preserve K2 priority; pending is not automatic when K2 holds.
3. Connect the actual executor's returned dictionary to selected classification
   via its existing/new execution bridge, rather than assuming that connection
   or negating semantic Evidence. Until that bridge is available, report only
   the independent classification exclusion.
4. Retest source-supported and discharged-output resumes, plus an unsettled
   producer with a pending child whose output is the only proposed input-head
   support. Keep its equations available to ordinary constraints and K2.

No new Lean theorem or general termination result is claimed by this note.
The unrestricted reachable/stable V5 evidence bridge remains open.
