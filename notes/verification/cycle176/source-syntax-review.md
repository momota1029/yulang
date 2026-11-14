# Fresh integration cf6e source-syntax review

Read design note and GeneralNominalCommonTrustedLedger, ReachableSchemas,
SourceInitialization directly at cf6e554f292c15102fc7a18da3e22a2adb5ed610.
No source/cache edits or builds.

The ten new modules do not directly close the I30 G candidate installation
producer. They explicitly leave the centered boundary unchanged.

- ReachableSchemas opens GeneralNominalActualInspectionSteps. Its path is old
  actual Step over Tracked, not centered Step. No unrestricted centered erasure
  theorem is provided. CenteredPointMergeExample already shows exact erasure
  can fail, so these actual-path hypotheses cannot be silently substituted.
- reachable_all_models / reachable_trusted_models show an ACTUAL current model
  satisfies coarse trusted facts. trusted_inhabited assumes current-model
  existence. This is weakening into a coarse predicate, not construction of one
  model satisfying both a centered journal and a prospective packet.
- CommonTrustedLedger.trusted_append/common_ledger combine finite Trusted
  derivations/facts. They do not prove arbitrary model intersection inhabited,
  Joint for an alias class, nor TrustedInputs. inputs_append/inputs_replace
  preserve previously supplied coarse TrustedInputs; uniform equality only
  under actual current models is explicitly insufficient for replacement.
- reachable_promoted_output still takes TrustedInputs as an explicit premise.
  It supplies labelled output/readback coverage, not ValueSupport.PacketGuard
  for every centered candidate or raw MergesClosed.
- SourceInitialization.initial_trusted_inputs is only the empty-ledger case.
  inconsistent_accessible is old actual-inspection accessibility when models
  are empty; it neither proves centered nonvacuity nor closes EvidenceNode.

Reusable direction: source-template/canonical-schema lemmas are generic, as
are coarse ledger concatenation and capture comparisons under their stated
uniform model premises. A centered reachable_all_models analogue can be proved
by actual centered trace induction without exact erasure (cycle176's ledger
work appears to cover this direction already). The stronger prospective-plan
common-model/support/Joint obligations remain explicit. No target switch or
new general closure claim is warranted.
