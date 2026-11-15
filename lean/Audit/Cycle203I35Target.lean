import Yulang.GeneralDictionaryAllocDefaultCounterexample202
import Yulang.GeneralNominalCenteredHeadAllocV7Composition

/- Exact I35 alias check against the already published, inhabited default fixture.
   This is revalidation, not a new counterexample or a repaired evidence judgment. -/
example : ¬ Yulang.GeneralNominalCenteredHeadAllocV7Composition.EvidenceNode
    Yulang.GeneralDictionaryAllocDefaultSource202.roles :=
  Yulang.GeneralDictionaryAllocDefaultCounterexample202.not_v7_evidenceNode

#print axioms Yulang.GeneralDictionaryAllocDefaultCounterexample202.not_v7_evidenceNode
#print axioms Yulang.GeneralDictionaryAllocDefaultCounterexample202.selected_inhabited_stable
#print axioms Yulang.GeneralDictionaryAllocDefaultCounterexample202.actual_default
#print axioms Yulang.GeneralNominalCenteredHeadAllocV7Composition.composition
#check Yulang.GeneralNominalCenteredHeadAllocV7Composition.GeneratedChildren
