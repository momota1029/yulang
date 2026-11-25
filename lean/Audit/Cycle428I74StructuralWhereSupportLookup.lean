import Yulang.GeneralDeclarativeI65I74StructuralWhereSupportLookup428

set_option backward.isDefEq.respectTransparency false
open Yulang.GeneralDeclarativeI65.I72
open Yulang.GeneralDeclarativeI65.StructuralWhere428
open Yulang.CommonRoleOutermostResolver (Summarizes)

/-- Structural regression on an explicitly nonempty proof forest:
the source is a real named derivation supplied at the indexed old
producer, and no new C15 output-bearing case is installed. -/
theorem actual_nonempty_legacy_support_head_is_the_original_proof428
    {B : SourcePrimitives} (incl : NamedRuleMap428 RepeatedCenters421.R13 B)
    {s : State} {needs} {need : OutputNeed s} {e : Event s need.producer} {tree}
    (source : SourceTrace RepeatedCenters421.R13 s need.producer tree (some e))
    (done : Summarizes tree (.selected need.dictionary))
    (eq : (e.outputs need.ordinal).receipt = need.expected)
    (tail : SupportForest RepeatedCenters421.R13 s needs) :
    ((transportOriginalSupport428 incl (.cons source done eq tail)).atOriginal 0 rfl).event = e ∧
      ((transportOriginalSupport428 incl (.cons source done eq tail)).atOriginal 0 rfl).source =
        (mapNamedTrace428 incl source).val :=
  ⟨rfl,rfl⟩

#print axioms lookup_after_rule_inclusion_is_the_same_original_producer428
#print axioms old_support_at_original_position_keeps_event_and_receipt428
#print axioms transported_existing_support_keeps_literal_output_and_same_model428
#print axioms actual_nonempty_legacy_support_head_is_the_original_proof428
