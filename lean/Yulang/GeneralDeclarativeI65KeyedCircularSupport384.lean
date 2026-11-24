import Yulang.GeneralDeclarativeI65ExactDependencies384

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (Dictionary)

/-- A closed support family can distinguish two dictionaries at
one request. The selected rule and the chosen ordered where
dictionaries must have a child in the same closed family.
No assertion is made about existence of a different rule or
dictionary outside the family, nor about solver execution. -/
def ClosedDependency384 (closed : Request → Dictionary → Prop)
    (s : State) (source : ExactSelectedRule384) : Prop :=
  ∀ q needs key kids whereDicts,
    source s q needs key kids → kids.length = whereDicts.length →
    closed q (.node key whereDicts) →
    (∃ need ∈ needs, closed need.producer need.dictionary) ∨
    (∃ pair ∈ kids.zip whereDicts, closed pair.1 pair.2)

theorem exact_where_forest_same_length384
    {s source ordinary tagged qs ds}
    (proofs : ExactWhereForest384 source ordinary tagged s qs ds) :
    qs.length = ds.length := by
  exact ExactWhereForest384.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ => True)
    (motive_3 := fun qs ds _ => qs.length = ds.length)
    (fun _ _ _ _ _ => True.intro)
    True.intro
    (fun _ _ _ _ _ => True.intro)
    rfl
    (fun _ _ _ next => congrArg Nat.succ next)
    proofs

theorem keyed_closed_family_has_no_finite_selected384
    {s source ordinary tagged q d}
    (closed : Request → Dictionary → Prop)
    (byRule : ClosedDependency384 closed s source)
    (proof : ExactSelected384 source ordinary tagged s q d) :
    ¬closed q d := by
  exact ExactSelected384.rec
    (motive_1 := fun q d _ => ¬closed q d)
    (motive_2 := fun needs _ => ∀ need ∈ needs, ¬closed need.producer need.dictionary)
    (motive_3 := fun qs ds _ => ∀ pair ∈ qs.zip ds, ¬closed pair.1 pair.2)
    (fun rule _ kids ihNeeds ihKids inFamily => by
      obtain ⟨dep,found,belongs⟩|⟨whereItem,found,belongs⟩ :=
        byRule _ _ _ _ _ rule (exact_where_forest_same_length384 kids) inFamily
      · exact ihNeeds dep found belongs
      · exact ihKids whereItem found belongs)
    (fun _ empty => by cases empty)
    (fun _ _ _ first after dep found => by
      rcases List.mem_cons.mp found with rfl|later
      · exact first
      · exact after dep later)
    (fun _ empty => by cases empty)
    (fun _ _ first after dep found => by
      simp only [List.zip_cons_cons,List.mem_cons] at found
      rcases found with rfl|later
      · exact first
      · exact after dep later)
    proof

end Yulang.GeneralDeclarativeI65
