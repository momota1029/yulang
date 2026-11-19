import Yulang.GeneralRebaseDiagnosticV6268

namespace Yulang.GeneralRebaseDiagnosticV8268
open CommonRoleOutermostResolver (Frontier)
open GeneralRebaseDiagnosticData268 (Inputs Valid priority priority_sound multiple k2)
open GeneralRebasePartialBool268 (Answer Reflect either either_sound)

/-- Either overlay has the same priority-ambiguity rule. It is safe to
combine them with a partial disjunction; neither masks a K2 rejection. -/
def conflicts (x : Inputs Demand) : Answer := either x.sharingConflict x.mergedConflict

def run (x : Inputs Demand) : Option (Frontier Demand) :=
 match conflicts x with
 | none => none
 | some false => GeneralRebaseDiagnosticV6268.run x
 | some true =>
   match priority x with
   | none => none
   | some true => some .ambiguous
   | some false => some .rejected

theorem conflicts_sound (b : B4TargetV8.SourceBoundary v) (r : v.Registry) (s : v.State) (d : v.Demand)
 (x : Inputs v.Demand) (valid : Valid b r s d x) :
 Reflect (b.SharingConflict r s d ∨ b.MergedOutputConflict r s d) (conflicts x) :=
 either_sound valid.sharingConflict valid.mergedConflict

theorem sound (b : B4TargetV8.SourceBoundary v) (r : v.Registry) (s : v.State) (d : v.Demand)
 (x : Inputs v.Demand) (valid : Valid b r s d x) (found : run x = some result) :
 B4TargetV8.Local b r s d result := by
 have flags := conflicts_sound b r s d x valid
 cases checks : conflicts x with
 | none => simp [run,checks] at found
 | some bVal =>
   rw [checks] at flags
   cases bVal with
   | false =>
     have sharing : ¬ b.SharingConflict r s d := fun h => flags (Or.inl h)
     have merged : ¬ b.MergedOutputConflict r s d := fun h => flags (Or.inr h)
     exact .ordinary sharing (.ordinary merged (GeneralRebaseDiagnosticV6268.sound b r s d x valid
       (by simpa only [run,checks] using found)))
   | true =>
     have prio := priority_sound b r s d x valid
     cases order : priority x with
     | none => simp [run,checks,order] at found
     | some override =>
       rw [order] at prio
       cases override with
       | false =>
         simp only [run,checks,order,Option.some.injEq] at found
         subst result
         by_cases sharing : b.SharingConflict r s d
         · exact .sharingRejected sharing prio
         · exact .ordinary sharing (.mergedRejected (flags.resolve_left sharing) prio)
       | true =>
         simp only [run,checks,order,Option.some.injEq] at found
         subst result
         by_cases sharing : b.SharingConflict r s d
         · exact .sharingAmbiguous sharing prio
         · exact .ordinary sharing (.mergedAmbiguous (flags.resolve_left sharing) prio)

structure Complete (x : Inputs Demand) : Prop where
 rootPending : x.rootPending ≠ none
 rootK2 : x.rootK2 ≠ none
 candidateK2 : x.candidateK2 ≠ none
 inspection : x.inspection ≠ none
 survivors : x.survivors ≠ .deferred
 chosenOutput : ∀ key kids, x.survivors = .unique (key,kids) → x.outputConflict key ≠ none
 mergedConflict : x.mergedConflict ≠ none
 sharingConflict : x.sharingConflict ≠ none

theorem total_priority (x : Inputs Demand) (complete : Complete x) : priority x ≠ none := by
 apply GeneralRebasePartialBool268.total_both
 · exact GeneralRebasePartialBool268.total_neg (GeneralRebasePartialBool268.total_both
      (GeneralRebasePartialBool268.total_neg complete.rootPending)
      (GeneralRebasePartialBool268.total_either complete.rootK2 complete.candidateK2))
 · cases h : x.survivors with
   | deferred => exact False.elim (complete.survivors h)
   | none | unique | ambiguous => simp [multiple]

theorem total_v6 (x : Inputs Demand) (complete : Complete x) :
 GeneralRebaseDiagnosticV6268.run x ≠ none := by
 cases p : x.rootPending with
 | none => exact False.elim (complete.rootPending p)
 | some pending =>
   cases pending with
   | true => simp [GeneralRebaseDiagnosticV6268.run,p]
   | false =>
     have total := GeneralRebasePartialBool268.total_either complete.rootK2 complete.candidateK2
     cases h : k2 x with
     | none => exact False.elim (total h)
     | some unsafeFlag =>
       cases unsafeFlag with
       | true => simp [GeneralRebaseDiagnosticV6268.run,p,h]
       | false =>
         cases i : x.inspection with
         | none => exact False.elim (complete.inspection i)
         | some needs =>
           cases needs with
           | true => simp [GeneralRebaseDiagnosticV6268.run,p,h,i]
           | false =>
             cases v : x.survivors with
             | deferred => exact False.elim (complete.survivors v)
             | none | ambiguous => simp [GeneralRebaseDiagnosticV6268.run,GeneralRebaseDiagnosticV6268.known,p,h,i,v]
             | unique item =>
               rcases item with ⟨key,kids⟩
               cases e : x.outputConflict key with
               | none => exact False.elim (complete.chosenOutput key kids v e)
               | some conflict =>
                 cases conflict <;> simp [GeneralRebaseDiagnosticV6268.run,GeneralRebaseDiagnosticV6268.known,p,h,i,v,e]

theorem total (x : Inputs Demand) (complete : Complete x) : run x ≠ none := by
 have known := GeneralRebasePartialBool268.total_either complete.sharingConflict complete.mergedConflict
 cases eq : conflicts x with
 | none => exact False.elim (known eq)
 | some conflict =>
   cases conflict with
   | false => simpa only [run,eq] using total_v6 x complete
   | true =>
     cases order : priority x with
     | none => exact False.elim (total_priority x complete order)
     | some isAmbiguous => cases isAmbiguous <;> simp [run,eq,order]

theorem exact_of_complete (b : B4TargetV8.SourceBoundary v) (r : v.Registry) (s : v.State) (d : v.Demand)
 (x : Inputs v.Demand) (valid : Valid b r s d x) (complete : Complete x) (result : Frontier v.Demand) :
 run x = some result ↔ B4TargetV8.Local b r s d result := by
 constructor
 · exact sound b r s d x valid
 · intro actual
   cases h : run x with
   | none => exact False.elim (total x complete h)
   | some found =>
     have same := B4TargetV8.local_functional (sound b r s d x valid h) actual
     cases same
     rfl

end Yulang.GeneralRebaseDiagnosticV8268
