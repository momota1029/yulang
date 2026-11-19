import Yulang.GeneralRebaseDiagnosticV8268

namespace Yulang.GeneralRebaseConsensusDiagnostic268
open CommonRoleOutermostResolver (Frontier)
open GeneralRebaseDiagnosticData268 (Inputs Valid priority priority_sound)
open GeneralRebaseDiagnosticV8268 (conflicts conflicts_sound Complete)

def overlay (x : Inputs Demand) : Option (Frontier Demand) :=
 match priority x with
 | none => none
 | some true => some .ambiguous
 | some false => some .rejected

def agree (ordinary special : Option (Frontier Demand)) : Option (Frontier Demand) :=
 match ordinary,special with
 | some .ambiguous,some .ambiguous => some .ambiguous
 | some .rejected,some .rejected => some .rejected
 | _,_ => none

theorem agree_iff (ordinary special : Option (Frontier Demand)) (result : Frontier Demand) :
 agree ordinary special = some result ↔ ordinary = some result ∧ special = some result ∧
   (result = .ambiguous ∨ result = .rejected) := by
 cases ordinary with
 | none => simp [agree]
 | some one =>
   cases special with
   | none => cases one <;> simp [agree]
   | some two =>
     cases one <;> cases two <;> cases result <;> simp [agree]

/-- An unknown overlay is harmless if both possible branches already agree.
This is not a guess that the unknown overlay predicate is false. -/
def run (x : Inputs Demand) : Option (Frontier Demand) :=
 match conflicts x with
 | some false => GeneralRebaseDiagnosticV6268.run x
 | some true => overlay x
 | none => agree (GeneralRebaseDiagnosticV6268.run x) (overlay x)

theorem ordinary_sound (b : B4TargetV8.SourceBoundary v) (r : v.Registry) (s : v.State) (d : v.Demand)
 (x : Inputs v.Demand) (valid : Valid b r s d x)
 (clear : ¬ (b.SharingConflict r s d ∨ b.MergedOutputConflict r s d))
 (found : GeneralRebaseDiagnosticV6268.run x = some result) :
 B4TargetV8.Local b r s d result :=
 .ordinary (fun h => clear (Or.inl h)) (.ordinary (fun h => clear (Or.inr h))
   (GeneralRebaseDiagnosticV6268.sound b r s d x valid found))

theorem overlay_sound (b : B4TargetV8.SourceBoundary v) (r : v.Registry) (s : v.State) (d : v.Demand)
 (x : Inputs v.Demand) (valid : Valid b r s d x)
 (blocked : b.SharingConflict r s d ∨ b.MergedOutputConflict r s d)
 (found : overlay x = some result) : B4TargetV8.Local b r s d result := by
 have order := priority_sound b r s d x valid
 cases p : priority x with
 | none => simp [overlay,p] at found
 | some choice =>
   rw [p] at order
   cases choice
   · have eq : Frontier.rejected = result := by simpa only [overlay,p,Option.some.injEq] using found
     subst result
     by_cases share : b.SharingConflict r s d
     · exact .sharingRejected share order
     · exact .ordinary share (.mergedRejected (blocked.resolve_left share) order)
   · have eq : Frontier.ambiguous = result := by simpa only [overlay,p,Option.some.injEq] using found
     subst result
     by_cases share : b.SharingConflict r s d
     · exact .sharingAmbiguous share order
     · exact .ordinary share (.mergedAmbiguous (blocked.resolve_left share) order)

theorem sound (b : B4TargetV8.SourceBoundary v) (r : v.Registry) (s : v.State) (d : v.Demand)
 (x : Inputs v.Demand) (valid : Valid b r s d x) (found : run x = some result) :
 B4TargetV8.Local b r s d result := by
 have overlayCheck := conflicts_sound b r s d x valid
 cases c : conflicts x with
 | none =>
   have agreed := (agree_iff _ _ _).mp (by simpa only [run,c] using found)
   by_cases blocked : b.SharingConflict r s d ∨ b.MergedOutputConflict r s d
   · exact overlay_sound b r s d x valid blocked agreed.2.1
   · exact ordinary_sound b r s d x valid blocked agreed.1
 | some bit =>
   rw [c] at overlayCheck
   cases bit
   · exact ordinary_sound b r s d x valid overlayCheck (by simpa only [run,c] using found)
   · exact overlay_sound b r s d x valid overlayCheck (by simpa only [run,c] using found)

theorem preserves (x : Inputs Demand) (old : GeneralRebaseDiagnosticV8268.run x = some result) :
 run x = some result := by
 cases c : conflicts x with
 | none => simp [GeneralRebaseDiagnosticV8268.run,c] at old
 | some bit =>
   cases bit
   · simpa only [run,GeneralRebaseDiagnosticV8268.run,c] using old
   · cases h : priority x with
     | none => simp [GeneralRebaseDiagnosticV8268.run,c,h] at old
     | some bit => cases bit <;> simpa only [run,GeneralRebaseDiagnosticV8268.run,overlay,c,h] using old

theorem exact_of_complete (b : B4TargetV8.SourceBoundary v) (r : v.Registry) (s : v.State) (d : v.Demand)
 (x : Inputs v.Demand) (valid : Valid b r s d x) (complete : Complete x) (result : Frontier v.Demand) :
 run x = some result ↔ B4TargetV8.Local b r s d result :=
 ⟨sound b r s d x valid,fun actual => preserves x
   ((GeneralRebaseDiagnosticV8268.exact_of_complete b r s d x valid complete result).mpr actual)⟩

/-- Known-safe-to-reject K2 is not blocked by missing overlay answers. -/
theorem known_k2 (x : Inputs Demand) (known : x.rootPending = some false)
 (k2Flag : GeneralRebaseDiagnosticData268.k2 x = some true) :
 run x = some .rejected := by
 have order : priority x = some false := by
   simp [priority,known,k2Flag,GeneralRebasePartialBool268.neg,GeneralRebasePartialBool268.both]
   cases GeneralRebaseDiagnosticData268.multiple x.survivors <;> rfl
 have ordinary : GeneralRebaseDiagnosticV6268.run x = some .rejected := by
   simp [GeneralRebaseDiagnosticV6268.run,known,k2Flag]
 cases h : conflicts x with
 | none => simp [run,h,overlay,order,ordinary,agree]
 | some bit => cases bit <;> simp [run,h,overlay,order,ordinary]

end Yulang.GeneralRebaseConsensusDiagnostic268
