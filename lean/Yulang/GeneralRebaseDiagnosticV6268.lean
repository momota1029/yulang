import Yulang.GeneralRebaseDiagnosticData268

namespace Yulang.GeneralRebaseDiagnosticV6268
open CommonRoleOutermostResolver (Frontier)
open GeneralRebaseDiagnosticData268 (Inputs Valid k2 k2_sound SurvivorSound)
open GeneralRebasePartialBool268 (Reflect)
open GeneralRebasePartialClassification267 (Verdict)

def known (x : Inputs Demand) : Option (Frontier Demand) :=
 match x.survivors with
 | .deferred => none
 | .none => some .rejected
 | .ambiguous .. => some .ambiguous
 | .unique (key,kids) =>
   match x.outputConflict key with
   | none => none
   | some true => some .rejected
   | some false => some (.selected key kids)

def run (x : Inputs Demand) : Option (Frontier Demand) :=
 match x.rootPending with
 | none => none
 | some true => some .pending
 | some false =>
   match k2 x with
   | none => none
   | some true => some .rejected
   | some false =>
     match x.inspection with
     | none => none
     | some true => some .pending
     | some false => known x

theorem known_sound (b : B4TargetV8.SourceBoundary v) (r : v.Registry) (s : v.State) (d : v.Demand)
 (x : Inputs v.Demand) (valid : Valid b r s d x) (safe : B4TargetV8.SafeKnown b r s d)
 (found : known x = some result) :
 B4TargetV6.Local b.toV7.toV6 r s d result := by
 have survivors := valid.survivors
 cases status : x.survivors with
 | deferred => simp [known,status] at found
 | none =>
   simp only [known,status,Option.some.injEq] at found
   subst result
   rw [status] at survivors
   exact .rejected ⟨safe.1,Or.inr (Or.inr ⟨safe.2.2.2,Or.inl survivors⟩)⟩
 | unique item =>
   rcases item with ⟨key,kids⟩
   rw [status] at survivors
   have output := valid.outputConflict key
   cases conflict : x.outputConflict key with
   | none => simp [known,status,conflict] at found
   | some b =>
     rw [conflict] at output
     cases b with
     | false =>
       simp only [known,status,conflict,Option.some.injEq] at found
       subst result
       exact .selected safe survivors output
     | true =>
       simp only [known,status,conflict,Option.some.injEq] at found
       subst result
       exact B4TargetV6.output_conflict_rejected safe survivors output
 | ambiguous one two =>
   rcases one with ⟨a,xs⟩
   rcases two with ⟨z,ys⟩
   simp only [known,status,Option.some.injEq] at found
   subst result
   rw [status] at survivors
   exact .ambiguous safe survivors.2.1 survivors.2.2 survivors.1

theorem sound (b : B4TargetV8.SourceBoundary v) (r : v.Registry) (s : v.State) (d : v.Demand)
 (x : Inputs v.Demand) (valid : Valid b r s d x) (found : run x = some result) :
 B4TargetV6.Local b.toV7.toV6 r s d result := by
 have pending := valid.rootPending
 cases pre : x.rootPending with
 | none => simp [run,pre] at found
 | some p =>
   rw [pre] at pending
   cases p with
   | true =>
     simp only [run,pre,Option.some.injEq] at found
     subst result
     exact .pending pending
   | false =>
     have cycle := k2_sound b r s d x valid
     cases chk : k2 x with
     | none => simp [run,pre,chk] at found
     | some c =>
       rw [chk] at cycle
       cases c with
       | true =>
         simp only [run,pre,chk,Option.some.injEq] at found
         subst result
         exact .rejected ⟨pending,cycle.imp_right Or.inl⟩
       | false =>
         have noRoot : ¬ b.RootK2 r s d := fun h => cycle (Or.inl h)
         have noCandidate : ¬ b.CandidateK2 r s d := fun h => cycle (Or.inr h)
         have sampling := valid.inspection
         cases inspection : x.inspection with
         | none => simp [run,pre,chk,inspection] at found
         | some i =>
           rw [inspection] at sampling
           cases i with
           | true =>
             simp only [run,pre,chk,inspection,Option.some.injEq] at found
             subst result
             exact .inspectionPending pending sampling noRoot noCandidate
           | false =>
             exact known_sound b r s d x valid ⟨pending,noRoot,noCandidate,sampling⟩
               (by simpa only [run,pre,chk,inspection] using found)

end Yulang.GeneralRebaseDiagnosticV6268
