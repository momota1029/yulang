import Yulang.GeneralNominalCenteredHeadMatSemanticAncestry

/-! Finite field readback retains arbitrary record tails. The tail is tested
only through ordinary field observations, without treating it as a row binder. -/
namespace Yulang.GeneralNominalCenteredHeadMatRecordReadback
open GeneralDeclarationPatterns GeneralPatternNormalForm
open GeneralNominalCenteredHeadMatPatternSemantics
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra application)
open CommonNominalFullCarrier

def entries : Pattern → List (Nat × Pattern)
  | .record label payload tail => (label,payload) :: entries tail
  | _ => []

def tail : Pattern → Pattern
  | .record _ _ rest => tail rest
  | other => other

def fold (fields : List (Nat × Ty)) (rest : Ty) : Ty :=
  fields.foldr (fun field value => record field.1 field.2 value) rest

def NoFields (value : Ty) : Prop :=
  ∀ depth rank env label obs,
    ¬ CommonNominalFullDemand.ProbeAt Common.rowLe rank env (observeTy depth value) (.field label obs)

def AllFields (value : Ty) : Prop :=
  ∀ label, CommonNominalFullDemand.ProbeAt Common.rowLe 0
    ⟨fun _ => .bottom,fun _ => []⟩ (observeTy 0 value) (.field label .trivial)

theorem labels_entries (pattern : Pattern) : (entries pattern).map Prod.fst = fields pattern := by
  cases pattern with
  | record label payload rest => simp only [entries,fields,List.map_cons,labels_entries rest]
  | _ => rfl

theorem eval_fold (pattern : Pattern) :
    eval semantics variables pattern =
      fold ((entries pattern).map fun entry => (entry.1,eval semantics variables entry.2))
        (eval semantics variables (tail pattern)) := by
  cases pattern with
  | record label payload rest => simp only [entries,tail,List.map_cons,fold,List.foldr_cons,eval,eval_fold rest]
  | _ => rfl

theorem tail_not_record (pattern : Pattern) : ∀ label payload rest, tail pattern ≠ .record label payload rest := by
  cases pattern with
  | record label payload rest => exact tail_not_record rest
  | _ => intros; simp only [tail]; intro same; cases same

theorem tail_closed (pattern : Pattern) (closed : pattern.variables = []) : (tail pattern).variables = [] := by
  cases pattern with
  | record label payload rest => exact tail_closed rest (List.append_eq_nil_iff.mp closed).2
  | _ => exact closed

theorem tail_normal (pattern : Pattern) (normal : Normal pattern) : Normal (tail pattern) := by
  cases pattern with
  | record label payload rest =>
      simp only [Normal] at normal
      exact tail_normal rest normal.2.1
  | _ => exact normal

theorem member_closed (member : (label,payload) ∈ entries pattern) (closed : pattern.variables = []) :
    payload.variables = [] := by
  cases pattern with
  | record name value rest =>
      rcases List.mem_cons.mp member with equal | member
      · cases equal; exact (List.append_eq_nil_iff.mp closed).1
      · exact member_closed member (List.append_eq_nil_iff.mp closed).2
  | _ => cases member

theorem member_normal (member : (label,payload) ∈ entries pattern) (normal : Normal pattern) : Normal payload := by
  cases pattern with
  | record name value rest =>
      simp only [Normal] at normal
      rcases List.mem_cons.mp member with equal | member
      · cases equal; exact normal.1
      · exact member_normal member normal.2.1
  | _ => cases member

theorem entries_mass (pattern : Pattern) :
    (entries pattern).length + 1 + ((entries pattern).map fun field => field.2.encode.size).sum ≤ pattern.encode.size := by
  cases pattern with
  | record name value rest =>
      have prior := entries_mass rest
      simp only [entries,List.length_cons,List.map_cons,List.sum_cons,Pattern.encode,Roles.Term.size,Roles.argsSize] at *
      omega
  | var => exact Nat.le_refl _
  | app | variant | join =>
      simp only [entries,List.length_nil,List.map_nil,List.sum_nil,Pattern.encode,Roles.Term.size,Roles.argsSize]
      omega

theorem terminal_fields (pattern : Pattern) (closed : pattern.variables = [])
    (normal : Normal pattern) (terminal : ∀ label payload rest, pattern ≠ .record label payload rest) :
    NoFields (eval (algebra constructors interpretation) variables pattern) ∨
      AllFields (eval (algebra constructors interpretation) variables pattern) := by
  cases pattern with
  | var name => cases closed
  | join => simp only [Normal] at normal
  | record label payload rest => exact False.elim (terminal label payload rest rfl)
  | variant tag payload => exact Or.inl (by intro depth rank env label obs; cases rank <;> exact id)
  | app name arguments =>
      simp only [eval,algebra,application]
      split
      · rename_i primitive found
        cases primitive with
        | scalar | emptyRecord | exactEmpty =>
            cases arguments with
            | nil => exact Or.inl (by intro depth rank env label obs; cases rank <;> exact id)
            | cons => exact Or.inr (by intro label; trivial)
        | pair =>
            cases arguments with
            | nil => exact Or.inr (by intro label; trivial)
            | cons first rest =>
                cases rest with
                | nil => exact Or.inr (by intro label; trivial)
                | cons last rest =>
                    cases rest with
                    | nil => exact Or.inl (by intro depth rank env label obs; cases rank <;> exact id)
                    | cons => exact Or.inr (by intro label; trivial)
      · split
        · exact Or.inl (by intro depth rank env label obs; cases rank <;> simp [observe_nominal,CommonNominalFullDemand.ProbeAt,CommonNominalFullDemand.ProbeStep,CommonNominalFullDemand.MaskedProbeStep])
        · exact Or.inr (by intro label; trivial)

variable {fields : List (Nat × Ty)}

theorem fold_absent (absent : label ∉ fields.map Prod.fst) :
    CommonNominalFullDemand.ProbeAt Common.rowLe rank env (observeTy depth (fold fields rest)) (.field label obs) ↔
      CommonNominalFullDemand.ProbeAt Common.rowLe rank env (observeTy depth rest) (.field label obs) := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
      have different : label ≠ field.1 := fun same => absent (List.mem_cons.mpr (Or.inl same))
      have absentTail : label ∉ fields.map Prod.fst := fun member => absent (List.mem_cons_of_mem _ member)
      change CommonNominalFullDemand.ProbeAt _ _ _ (.record field.1 _ _) _ ↔ _
      rw [CommonNominalFullDemand.probeAt_record_field,ite_eq_right different]
      exact ih absentTail

theorem fold_field (unique : (fields.map Prod.fst).Nodup) (member : (label,value) ∈ fields) :
    CommonNominalFullDemand.ProbeAt Common.rowLe rank env (observeTy depth (fold fields rest)) (.field label obs) ↔
      CommonNominalFullDemand.ProbeAt Common.rowLe rank env (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (.node value)) obs := by
  induction fields with
  | nil => cases member
  | cons field fields ih =>
      rcases List.mem_cons.mp member with equal | member
      · cases equal
        change CommonNominalFullDemand.ProbeAt _ _ _ (.record label _ _) _ ↔ _
        rw [CommonNominalFullDemand.probeAt_record_field,ite_eq_left rfl]
      · have different : label ≠ field.1 := by
          intro same
          exact (List.nodup_cons.mp unique).1 (same ▸ List.mem_map.mpr ⟨(label,value),member,rfl⟩)
        change CommonNominalFullDemand.ProbeAt _ _ _ (.record field.1 _ _) _ ↔ _
        rw [CommonNominalFullDemand.probeAt_record_field,ite_eq_right different]
        exact ih (List.nodup_cons.mp unique).2 member

theorem fold_presence (empty : NoFields rest) (unique : (fields.map Prod.fst).Nodup) :
    CommonNominalFullDemand.ProbeAt Common.rowLe 0 env (observeTy 0 (fold fields rest)) (.field label .trivial) ↔
      label ∈ fields.map Prod.fst := by
  constructor
  · intro seen
    by_cases member : label ∈ fields.map Prod.fst
    · exact member
    · exact False.elim (empty 0 0 env label .trivial ((fold_absent member).mp seen))
  · intro member
    obtain ⟨field,present,equal⟩ := List.mem_map.mp member
    subst label
    exact (fold_field unique present).mpr (CommonNominalFullDemand.probeAt_trivial ..)

theorem empty_tail_of_finite (finite : Equivalent (fold fields rest) (GeneralNominalStructuralReadback.recordValues other))
    (cases : NoFields rest ∨ AllFields rest) : NoFields rest := by
  rcases cases with empty | full
  · exact empty
  · let label := (fields.map Prod.fst ++ other.map Prod.fst).foldr Nat.max 0 + 1
    have beyond : ∀ x ∈ fields.map Prod.fst ++ other.map Prod.fst, x < label := by
      intro x member
      have member_max (xs : List Nat) : ∀ x ∈ xs, x ≤ xs.foldr Nat.max 0 := by
        induction xs with
        | nil => intro x member; cases member
        | cons head rest ih =>
            intro x member
            rcases List.mem_cons.mp member with rfl | later
            · exact Nat.le_max_left ..
            · exact Nat.le_trans (ih x later) (Nat.le_max_right ..)
      have upper := member_max _ x member
      exact Nat.lt_succ_of_le upper
    have one : label ∉ fields.map Prod.fst := by intro h; exact Nat.lt_irrefl _ (beyond _ (List.mem_append_left _ h))
    have two : label ∉ other.map Prod.fst := by intro h; exact Nat.lt_irrefl _ (beyond _ (List.mem_append_right _ h))
    have seen := (fold_absent (rest := rest) one).mpr (full label)
    have transferred := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (finite.2 0) 0
      ⟨fun _ => .bottom,fun _ => []⟩ (.field label .trivial) seen
    exact False.elim (two ((GeneralNominalRecordInversion.field_presence other label).mp transferred))

end Yulang.GeneralNominalCenteredHeadMatRecordReadback
