import Yulang.GeneralDeclarativeI65I74OpenTailIsolation414

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.OpenTail414
open GeneralDeclarativeI65
open Checker408 (Problem)
open CommonNominalFullCarrier (Ty record subtype_refl)

def modelWithTail414 {s q} (a : OpenInput s q) (residual : Ty) : I72.Model :=
  ⟨fun slot => ((if slot = a.root then record a.label (.base .int) residual
    else if slot = a.tail then residual else .base .int), Common.rowEmpty),
    fun _ => none,
    fun slot => if slot = a.root then some (openTerm a.label a.field a.tail) else none⟩

theorem model_tail_is_exact414 {s q} (a : OpenInput s q) (residual : Ty) :
    ((modelWithTail414 a residual).assignment a.tail).1 = residual := by
  simp [modelWithTail414,Ne.symm a.rootTail]

/-- A concrete family of same-State models, not a semantic value consulted
by the checker. This is for the single retained literal origin slice. -/
theorem any_model_tail_fits_original_input414 {s q} (a : OpenInput s q)
    (onlyOriginal : s.core.origins = [a.origin]) (residual : Ty) :
    Fits s (modelWithTail414 a residual) := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro row noRow; rw [a.noAtoms] at noRow; cases noRow
  · intro row noRow; rw [a.noBounds] at noRow; cases noRow
  · intro row seen
    rw [a.exactRows] at seen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at seen
    rcases seen with hr|hf
    · cases hr
      change CommonNominalFullCarrier.Equivalent ((modelWithTail414 a residual).assignment a.root).1
        (record a.label ((modelWithTail414 a residual).assignment a.field).1
          ((modelWithTail414 a residual).assignment a.tail).1)
      simp [modelWithTail414,Ne.symm a.rootField,a.fieldTail,Ne.symm a.rootTail]
      exact ⟨subtype_refl _,subtype_refl _⟩
    · cases hf
      change CommonNominalFullCarrier.Equivalent ((modelWithTail414 a residual).assignment a.field).1 (.base .int)
      simp [modelWithTail414,Ne.symm a.rootField,a.fieldTail]
      exact ⟨subtype_refl _,subtype_refl _⟩
  · intro row noRow; rw [a.noNative] at noRow; cases noRow
  · intro o witnessed
    rw [onlyOriginal] at witnessed
    cases List.mem_singleton.mp witnessed
    simp [modelWithTail414,a.originSlot,a.literal]

/-- An unresolved source tail can range over different concrete record
models while the *same* actual checked result remains pending. No
choice of model determines which candidate the checker may inspect. -/
theorem one_checked_state_has_two_tail_models414 (p : Problem) (w : OpenWire)
    (yes : check p pendingReport (.openTail w) = true)
    (read : ∀ v : OpenVerified p, replayOpen414 p w = some v →
      p.state.core.origins = [v.pending.input.origin])
    (fresh : Nat) :
    ∃ a : OpenInput p.state p.root, ∃ m n : I72.Model,
      Fits p.state m ∧ Fits p.state n ∧
      (m.assignment a.tail).1 = .emptyRecord ∧
      (n.assignment a.tail).1 = record fresh (.base .int) .emptyRecord ∧
      (m.assignment a.tail).1 ≠ (n.assignment a.tail).1 ∧
      ReportEvidence p.state m p.root pendingReport ∧ ReportEvidence p.state n p.root pendingReport := by
  obtain ⟨v,seen,_⟩ := checked_open_tail_reflects_original414 p pendingReport w yes
  let a := v.pending.input
  let m := modelWithTail414 a .emptyRecord
  let n := modelWithTail414 a (record fresh (.base .int) .emptyRecord)
  have mFits := any_model_tail_fits_original_input414 a (read v seen) .emptyRecord
  have nFits := any_model_tail_fits_original_input414 a (read v seen) (record fresh (.base .int) .emptyRecord)
  have mSlot := model_tail_is_exact414 a .emptyRecord
  have nSlot := model_tail_is_exact414 a (record fresh (.base .int) .emptyRecord)
  refine ⟨a,m,n,mFits,nFits,mSlot,nSlot,?_,(check_sound p _ _ yes).2 m mFits,(check_sound p _ _ yes).2 n nFits⟩
  change ((modelWithTail414 a .emptyRecord).assignment a.tail).1 ≠
    ((modelWithTail414 a (record fresh (.base .int) .emptyRecord)).assignment a.tail).1
  rw [mSlot,nSlot]
  intro h
  cases h

end Yulang.GeneralDeclarativeI65.I72.OpenTail414
