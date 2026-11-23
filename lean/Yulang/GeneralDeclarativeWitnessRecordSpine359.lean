import Yulang.GeneralDeclarativeWitnessExactEndpointResidual358

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessRecordSpine359
open CommonNominalFullCarrier (Ty Equivalent exactEmpty emptyRecord)
open GeneralDeclarativeHead320 (Equation State Models)
open GeneralDeclarativeWitnessAuthoredProjection358 (Source)
open GeneralDeclarativeWitnessSharedTailProjection358 (field)
open GeneralDeclarativeExactDeleteRigid337 (Fields Terminal literal)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans record_congr)
open GeneralNominalCommonBridge (Assignment)

inductive EndKind where
  | exact | width

def EndKind.ty : EndKind → Ty
  | .exact => exactEmpty
  | .width => emptyRecord

def EndKind.row (k : EndKind) (name : Nat) : Equation :=
  ⟨name,.primitive (match k with | .exact => .exactEmpty | .width => .emptyRecord) []⟩

theorem EndKind.terminal (kind : EndKind) : Terminal kind.ty := by
  cases kind <;> constructor

/-- Names are logical coordinates in literal author equations, not physical
addresses or representatives chosen after observing the solver. -/
inductive Spine where
  | terminal (kind : EndKind)
  | cons (label payload rest : Nat) (tail : Spine)

def Spine.rows (root : Nat) : Spine → List Equation
  | .terminal k => [k.row root]
  | .cons label payload rest tail => field root label payload rest :: tail.rows rest

def Spine.fields (m : Assignment) : Spine → Fields
  | .terminal _ => []
  | .cons label payload _ rest => (label,(m payload).1) :: rest.fields m

def Spine.kind : Spine → EndKind
  | .terminal t => t
  | .cons _ _ _ tail => tail.kind

def Spine.denote (m : Assignment) (spine : Spine) : Ty :=
  literal (spine.fields m) spine.kind.ty

structure Read (source : Source) (s : State) (name : Nat) (spine : Spine) : Prop where
  authored : ∀ row ∈ spine.rows name,row ∈ source.authored
  current : ∀ row ∈ spine.rows name,row ∈ s.equations

def check (source : Source) (s : State) (name : Nat) (spine : Spine) : Bool :=
  (spine.rows name).all (fun r => decide (r ∈ source.authored)) &&
  (spine.rows name).all (fun r => decide (r ∈ s.equations))

theorem check_exact {source s name spine} :
    check source s name spine = true ↔ Read source s name spine := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.authored,h.current⟩⟩

theorem read_in_model {source s name spine} (read : Read source s name spine)
    (m : Assignment) (fit : Models s m) : Equivalent (m name).1 (spine.denote m) := by
  induction spine generalizing name with
  | terminal kind =>
    have found := fit.2 (kind.row name) (read.current _ (by simp [Spine.rows]))
    cases kind <;> exact found
  | cons label payload rest tail ih =>
    have here := fit.2 (field name label payload rest) (read.current _ (by simp [Spine.rows]))
    have there : Read source s rest tail :=
      ⟨fun r h => read.authored r (List.mem_cons_of_mem _ h),
       fun r h => read.current r (List.mem_cons_of_mem _ h)⟩
    exact eqv_trans here (record_congr label (eqv_refl _) (ih there))

end Yulang.GeneralDeclarativeWitnessRecordSpine359
