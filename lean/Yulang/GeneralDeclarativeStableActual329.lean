import Yulang.GeneralDeclarativeDemandAliases322
import Yulang.GeneralDeclarativeStableTies329

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStableActual329
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeWhere319 (Capture InInterval)
open GeneralDeclarativeDemand320 (Demand HeadMeaning Bounds bounds_sound sourceValue)
open GeneralDeclarativeDemandAliases322 (Name lookup_prior)
open GeneralDeclarativeOutputs320 (bodyCapture bodyPattern)
open GeneralDeclarativeAssembly320 (Node Meaning)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeHead320 (State Models)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_symm eqv_trans)
open CommonRoleOutermostResolver (All₂)

def InRange (m : Assignment) (a : Capture) : Prop :=
  InInterval (m a.lower).1 (m a.upper).1 (m a.center).1

def Now (m : Assignment) (a b : Capture) : Prop :=
  Equivalent (m a.center).1 (m b.center).1

structure SameActual (m : Assignment) (a b : Demand) : Prop where
  role : a.role = b.role
  args : All₂ (Now m) a.arguments b.arguments
  outputs : All₂ (Name m) a.outputs b.outputs

theorem by_name {m : Assignment} {a b : Capture} (same : a.center = b.center) :
    Now m a b := by unfold Now; rw [same]; exact eqv_refl _

theorem by_selected_tie {s : State}
    (closed : GeneralDeclarativeStableTies329.Consequence s selected uses)
    (found : (binder,a.center) ∈ uses) (m) (fit : Models s m) : Now m a (selected binder) :=
  GeneralDeclarativeStableTies329.from_use closed found m fit

theorem head {m : Assignment} {a b : Capture} (same : Now m a b) (new : InRange m b)
    (previous : HeadMeaning c interp capture m a p) : HeadMeaning c interp capture m b p :=
  ⟨eqv_trans (eqv_symm same) previous.1,new⟩

theorem heads {m : Assignment}
    (same : All₂ (Now m) as bs) (new : ∀ b ∈ bs, InRange m b)
    (previous : All₂ (HeadMeaning c interp capture m) as ps) :
    All₂ (HeadMeaning c interp capture m) bs ps := by
  induction same generalizing ps with
  | nil => cases previous; exact .nil
  | cons this _ ih =>
    cases previous with
    | cons old rest =>
      exact .cons (head this (new _ List.mem_cons_self) old)
        (ih (fun b seen => new b (List.mem_cons_of_mem _ seen)) rest)

theorem indexed {m : Assignment} (same : All₂ (Now m) as bs) (i : Nat) :
    Equivalent (m ((as[i]?.map Capture.center).getD 0)).1
      (m ((bs[i]?.map Capture.center).getD 0)).1 := by
  induction same generalizing i with
  | nil => exact eqv_refl _
  | cons this _ ih =>
    cases i with
    | zero => exact this
    | succ j => exact ih j

theorem rhs {m : Assignment} {a b : Demand} (same : All₂ (Now m) a.arguments b.arguments)
    (body : GeneralDictionaryAssociatedProvenance.Body) :
    Equivalent (sourceValue c interp (bodyCapture a capture body) m (bodyPattern body))
      (sourceValue c interp (bodyCapture b capture body) m (bodyPattern body)) := by
  cases body with
  | explicit => exact eqv_refl _
  | default =>
    apply GeneralNominalCenteredHeadMatSemanticSubstitution.eval_congr
    intro key _
    exact indexed same key

/-- For same-model typing, two demand arguments need not have equal
endpoints. It is the actual name/value that is shared, and the new
span must independently be bounded. The where children keep their
order, while defaults and fixed outputs use the actual inputs. No
transport of candidate probing or Classify is implied. -/
theorem retarget {m : Assignment} {a b : Demand}
    (same : SameActual m a b) (new : ∀ bArg ∈ b.arguments, InRange m bArg)
    (stays : Node r interp m a key children) : Node r interp m b key children := by
  obtain ⟨impl,captures,id,typing⟩ := stays
  refine ⟨impl,captures,id,typing.visible,typing.role.trans same.role,typing.captures,
    heads same.args new typing.head,typing.children,?_⟩
  intro out there
  obtain ⟨prior,seen,linked⟩ := lookup_prior same.outputs there
  obtain ⟨body,supplies,returns⟩ := typing.outputs prior seen
  exact ⟨body,linked.same ▸ supplies,
    eqv_trans (eqv_symm linked.value) (eqv_trans returns (rhs same.args body))⟩

theorem evidence {s : State} {a b : Demand}
    (m) (fits : Models s m) (same : SameActual m a b)
    (new : ∀ bArg ∈ b.arguments, Bounds s bArg)
    (checked : Evidence r interp m a dict) : Evidence r interp m b dict := by
  cases checked with
  | node proof kids => exact .node (retarget same (fun n h => bounds_sound (new n h) m fits) proof) kids

end Yulang.GeneralDeclarativeStableActual329
