import Yulang.GeneralDeclarativePlacementEquiv327
import Yulang.GeneralDeclarativeDemandAliases322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativePlacementEvidence327
open GeneralDeclarativePlacementEquiv327 (SpanSame RequestSame)
open GeneralDeclarativeDemandAliases322 (Arg Name Same head_transport evidence_transport)
open GeneralDeclarativeAssembly320 (ChildDenotes Meaning Node)
open GeneralDeclarativeNormalized320 (NormalMeaning)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans eqv_symm)
open CommonRoleOutermostResolver (All₂)

theorem exact_alias {m : Assignment} (same : RequestSame m a b) : Same m a b := by
  refine ⟨same.1,?_,?_⟩
  · exact GeneralDeclarativeNormalized320.ordered_map same.2.1 (fun _ _ _ _ span => ⟨span.1,span.2.1,span.2.2⟩)
  · rw [same.2.2]
    generalize b.outputs = outputs
    induction outputs with
    | nil => exact .nil
    | cons first rest ih => exact .cons ⟨rfl,eqv_refl _⟩ ih

theorem normal_arg {m : Assignment} (same : SpanSame m a b) (seen : NormalMeaning c i cap m a pat) :
    NormalMeaning c i cap m b pat := by
  obtain ⟨exp,rule,lo,hi,head⟩ := seen
  exact ⟨exp,rule,eqv_trans (eqv_symm same.1) lo,eqv_trans (eqv_symm same.2.2) hi,
    head_transport ⟨same.1,same.2.1,same.2.2⟩ head⟩

theorem normal_arguments {m : Assignment}
    (same : All₂ (SpanSame m) as bs)
    (seen : All₂ (NormalMeaning c i cap m) as pats) :
    All₂ (NormalMeaning c i cap m) bs pats := by
  induction same generalizing pats with
  | nil => cases seen; exact .nil
  | cons first _ ih =>
    cases seen with
    | cons firstRead rest => exact .cons (normal_arg first firstRead) (ih rest)

theorem same_child {m : Assignment}
    (same : RequestSame m a b) (read : ChildDenotes c i cap m cl a) : ChildDenotes c i cap m cl b := by
  refine ⟨same.1.symm.trans read.role,normal_arguments same.2.1 read.arguments,?_⟩
  rw [← same.2.2]
  exact read.outputs

theorem child_sequence {m : Assignment}
    (same : All₂ (RequestSame m) old new)
    (read : All₂ (ChildDenotes c i cap m) clauses old) :
    All₂ (ChildDenotes c i cap m) clauses new := by
  induction same generalizing clauses with
  | nil => cases read; exact .nil
  | cons one _ ih =>
    cases read with
    | cons found rest => exact .cons (same_child one found) (ih rest)

theorem meaning {m : Assignment}
    (same : All₂ (RequestSame m) old new)
    (read : Meaning r i m d decl cap old) : Meaning r i m d decl cap new :=
  ⟨read.visible,read.role,read.captures,read.head,child_sequence same read.children,read.outputs⟩

theorem children_evidence {m : Assignment}
    (same : All₂ (RequestSame m) old new)
    (good : All₂ (Evidence r i m) old dicts) : All₂ (Evidence r i m) new dicts := by
  induction same generalizing dicts with
  | nil => cases good; exact .nil
  | cons first _ ih =>
    cases good with
    | cons sound tail => exact .cons (evidence_transport (exact_alias first) sound) (ih tail)

/-- For the same root, same-model evidence may be rebuilt with
different names for each observed ordered child call. This is not
transport of candidate authority, recurrence checks, or Classify. -/
theorem retarget {m : Assignment} (same : All₂ (RequestSame m) old new)
    (root : Node r i m d key old) (kids : All₂ (Evidence r i m) old dicts) :
    Node r i m d key new ∧ All₂ (Evidence r i m) new dicts := by
  obtain ⟨decl,cap,found,read⟩ := root
  exact ⟨⟨decl,cap,found,meaning same read⟩,children_evidence same kids⟩

end Yulang.GeneralDeclarativePlacementEvidence327
