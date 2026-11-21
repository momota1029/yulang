import Yulang.GeneralDeclarativeFrameReadback325
import Yulang.GeneralDeclarativeDefaultScope320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativePlacementEquiv327
open GeneralDeclarations (Declaration Clause)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeFrameReadback325 (ClauseFrame sourceNames placeById)
open GeneralDeclarativeClauseOrigins325 (Origin origin_reads normalized_order)
open GeneralDeclarativeEqualities322 (semantic)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeSourceEmission322 (Names useArg inputs demand)
open GeneralDeclarativeEmissionOperands322 (Compound)
open GeneralDeclarativeDefaultScope320 (ordered_length)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_symm eqv_trans)
open CommonNominalFullCarrier (Equivalent)
open CommonRoleOutermostResolver (All₂)

def SpanSame (m : Assignment) (a b : Capture) : Prop :=
  Equivalent (m a.lower).1 (m b.lower).1 ∧
  Equivalent (m a.center).1 (m b.center).1 ∧ Equivalent (m a.upper).1 (m b.upper).1

def RequestSame (m : Assignment) (a b : Demand) : Prop :=
  a.role = b.role ∧ All₂ (SpanSame m) a.arguments b.arguments ∧ a.outputs = b.outputs

theorem span_refl (m : Assignment) (a : Capture) : SpanSame m a a :=
  ⟨eqv_refl _,eqv_refl _,eqv_refl _⟩

theorem same_origin {s : State} (a : Origin s n e) (b : Origin s j e) (m) (v : Models s m) :
    Equivalent (m n).1 (m j).1 :=
  eqv_trans (semantic (origin_reads a) m v) (eqv_symm (semantic (origin_reads b) m v))

theorem inputs_related (m : Assignment) (names : Names) (left right : Nat → Capture)
    (offset : Nat) (patterns : List Pattern)
    (agrees : ∀ j p, patterns[j]? = some p →
      SpanSame m (useArg names (left (offset+j)) p) (useArg names (right (offset+j)) p)) :
    All₂ (SpanSame m) (inputs names left offset patterns) (inputs names right offset patterns) := by
  induction patterns generalizing offset with
  | nil => exact .nil
  | cons first rest ih =>
    refine .cons (agrees 0 first rfl) (ih (offset+1) ?_)
    intro j p here
    have asPosition := agrees (j+1) p (show (first::rest)[j+1]? = some p from here)
    have shift : offset + (j+1) = offset + 1 + j := by omega
    simpa only [shift] using asPosition

theorem placement_for_clause {s : State} {left right : Placement}
    (a : ClauseFrame s reg i decl cl names left) (b : ClauseFrame s reg i decl cl names right)
    (targets : left.targets cl = right.targets cl) (m) (valid : Models s m) :
    RequestSame m (demand decl cl names (left.compound cl) (left.targets cl))
      (demand decl cl names (right.compound cl) (right.targets cl)) := by
  obtain ⟨codes,printed,aRead⟩ := a.input
  obtain ⟨codes',printed',bRead⟩ := b.input
  cases Option.some.inj (printed.symm.trans printed')
  have lengths := ordered_length (normalized_order printed)
  refine ⟨rfl,inputs_related m names _ _ 0 cl.arguments ?_,by simp [demand,targets]⟩
  intro j p pos
  rw [Nat.zero_add]
  cases kind : normalize p with
  | var binder =>
    simpa [useArg,kind] using span_refl m (names.input binder)
  | app tag forms | record tag forms _ | variant tag forms | join tag forms =>
    have fallsOutside : Compound p := by
      intro n h
      rw [kind] at h
      cases h
    have inBound : j < codes.length := by
      rw [← lengths]
      exact (List.getElem?_eq_some_iff.mp pos).1
    let e := codes[j]'inBound
    have code : codes[j]? = some e := List.getElem?_eq_getElem inBound
    obtain ⟨a0,a1,a2⟩ := aRead j p e pos code fallsOutside
    obtain ⟨b0,b1,b2⟩ := bRead j p e pos code fallsOutside
    simpa [useArg,kind] using
      (show SpanSame m (left.compound cl j) (right.compound cl j) from
        ⟨same_origin a0 b0 m valid,same_origin a1 b1 m valid,same_origin a2 b2 m valid⟩)

/-- Changing only the names chosen to hold the observed compound
values leaves every ordered child argument observationally equivalent
in the same ordinary model. Relative to the same source capture and
same produces/targets, no match/rejection rule is involved. -/
theorem complete_ordered {s : State} {left right : Placement}
    (targets : left.targets = right.targets)
    (a : ∀ cl ∈ decl.requirements, ClauseFrame s reg i decl cl (sourceNames decl left base) left)
    (b : ∀ cl ∈ decl.requirements, ClauseFrame s reg i decl cl (sourceNames decl right base) right)
    (m) (valid : Models s m) :
    All₂ (RequestSame m) (children decl (sourceNames decl left base) left)
      (children decl (sourceNames decl right base) right) := by
  have shared : sourceNames decl left base = sourceNames decl right base := by
    unfold sourceNames
    congr 1
    funext c e
    unfold placeById
    rw [targets]
  rw [← shared]
  have both : ∀ cl ∈ decl.requirements, RequestSame m
      (demand decl cl (sourceNames decl left base) (left.compound cl) (left.targets cl))
      (demand decl cl (sourceNames decl left base) (right.compound cl) (right.targets cl)) := by
    intro cl provided
    exact placement_for_clause (a cl provided) (shared ▸ b cl provided) (congrFun targets cl) m valid
  unfold children
  have walk (ls : List Clause) (given : ∀ cl ∈ ls, cl ∈ decl.requirements) :
      All₂ (RequestSame m)
        (ls.map (fun cl => demand decl cl (sourceNames decl left base) (left.compound cl) (left.targets cl)))
        (ls.map (fun cl => demand decl cl (sourceNames decl left base) (right.compound cl) (right.targets cl))) := by
    induction ls with
    | nil => exact .nil
    | cons c more ih =>
      exact .cons (both c (given c List.mem_cons_self)) (ih (fun cl here => given cl (List.mem_cons_of_mem _ here)))
  exact walk _ (fun _ h => h)

end Yulang.GeneralDeclarativePlacementEquiv327
