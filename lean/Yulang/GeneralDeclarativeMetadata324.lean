import Yulang.GeneralDeclarativeNFHead324
import Yulang.GeneralDeclarativeEndpointProbe321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeMetadata324
open GeneralDeclarationPatterns (Constructors Pattern normalize)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadMatExpressions (Expr application translate translateMany)
open GeneralDeclarativeEndpointProbe321 (Matches)
open GeneralDeclarativeNFHead324 (fact)
open GeneralDeclarativeDemand320 (sourceValue)
open GeneralDeclarativeWhere319 (variables)
open GeneralNominalCenteredHeadMatCompilerSemantics (translate_value)

mutual
 def keys : Pattern → List Nat
  | .var _ => []
  | .app n ps => n :: keysMany ps
  | .record _ payload tail => keys payload ++ keys tail
  | .variant _ payload => keys payload
  | .join a b => keys a ++ keys b
 def keysMany : List Pattern → List Nat
  | [] => []
  | p::ps => keys p ++ keysMany ps
end

def Same (c c' : Constructors) (i i' : Interpretation) (names : List Nat) : Prop :=
  ∀ k ∈ names, c k = c' k ∧ i.primitives k = i'.primitives k ∧
    i.invariantNominal k = i'.invariantNominal k

theorem app_same {c c' : Constructors} {i i' : Interpretation} (known : Same c c' i i' [k]) :
    application c i k xs = application c' i' k xs := by
  have ⟨n,p,flag⟩ := known k List.mem_cons_self
  simp [application,n,p,flag]

mutual
 theorem translation (p : Pattern) (known : Same c c' i i' (keys p)) :
    translate c i p = translate c' i' p := by
  cases p with
  | var => rfl
  | app k ps =>
    have inside := many ps (fun n used => known n (List.mem_cons_of_mem _ used))
    have locally : Same c c' i i' [k] := fun n used => known n (by
      cases List.mem_singleton.mp used
      exact List.mem_cons_self)
    simp only [translate,inside,app_same locally]
  | record k a b =>
    simp only [translate,translation a (fun n used => known n (List.mem_append_left _ used)),
      translation b (fun n used => known n (List.mem_append_right _ used))]
  | variant k payload =>
    simp only [translate,translation payload known]
  | join a b =>
    simp only [translate,translation a (fun n used => known n (List.mem_append_left _ used)),
      translation b (fun n used => known n (List.mem_append_right _ used))]
 termination_by sizeOf p
 theorem many (ps : List Pattern) (known : Same c c' i i' (keysMany ps)) :
    translateMany c i ps = translateMany c' i' ps := by
  cases ps with
  | nil => rfl
  | cons p rest =>
    simp only [translateMany,translation p (fun n used => known n (List.mem_append_left _ used)),
      many rest (fun n used => known n (List.mem_append_right _ used))]
 termination_by sizeOf ps
end

/-- Information not consulted after source normalization, including a
removed record field, is not a requirement of the normalized compiler. -/
theorem normalized_fact {p : Pattern} (known : Same c c' i i' (keys (normalize p))) :
    fact c i cap arg p = fact c' i' cap arg p := by
  simp only [fact,translation (normalize p) known]

theorem normalized_probe {p : Pattern} (known : Same c c' i i' (keys (normalize p))) :
    Matches s c i arg p ↔ Matches s c' i' arg p := by
  unfold Matches
  rw [translation (normalize p) known]

theorem normal_meaning {p : Pattern} (known : Same c c' i i' (keys (normalize p)))
    (printed : translate c i (normalize p) = some code) :
    sourceValue c i cap m p = sourceValue c' i' cap m p := by
  have other : translate c' i' (normalize p) = some code := (translation (normalize p) known).symm.trans printed
  exact (translate_value (normalize p) (variables := variables cap m) printed).symm.trans
    (translate_value (normalize p) (variables := variables cap m) other)

end Yulang.GeneralDeclarativeMetadata324
