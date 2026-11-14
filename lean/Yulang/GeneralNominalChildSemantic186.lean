import Yulang.GeneralNominalChildCoherence184
import Yulang.GeneralNominalHeadCoreCoverage185

/-! Semantic child-center coherence. The binder hypothesis concerns only names
actually used by the child, and will be supplied by actual head readback. -/
namespace Yulang.GeneralNominalChildSemantic186
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalOriginTerms
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls}

theorem child_centers (first last : Plan roles)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (invocation : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration = last.packet.declaration)
    (clause : Clause) (member : clause ∈ first.packet.declaration.requirements)
    (signature : clause.Signature roles) (model : Assignment)
    (binders : ∀ name ∈ first.packet.declaration.inputNames,
      Same model (.source (first.binder name)) (.source (last.binder name)))
    (index : Fin (roles clause.role).arity) :
    Same model (.source ((first.childSite clause signature).center index))
      (.source ((last.childSite clause signature).center index)) := by
  let pattern := clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)
  change Same model (.source (first.emittedCenter clause.id index.val pattern))
    (.source (last.emittedCenter clause.id index.val pattern))
  cases normalized : GeneralDeclarationPatterns.normalize pattern with
  | var name =>
    have patternMember : pattern ∈ clause.arguments := List.getElem_mem ..
    have normalMember : GeneralDeclarationPatterns.normalize pattern ∈
        GeneralDeclarationPatterns.normalizeArgs clause.arguments := by
      rw [GeneralNominalChildAssembly.normalize_map]
      exact List.mem_map.mpr ⟨pattern,patternMember,rfl⟩
    have used := GeneralNominalCanonicalTemplates.argument_variables _ _ normalMember
      (show name ∈ (GeneralDeclarationPatterns.normalize pattern).variables by
        simp [normalized, GeneralDeclarationPatterns.Pattern.variables])
    simpa only [Plan.emittedCenter,normalized] using
      binders name (first.packet.checked.scope.1 clause member name used)
  | _ =>
    simp only [Plan.emittedCenter,normalized]
    rw [seed,invocation,declaration]
    exact source_self model _

 theorem child_centers_list (first last : Plan roles)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (invocation : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration = last.packet.declaration)
    (clause : Clause) (member : clause ∈ first.packet.declaration.requirements)
    (signature : clause.Signature roles) (model : Assignment)
    (binders : ∀ name ∈ first.packet.declaration.inputNames,
      Same model (.source (first.binder name)) (.source (last.binder name))) :
    ∀ index : Nat, Same model
      (.source (((List.ofFn (first.childSite clause signature).center)[index]?).getD 0))
      (.source (((List.ofFn (last.childSite clause signature).center)[index]?).getD 0)) := by
  intro index
  change Same model
    (.source (((List.ofFn (fun i : Fin (roles clause.role).arity => (first.childSite clause signature).center i))[index]?).getD 0))
    (.source (((List.ofFn (fun i : Fin (roles clause.role).arity => (last.childSite clause signature).center i))[index]?).getD 0))
  by_cases bounded : index < (roles clause.role).arity
  · simpa only [List.getElem?_ofFn, dite_eq_left bounded, Option.getD_some] using
      child_centers first last seed invocation declaration clause member signature model binders ⟨index,bounded⟩
  · simp only [List.getElem?_ofFn, dite_eq_right bounded, Option.getD_none]
    exact source_self model 0

end Yulang.GeneralNominalChildSemantic186
