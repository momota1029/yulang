import Yulang.GeneralNominalAllHeadReadback253
import Yulang.GeneralNominalRequestCanonical

set_option backward.isDefEq.respectTransparency false

/-! Individual query names inherit finite source projections. A variable-list
leaf gives each name the same bound; it does not sum duplicate captures. -/
namespace Yulang.GeneralNominalQueryReadback254
open GeneralDeclarationPatterns GeneralNominalCenters
open GeneralNominalInspection (Query)
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalFiniteMeaning
open GeneralNominalReadbackFunctionality GeneralNominalCompoundReadback GeneralNominalMaterialization
open GeneralNominalCenteredHeadMatPatternSemantics
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalCenteredHeadMatHeadShape GeneralNominalCenteredHeadMatHeadParts
open GeneralNominalCenteredHeadMatSchemaMass hiding schema_restrict schema_mass
open GeneralNominalVersionedHeadMass237
open CommonNominalFullCarrier
variable {model : GeneralNominalCommonBridge.Assignment}

def Shaped : Query → Prop
 | .variables _ | .scalar _ => True
 | .deferred _ => False
 | .node shape children => shape.Canonical ∧ children.length = shape.arity ∧ ∀ child ∈ children, Shaped child
 | .nominal _ children => ∀ child ∈ children, Shaped child

theorem member_sum (items : List Nat) (n : Nat) (member : n ∈ items) : n ≤ items.sum := by
 induction items with
 | nil => cases member
 | cons first rest ih =>
   rcases List.mem_cons.mp member with rfl | member
   · simp only [List.sum_cons]; omega
   · have smaller := ih member
     simp only [List.sum_cons]; omega

theorem projection
 (complete : CompleteLabel pattern)
 (known : At model .actual origin (eval (algebra constructors interpretation) (fun _ => .bottom) pattern))
 (canonical : TestCanonical test) (head : Head model origin test)
 (index : Fin (arity test)) :
 ∃ part, CompleteLabel part ∧
 At model .actual (project origin test index) (eval (algebra constructors interpretation) (fun _ => .bottom) part) ∧
 part.encode.size ≤ pattern.encode.size := by
 obtain ⟨actual,seen⟩ := known.1
 obtain ⟨pieces,length,parts,equal,bound⟩ := inversion complete canonical
   (holds_congr (known.2 actual seen) (head.2 actual seen))
 let part := pieces[index.val]'(by rw [length]; exact index.isLt)
 have built : At model .actual origin
   (build test (fun i => eval (algebra constructors interpretation) (fun _ => .bottom)
     (pieces[i.val]'(by rw [length]; exact i.isLt)))) := by
   have ready := at_congr known equal
   rw [realize_build (by simpa only [List.length_map] using length)] at ready
   simpa only [List.getElem_map] using ready
 refine ⟨part,parts _ (List.getElem_mem ..),project_value test canonical _ built index,?_⟩
 have member : part.encode.size ∈ pieces.map (fun p => p.encode.size) :=
   List.mem_map.mpr ⟨part,List.getElem_mem ..,rfl⟩
 have below := member_sum _ _ member
 change part.encode.size ≤ (pieces.map fun p => p.encode.size).sum at below
 change cost test + (pieces.map fun p => p.encode.size).sum ≤ pattern.encode.size at bound
 omega

theorem many_names (queries : List Query) :
 GeneralNominalCaptureNames.manyNames queries = queries.flatMap GeneralNominalCaptureNames.names := by
 induction queries <;> simp_all [GeneralNominalCaptureNames.manyNames]

theorem query_part (query : Query) (shaped : Shaped query)
 (complete : CompleteLabel pattern)
 (known : At model .actual origin (eval (algebra constructors interpretation) (fun _ => .bottom) pattern))
 (valid : GeneralNominalVersionedPlans231.SchemaHolds plan (schema query origin .actual) model)
 (name : Nat) (member : name ∈ GeneralNominalCaptureNames.names query) :
 ∃ part, Part (algebra constructors interpretation) plan model name part ∧ part.encode.size ≤ pattern.encode.size := by
 cases query with
 | variables names =>
   have same := valid.2 ⟨name,origin,.actual⟩ (by simpa only [schema,GeneralNominalCaptureNames.names] using List.mem_map.mpr ⟨name,member,rfl⟩)
   simp only [ite_true,GeneralNominalVersionedFrame231.binder_eq] at same
   obtain ⟨actual,seen⟩ := known.1
   exact ⟨pattern,⟨complete,eqv_trans (eqv_symm (same.2.2 _ _ seen (.source _))) (known.2 actual seen)⟩,Nat.le_refl _⟩
 | deferred => simp only [Shaped] at shaped
 | scalar => cases member
 | node shape children =>
   simp only [Shaped] at shaped
   rw [GeneralNominalCaptureNames.names,many_names] at member
   obtain ⟨child,present,used⟩ := List.mem_flatMap.mp member
   obtain ⟨index,inside,found⟩ := List.mem_iff_getElem.mp present
   have bounded : index < shape.arity := by rw [← shaped.2.1]; exact inside
   obtain ⟨part,closed,represented,small⟩ := projection complete known (test := .structural shape) shaped.1
     (valid.1 (origin,.structural shape) (by simp only [schema]; exact List.mem_cons_self ..)) ⟨index,bounded⟩
   have included := schemas_component children (fun i => Origin.structural origin shape i)
     .actual 0 index (query := child) (by rw [List.getElem?_eq_getElem inside,found])
   have childValid : GeneralNominalVersionedPlans231.SchemaHolds plan
     (schema child (.structural origin shape index) .actual) model := by
     apply schema_restrict valid
     simp only [Included,Nat.zero_add] at included
     simp only [Included,schema]
     exact ⟨fun t h => List.mem_cons_of_mem _ (included.1 h),included.2⟩
   obtain ⟨label,labelPart,labelSmall⟩ := query_part child (shaped.2.2 child present) closed represented childValid name used
   exact ⟨label,labelPart,Nat.le_trans labelSmall small⟩
 | nominal key children =>
   simp only [Shaped] at shaped
   rw [GeneralNominalCaptureNames.names,many_names] at member
   obtain ⟨child,present,used⟩ := List.mem_flatMap.mp member
   obtain ⟨index,inside,found⟩ := List.mem_iff_getElem.mp present
   obtain ⟨part,closed,represented,small⟩ := projection complete known (test := .nominal key children.length) trivial
     (valid.1 (origin,.nominal key children.length) (by simp only [schema]; exact List.mem_cons_self ..)) ⟨index,inside⟩
   have included := schemas_component children (fun i => Origin.nominal origin key i)
     .actual 0 index (query := child) (by rw [List.getElem?_eq_getElem inside,found])
   have childValid : GeneralNominalVersionedPlans231.SchemaHolds plan
     (schema child (.nominal origin key index) .actual) model := by
     apply schema_restrict valid
     simp only [Included,Nat.zero_add] at included
     simp only [Included,schema]
     exact ⟨fun t h => List.mem_cons_of_mem _ (included.1 h),included.2⟩
   obtain ⟨label,labelPart,labelSmall⟩ := query_part child (shaped child present) closed represented childValid name used
   exact ⟨label,labelPart,Nat.le_trans labelSmall small⟩
 termination_by sizeOf query
 decreasing_by all_goals have bound := List.sizeOf_lt_of_mem present; simp_all; omega

theorem translated_arity (pattern : Pattern)
 (translated : GeneralNominalInspection.translate constructors interpretation pattern = .node shape children) :
 children.length = shape.arity := by
 cases pattern with
 | var | join => simp only [GeneralNominalInspection.translate] at translated; cases translated
 | variant tag payload =>
   simp only [GeneralNominalInspection.translate] at translated
   split at translated <;> cases translated <;> rfl
 | record label payload tail =>
   simp only [GeneralNominalInspection.translate] at translated
   split at translated
   · cases translated; simp only [List.length_map,GeneralNormalizedObservation.Shape.arity]
   · cases translated
 | app key arguments =>
   rw [GeneralNominalInspection.translate.eq_def] at translated
   dsimp only at translated
   split at translated
   · cases translated
   · cases translated; rfl
   · cases translated; rfl
   · cases translated; rfl
   · split at translated
     · split at translated <;> cases translated
     · cases translated

theorem shaped_of_source (query : Query) (pattern : Pattern)
 (translated : GeneralNominalInspection.translate constructors interpretation pattern = query)
 (complete : GeneralNominalHeadMatchMass.Complete query)
 (canonical : ∀ test ∈ GeneralNominalSchemaVocabulary.vocabulary query, TestCanonical test) :
 Shaped query := by
 cases query with
 | variables | scalar => simp only [Shaped]
 | deferred => simp only [GeneralNominalHeadMatchMass.Complete] at complete
 | node shape children =>
   simp only [Shaped]
   simp only [GeneralNominalHeadMatchMass.Complete] at complete
   refine ⟨canonical _ (List.mem_cons_self ..),translated_arity pattern translated,?_⟩
   intro child present
   cases child with
   | variables => simp only [Shaped]
   | scalar => simp only [Shaped]
   | deferred p => have bad := complete _ present; simp only [GeneralNominalHeadMatchMass.Complete] at bad
   | node childShape grandchildren =>
     obtain ⟨part,_,source⟩ := GeneralNominalSourcePatternParts.child_source pattern
       (by rw [translated]; exact present) (by intro names same; cases same)
     apply shaped_of_source _ part source (complete _ present)
     intro test member
     apply canonical
     apply List.mem_cons_of_mem
     rw [GeneralNominalRequestTemplates.vocabularies_flatMap]
     exact List.mem_flatMap.mpr ⟨_,present,member⟩
   | nominal key grandchildren =>
     obtain ⟨part,_,source⟩ := GeneralNominalSourcePatternParts.child_source pattern
       (by rw [translated]; exact present) (by intro names same; cases same)
     apply shaped_of_source _ part source (complete _ present)
     intro test member
     apply canonical
     apply List.mem_cons_of_mem
     rw [GeneralNominalRequestTemplates.vocabularies_flatMap]
     exact List.mem_flatMap.mpr ⟨_,present,member⟩
 | nominal key children =>
   simp only [Shaped]
   simp only [GeneralNominalHeadMatchMass.Complete] at complete
   intro child present
   cases child with
   | variables => simp only [Shaped]
   | scalar => simp only [Shaped]
   | deferred p => have bad := complete _ present; simp only [GeneralNominalHeadMatchMass.Complete] at bad
   | node childShape grandchildren =>
     obtain ⟨part,_,source⟩ := GeneralNominalSourcePatternParts.child_source pattern
       (by rw [translated]; exact present) (by intro names same; cases same)
     apply shaped_of_source _ part source (complete _ present)
     intro test member
     apply canonical
     apply List.mem_cons_of_mem
     rw [GeneralNominalRequestTemplates.vocabularies_flatMap]
     exact List.mem_flatMap.mpr ⟨_,present,member⟩
   | nominal key grandchildren =>
     obtain ⟨part,_,source⟩ := GeneralNominalSourcePatternParts.child_source pattern
       (by rw [translated]; exact present) (by intro names same; cases same)
     apply shaped_of_source _ part source (complete _ present)
     intro test member
     apply canonical
     apply List.mem_cons_of_mem
     rw [GeneralNominalRequestTemplates.vocabularies_flatMap]
     exact List.mem_flatMap.mpr ⟨_,present,member⟩
 termination_by sizeOf query
 decreasing_by all_goals have bound := List.sizeOf_lt_of_mem present; simp_all; omega

theorem translated_shaped (pattern : Pattern)
 (tidy : GeneralNominalRequestCanonical.Tidy pattern)
 (complete : GeneralNominalHeadMatchMass.Complete (GeneralNominalInspection.translate constructors interpretation pattern)) :
 Shaped (GeneralNominalInspection.translate constructors interpretation pattern) :=
 shaped_of_source _ pattern rfl complete (GeneralNominalRequestCanonical.translated_canonical pattern tidy)

end Yulang.GeneralNominalQueryReadback254

