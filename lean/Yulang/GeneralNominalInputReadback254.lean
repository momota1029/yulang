import Yulang.GeneralNominalQueryReadback254

/-! Finite individual input captures for actual completed head inspections,
including leaf declarations with multi-name query leaves. Joint head size is
not bounded here: duplicated names can describe one source projection. -/
namespace Yulang.GeneralNominalInputReadback254
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatPatternSemantics
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalCenteredHeadMatHeadParts
open GeneralNominalCenteredHeadMatSchemaMass hiding schema_restrict schema_mass
open GeneralNominalCenteredHeadMatSemanticLabels (Inputs Captures images)
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalFiniteMeaning
open GeneralNominalReadbackFunctionality GeneralNominalCompoundReadback GeneralNominalMaterialization
open GeneralNominalVersionedHeadMass237
open GeneralNominalQueryReadback254
open GeneralNominalPatersonLineage (mass)
variable {roles : Roles.RoleDecls} {plan : Plan roles} {labels : List Pattern}

theorem variable_member (patterns : List Pattern) (name : Nat)
 (used : name ∈ variablesArgs patterns) :
 ∃ pattern ∈ patterns, name ∈ pattern.variables := by
 induction patterns with
 | nil => cases used
 | cons first rest ih =>
   rcases List.mem_append.mp used with one | tail
   · exact ⟨first,List.mem_cons_self ..,one⟩
   · obtain ⟨pattern,member,used⟩ := ih tail
     exact ⟨pattern,List.mem_cons_of_mem _ member,used⟩

/-- No nonempty-where or coveredHead hypothesis. The finite normal labels and
the actual Frame/Holds premises are retained; the witness is model-relative. -/
theorem input_part
 (frame : GeneralNominalVersionedEvidence231.Frame registry state focus key plan)
 (branch : GeneralNominalVersionedPlans231.Holds plan model)
 (known : Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model plan.input labels)
 (name : Nat) (input : name ∈ plan.packet.declaration.inputNames) :
 ∃ pattern, Part (algebra plan.packet.registry.constructors plan.packet.context.interpretation) plan model name pattern ∧
 pattern.encode.size ≤ mass labels := by
 obtain ⟨template,templateMem,used⟩ := variable_member _ name input
 obtain ⟨position,inHead,templateEq⟩ := List.mem_iff_getElem.mp templateMem
 obtain ⟨inputLength,inputMeanings⟩ := known
 have role : plan.packet.declaration.role = plan.input.occurrence.demand.role := by
   rw [plan.input_exact,frame.occurrence_eq]; exact frame.role_eq
 have headLength : (normalizeArgs plan.packet.declaration.head).length = (roles plan.input.occurrence.demand.role).arity := by
   simpa only [GeneralNominalChildAssembly.normalize_map,List.length_map,role] using plan.packet.checked.signature.1
 let index : Fin (roles plan.input.occurrence.demand.role).arity := ⟨position,by rw [← headLength]; exact inHead⟩
 have prepared := frame.prepared
 rw [← frame.context_eq] at prepared
 obtain ⟨_,_,bounds,_,_,finished,_⟩ := prepared
 have allComplete := GeneralNominalCompleteNames183.many_complete plan.packet.context.state _ bounds _ _ finished
 have complete : GeneralNominalHeadMatchMass.Complete
   (GeneralNominalInspection.translate plan.packet.context.state.constructors plan.packet.context.interpretation template) :=
   allComplete _ (List.mem_map.mpr ⟨template,templateMem,rfl⟩)
 have shaped := translated_shaped template
   (GeneralNominalRequestCanonical.normalized_args_tidy _ template templateMem) complete
 have named := GeneralNominalCompleteNames183.translated_names _ _ template complete name used
 have valid := branch.2.1.2.2.2.2.1
 let origin := Origin.source (plan.input.center index)
 let label := normalize (labels[position]'(by rw [inputLength]; exact index.isLt))
 have inputMeaning := inputMeanings index
 have represented : At model .actual origin
   (eval (algebra plan.packet.registry.constructors plan.packet.context.interpretation) (fun _ => .bottom) label) :=
   ⟨⟨_,.source _⟩,by intro value seen; change Observes model (.source (plan.input.center index)) value at seen; cases seen; exact inputMeaning.2.2⟩
 have included := schemas_component
   (GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation plan.packet.declaration)
   (fun i => .source ((List.ofFn plan.input.center)[i]?.getD 0)) .actual 0 position
   (query := GeneralNominalInspection.translate plan.packet.context.state.constructors plan.packet.context.interpretation template)
   (by simp only [GeneralNominalInspection.queries,Declaration.normalHead,List.getElem?_map,
     List.getElem?_eq_getElem inHead,Option.map_some,templateEq])
 have localValid : GeneralNominalVersionedPlans231.SchemaHolds plan
   (schema (GeneralNominalInspection.translate plan.packet.context.state.constructors plan.packet.context.interpretation template) origin .actual) model := by
   have restricted := schema_restrict valid included
   simpa only [Nat.zero_add,List.getElem?_ofFn,index.isLt,dite_eq_left,Option.getD_some,origin,index] using restricted
 obtain ⟨pattern,part,bound⟩ := query_part _ shaped
   ⟨inputMeaning.1,GeneralPatternCoveredResult.covered_result_normal _ inputMeaning.2.1⟩ represented localValid name named
 refine ⟨pattern,part,Nat.le_trans bound ?_⟩
 have member : label.encode.size ∈ (normalizeArgs labels).map (fun p => p.encode.size) := by
   apply List.mem_map.mpr
   refine ⟨label,?_,rfl⟩
   rw [GeneralNominalChildAssembly.normalize_map]
   exact List.mem_map.mpr ⟨_,List.getElem_mem ..,rfl⟩
 have small := member_sum _ _ member
 simpa only [label,index,mass,counted,GeneralNominalCenteredHeadMatHeadParts.encoded_size,GeneralNominalCenteredHeadMatHeadParts.size] using small


theorem readback
 (frame : GeneralNominalVersionedEvidence231.Frame registry state focus key plan)
 (branch : GeneralNominalVersionedPlans231.Holds plan model)
 (known : Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model plan.input labels) :
 ∃ capture, Captures plan model capture ∧
 (∀ name, GeneralPatternNormalForm.Normal (capture name)) ∧
 (∀ name ∈ plan.packet.declaration.inputNames,
   Part (algebra plan.packet.registry.constructors plan.packet.context.interpretation) plan model name (capture name)) ∧
 (∀ name ∈ plan.packet.declaration.inputNames, (capture name).encode.size ≤ mass labels) ∧
 (∀ name ∈ plan.packet.declaration.inputNames, GeneralPatternAdditiveDepth253.depth (capture name) ≤ mass labels) := by
 classical
 let witnesses := fun name input => input_part frame branch known name input
 let capture : Nat → Pattern := fun name => if input : name ∈ plan.packet.declaration.inputNames
   then Classical.choose (witnesses name input) else .var name
 have normals (name : Nat) : GeneralPatternNormalForm.Normal (capture name) := by
   by_cases input : name ∈ plan.packet.declaration.inputNames
   · simpa only [capture,dite_eq_left input] using (Classical.choose_spec (witnesses name input)).1.1.2
   · simp only [capture,dite_eq_right input,GeneralPatternNormalForm.Normal]
 have fixed (name : Nat) : normalize (capture name) = capture name := GeneralPatternNormalForm.fixed _ (normals name)
 have parts (name : Nat) (input : name ∈ plan.packet.declaration.inputNames) :
   Part (algebra plan.packet.registry.constructors plan.packet.context.interpretation) plan model name (capture name) := by
   simpa only [capture,dite_eq_left input] using (Classical.choose_spec (witnesses name input)).1
 have bounds (name : Nat) (input : name ∈ plan.packet.declaration.inputNames) : (capture name).encode.size ≤ mass labels := by
   simpa only [capture,dite_eq_left input] using (Classical.choose_spec (witnesses name input)).2
 refine ⟨capture,⟨?_,?_⟩,normals,parts,bounds,?_⟩
 · intro name; rw [fixed]; exact GeneralPatternNormalForm.covered_normal _ (normals name)
 · intro name needed
   have part := parts name (GeneralNominalCenteredHeadMatSemanticLabels.needed_in_head needed)
   exact ⟨by rw [fixed]; exact part.1.1,
     by rw [fixed]; exact GeneralPatternNormalForm.covered_normal _ part.1.2,
     by rw [fixed]; exact part.2⟩
 · intro name input
   exact Nat.le_trans (GeneralPatternAdditiveDepth253.depth_le_size _) (bounds name input)

end Yulang.GeneralNominalInputReadback254

