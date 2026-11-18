import Yulang.GeneralNominalOutputReadback254
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalDefaultReadback254
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalCenters
open GeneralNominalCenteredHeadMatPatternSemantics GeneralNominalCenteredHeadMatSemanticSubstitution
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalCenteredHeadMatSemanticLabels (Inputs)
open GeneralPatternAdditiveDepth253 (depth)
open GeneralNominalPatersonLineage (mass)
open CommonNominalFullCarrier (Equivalent)
variable {roles : Roles.RoleDecls} {plan : Plan roles} {model : GeneralNominalCommonBridge.Assignment}

mutual
 def pattern : Roles.Term → Pattern
 | .var name => .var name
 | .app name terms => .app name (patterns terms)
 def patterns : List Roles.Term → List Pattern
 | [] => []
 | term :: terms => pattern term :: patterns terms
end

mutual
 theorem compiled (term : Roles.Term) :
 GeneralNominalCenteredHeadMatExpressions.translate constructors interpretation (pattern term) =
 GeneralNominalCenteredHeadMatExpressions.translateDefault constructors interpretation term := by
 cases term with
 | var => rfl
 | app name terms =>
   simp only [pattern,GeneralNominalCenteredHeadMatExpressions.translate,
     GeneralNominalCenteredHeadMatExpressions.translateDefault,compiled_many]
 theorem compiled_many (terms : List Roles.Term) :
 GeneralNominalCenteredHeadMatExpressions.translateMany constructors interpretation (patterns terms) =
 GeneralNominalCenteredHeadMatExpressions.translateDefaults constructors interpretation terms := by
 cases terms with
 | nil => rfl
 | cons term terms =>
   simp only [patterns,GeneralNominalCenteredHeadMatExpressions.translateMany,
     GeneralNominalCenteredHeadMatExpressions.translateDefaults,compiled,compiled_many]
end

mutual
 theorem variable_bound (term : Roles.Term) (name : Nat) (member : name ∈ (pattern term).variables) : name < term.bound := by
 cases term with
 | var n => cases List.mem_singleton.mp member; exact Nat.lt_succ_self _
 | app key terms => exact variables_bound terms name member
 theorem variables_bound (terms : List Roles.Term) (name : Nat) (member : name ∈ variablesArgs (patterns terms)) :
 name < Roles.argsBound terms := by
 cases terms with
 | nil => cases member
 | cons term terms =>
   rcases List.mem_append.mp member with first | rest
   · exact Nat.lt_of_lt_of_le (variable_bound term name first) (Nat.le_max_left _ _)
   · exact Nat.lt_of_lt_of_le (variables_bound terms name rest) (Nat.le_max_right _ _)
end

/-- Positional defaults read input centers, not declaration binders. Default
scope is the RoleDecl field already required by the source signature. -/
theorem default_readback
 (known : Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model plan.input labels)
 (sameRole : plan.packet.declaration.role = plan.input.occurrence.demand.role)
 (declared : (roles plan.packet.declaration.role).assoc name = some (some rhs))
 (compiled : GeneralNominalCenteredHeadMatEffects.compileBody plan (.default plan.packet.declaration.role name rhs) = some expression)
 (held : GeneralNominalCenteredHeadMatEffects.BodyHolds plan target model (.default plan.packet.declaration.role name rhs)) :
 ∃ result : Pattern, result.variables = [] ∧
 Equivalent (model target).1
   (eval (algebra plan.packet.registry.constructors plan.packet.context.interpretation) (fun _ => .bottom) result) ∧
 depth result ≤ depth (pattern rhs) + mass labels := by
 obtain ⟨length,inputs⟩ := known
 have scope := (roles plan.packet.declaration.role).defaultsScoped name rhs declared
 rw [sameRole] at scope
 let capture : Nat → Pattern := fun index => if inside : index < labels.length then normalize labels[index] else .var index
 have validIndex (index : Nat) (used : index ∈ (pattern rhs).variables) : index < labels.length := by
   rw [length]; exact Nat.lt_of_lt_of_le (variable_bound rhs index used) scope
 have closed (index : Nat) (used : index ∈ (pattern rhs).variables) : (capture index).variables = [] := by
   have bound := validIndex index used
   simpa only [capture,dite_eq_left bound] using (inputs ⟨index,by rw [←length]; exact bound⟩).1
 have bounded (index : Nat) (used : index ∈ (pattern rhs).variables) : depth (capture index) ≤ mass labels := by
   have bound := validIndex index used
   have sized := GeneralNominalQueryReadback254.member_sum
     ((normalizeArgs labels).map fun p => p.encode.size) (normalize labels[index]).encode.size
     (List.mem_map.mpr ⟨normalize labels[index],by
       rw [GeneralNominalChildAssembly.normalize_map]
       exact List.mem_map.mpr ⟨_,List.getElem_mem ..,rfl⟩,rfl⟩)
   have depthBound := GeneralPatternAdditiveDepth253.depth_le_size (normalize labels[index])
   simp only [capture,dite_eq_left bound]
   change depth (normalize labels[index]) ≤ Roles.argsSize (encodeArgs (normalizeArgs labels))
   rw [GeneralNominalCenteredHeadMatHeadParts.encoded_size]
   exact Nat.le_trans depthBound sized
 have values (index : Nat) (used : index ∈ (pattern rhs).variables) :
 Equivalent (GeneralNominalCenteredHeadMatEffects.defaultVariables plan model .actual index)
   (eval (algebra plan.packet.registry.constructors plan.packet.context.interpretation) (fun _ => .bottom) (capture index)) := by
   have bound := validIndex index used
   have within : index < (roles plan.input.occurrence.demand.role).arity := by rw [←length]; exact bound
   simpa only [GeneralNominalCenteredHeadMatEffects.defaultVariables,List.getElem?_ofFn,within,dite_eq_left,
     Option.getD_some,capture,dite_eq_left bound] using (inputs ⟨index,within⟩).2.2
 have translated : GeneralNominalCenteredHeadMatExpressions.translate plan.packet.registry.constructors
   plan.packet.context.interpretation (pattern rhs) = some expression := by
   rw [GeneralNominalDefaultReadback254.compiled]; exact compiled
 have equation := (GeneralNominalCenteredHeadMatEffects.body_equation compiled).mp held
 have exactValue := GeneralNominalCenteredHeadMatCompilerSemantics.translate_value
   (variables := GeneralNominalCenteredHeadMatEffects.defaultVariables plan model) (pattern rhs) translated
 change Equivalent (model target).1
   (GeneralNominalCenteredHeadMatExpressions.value (GeneralNominalCenteredHeadMatEffects.defaultVariables plan model) .actual expression) at equation
 rw [exactValue] at equation
 have substitute := eval_congr (algebra := algebra plan.packet.registry.constructors plan.packet.context.interpretation) (pattern rhs) values
 rw [← eval_subst (pattern rhs) capture] at substitute
 exact ⟨(pattern rhs).subst capture,subst_closed _ _ closed,eqv_trans equation substitute,
   GeneralDeclarationOutputDepth253.subst_supported _ capture _ bounded⟩

end Yulang.GeneralNominalDefaultReadback254
