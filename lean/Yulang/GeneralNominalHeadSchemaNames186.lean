import Yulang.GeneralNominalHeadSchemaSemantic186
import Yulang.GeneralDictionaryActualSchemaScope
import Yulang.GeneralPatternVariableProvenance

/-! Every generated head use has actual mode and a checked input name.
Translator scope and normalization provenance are reused; no new pattern
semantics or complete-inspection premise is introduced. -/
namespace Yulang.GeneralNominalHeadSchemaNames186
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalCenters
open GeneralNominalMaterialization GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query)
open GeneralDictionaryActualSchemaScope

mutual
 theorem schema_actual (query : Query) (origin : Origin) (entry : Use)
    (present : entry ∈ (schema query origin .actual).variables) : entry.mode = .actual := by
  cases query with
  | variables names =>
    simp only [schema] at present
    obtain ⟨name,_,rfl⟩ := List.mem_map.mp present
    rfl
  | scalar base => simp [schema] at present
  | deferred reason => simp [schema] at present
  | node shape children =>
    simp only [schema] at present
    exact schemas_actual children _ 0 entry present
  | nominal name children =>
    simp only [schema] at present
    exact schemas_actual children _ 0 entry present
 termination_by sizeOf query

 theorem schemas_actual (queries : List Query) (origins : Nat → Origin) (offset : Nat)
    (entry : Use) (present : entry ∈ (schemas queries origins .actual offset).variables) :
    entry.mode = .actual := by
  cases queries with
  | nil => simp [schemas] at present
  | cons query rest =>
    simp only [schemas,Schema.append] at present
    rcases List.mem_append.mp present with first | last
    · exact schema_actual query (origins offset) entry first
    · exact schemas_actual rest origins (offset+1) entry last
 termination_by sizeOf queries
end

 theorem head_actual (plan : Plan roles) (entry : Use) (present : entry ∈ plan.headSchema.variables) :
    entry.mode = .actual := schemas_actual _ _ 0 entry present

 theorem head_input (plan : Plan roles) (entry : Use) (present : entry ∈ plan.headSchema.variables) :
    entry.name ∈ plan.packet.declaration.inputNames := by
  apply schemas_scoped (fun name => name ∈ plan.packet.declaration.inputNames) _ _ .actual 0 _ entry present
  rw [queries_scoped_iff]
  intro query member
  obtain ⟨pattern,patternMember,rfl⟩ := List.mem_map.mp member
  exact query_scoped_mono _ _
    (fun name used => variables_args_member _ pattern patternMember name used)
    _ (translated_scoped _ _ pattern)

 theorem input_not_output (plan : Plan roles) (name : Nat)
    (input : name ∈ plan.packet.declaration.inputNames) : name ∉ plan.packet.declaration.outputNames := by
  intro output
  exact plan.packet.checked.outputOnly.1 name output
    (GeneralPatternVariableProvenance.normalize_args_variables _ input)

 theorem head_not_output (plan : Plan roles) (entry : Use) (present : entry ∈ plan.headSchema.variables) :
    entry.name ∉ plan.packet.declaration.outputNames := input_not_output plan entry.name (head_input plan entry present)

end Yulang.GeneralNominalHeadSchemaNames186
