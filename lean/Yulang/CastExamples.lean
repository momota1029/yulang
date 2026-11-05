import Yulang.Methods
import Yulang.LiteralCasts

/-!
# Executable boundary regressions

These examples use equality as the supplied ordinary-compatibility relation.
They test cast routing and rejection, not completeness of a structural-subtyping
solver or execution/effect preservation of conversion bodies.
-/

namespace Yulang.CastExamples

open Casts CastGraph

def intType : Ty := .base .int
def strType : Ty := .base .str
def idType : Ty := .nominal 0 []
def listType (element : Ty) : Ty := .nominal 1 [element]

attribute [local simp] accepts converts fields Ty.isNominal Ty.isRecord Ty.lookup
  equalityCompatibility intType strType idType listType

def idToInt : Registry 2 where
  types := fun vertex => if vertex = 0 then idType else intType
  rules := [(0, 1)]

theorem idToInt_valid : idToInt.WellFormed := by decide

theorem scalar_conversion :
    checkBoundary equalityCompatibility idToInt idType intType = .converted := by
  simp [checkBoundary] <;> decide

theorem source_union_all_members_convert :
    checkBoundary equalityCompatibility idToInt (.union intType idType) intType = .converted := by
  simp [checkBoundary] <;> decide

theorem source_union_missing_member_is_rejected :
    checkBoundary equalityCompatibility idToInt (.union intType strType) intType = .rejected := by
  simp [checkBoundary] <;> decide

theorem arrow_argument_is_contravariant :
    checkBoundary equalityCompatibility idToInt (.arrow intType intType) (.arrow idType intType) =
      .converted := by
  simp [checkBoundary] <;> decide

theorem arrow_argument_wrong_direction_rejected :
    checkBoundary equalityCompatibility idToInt (.arrow idType intType) (.arrow intType intType) =
      .rejected := by
  simp [checkBoundary] <;> decide

theorem arrow_result_is_covariant :
    checkBoundary equalityCompatibility idToInt (.arrow intType idType) (.arrow intType intType) =
      .converted := by
  simp [checkBoundary] <;> decide

theorem tuple_components_are_covariant :
    checkBoundary equalityCompatibility idToInt (.pair idType strType) (.pair intType strType) =
      .converted := by
  simp [checkBoundary] <;> decide

theorem record_fields_follow_labels :
    checkBoundary equalityCompatibility idToInt
      (.record 1 strType (.record 0 idType .emptyRecord))
      (.record 0 intType .emptyRecord) = .converted := by
  simp [checkBoundary] <;> decide

theorem shadowed_target_field_is_not_an_obligation :
    checkBoundary equalityCompatibility idToInt (.record 0 idType .emptyRecord)
      (.record 0 intType (.record 0 strType .emptyRecord)) = .converted := by
  simp [checkBoundary] <;> decide

theorem variant_payload_is_covariant :
    checkBoundary equalityCompatibility idToInt (.variant 0 idType) (.variant 0 intType) =
      .converted := by
  simp [checkBoundary] <;> decide

theorem distinct_variant_tags_are_not_payload_casts :
    checkBoundary equalityCompatibility idToInt (.variant 0 idType) (.variant 1 intType) =
      .rejected := by
  simp [checkBoundary] <;> decide

theorem fixed_nominal_arguments_do_not_cast :
    checkBoundary equalityCompatibility idToInt (listType idType) (listType intType) =
      .rejected := by
  simp [checkBoundary] <;> decide

/-- An explicit outer rule is different from lifting the element rule. -/
def outerListRule : Registry 2 where
  types := fun vertex => if vertex = 0 then listType idType else listType intType
  rules := [(0, 1)]

theorem explicit_outer_nominal_rule_is_accepted :
    checkBoundary equalityCompatibility outerListRule (listType idType) (listType intType) =
      .converted := by
  simp [checkBoundary] <;> decide

def selfRule : Registry 1 where
  types := fun _ => intType
  rules := [(0, 0)]

theorem existing_match_skips_registered_conversion :
    checkBoundary equalityCompatibility selfRule intType intType = .unchanged := by decide

def duplicateRule : Registry 2 where
  types := idToInt.types
  rules := [(0, 1), (0, 1)]

theorem duplicate_direct_declarations_are_rejected :
    checkBoundary equalityCompatibility duplicateRule idType intType = .invalidRegistry := by decide

def diamond : Registry 4 where
  types := fun vertex => .nominal vertex.val []
  rules := [(0, 1), (0, 2), (1, 3), (2, 3)]

theorem multiple_transitive_paths_are_permitted :
    checkBoundary equalityCompatibility diamond (.nominal 0 []) (.nominal 3 []) = .converted := by
  simp [checkBoundary] <;> decide

def hasAdd (receiver : Ty) : Bool := decide (receiver = intType)
def hasShow (receiver : Ty) : Bool := decide (receiver = intType ∨ receiver = idType)

theorem method_unique_member_casts_the_whole_union :
    Methods.checkCall equalityCompatibility idToInt hasAdd [intType, idType] =
      .resolved intType := by
  simp [Methods.checkCall, Methods.resolve, Methods.candidates, Methods.select, Methods.AllEqual,
    Methods.membersAccept, hasAdd] <;> decide

theorem method_missing_conversion_is_rejected :
    Methods.checkCall equalityCompatibility idToInt hasAdd [intType, strType] =
      .missingCast := by
  simp [Methods.checkCall, Methods.resolve, Methods.candidates, Methods.select, Methods.AllEqual,
    Methods.membersAccept, hasAdd] <;> decide

theorem method_multiple_owners_are_ambiguous :
    Methods.checkCall equalityCompatibility idToInt hasShow [idType, intType] =
      .ambiguous := by decide

theorem duplicate_union_members_do_not_create_ambiguity :
    Methods.checkCall equalityCompatibility idToInt hasAdd [idType, intType, intType] =
      .resolved intType := by
  simp [Methods.checkCall, Methods.resolve, Methods.candidates, Methods.select, Methods.AllEqual,
    Methods.membersAccept, hasAdd] <;> decide

def intToId : Registry 2 where
  types := idToInt.types
  rules := [(1, 0)]

def integerLiteral : LiteralCasts.DeferredLiteral :=
  ⟨100, [⟨101, intType⟩]⟩

theorem chosen_literal_target_checks_the_original_site :
    LiteralCasts.finish equalityCompatibility intToId integerLiteral (some idType) =
      some (integerLiteral.targetPlan idType) := by
  simp [LiteralCasts.finish, LiteralCasts.sitesAccept, integerLiteral] <;> decide

theorem already_built_list_is_not_rewritten :
    checkBoundary equalityCompatibility intToId (listType intType) (listType idType) =
      .rejected := by
  simp [checkBoundary] <;> decide

def mixedLiteral : LiteralCasts.DeferredLiteral :=
  ⟨200, [⟨201, intType⟩, ⟨202, idType⟩]⟩

theorem eof_keeps_the_original_element_union :
    LiteralCasts.finish equalityCompatibility idToInt mixedLiteral none =
      some ⟨200, .unionOf [intType, idType],
        [.keep ⟨201, intType⟩, .keep ⟨202, idType⟩]⟩ := by
  simp [LiteralCasts.finish, LiteralCasts.DeferredLiteral.fallbackPlan, mixedLiteral] <;> decide

theorem literal_target_rejects_a_missing_element_cast :
    LiteralCasts.finish equalityCompatibility idToInt
      ⟨300, [⟨301, intType⟩, ⟨302, strType⟩]⟩ (some intType) = none := by
  simp [LiteralCasts.finish, LiteralCasts.sitesAccept] <;> decide

end Yulang.CastExamples
