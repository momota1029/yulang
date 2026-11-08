import SpecExamples
import Yulang.CommonRoleSettledExamples
import Yulang.CommonSourceOptionalX22
import Yulang.CommonRoleOpenNormalization

/-!
# X1–X24: unified entry-sensitive conformance index

This is a status index, not a new conformance proof. `provedComponent` means
only the named component entry; `provedSettled` means the settled lowered-role
entry; `provedSource` names the new structural source-pattern/case entry.
None means integration into Core.infer. The old tables remain historical.
X22's new entry succeeds while the legacy strict entry still rejects.
X15/X16 have local normalization results only, NOT outer resolver proofs.
The #check commands below validate every cited evidence declaration.
-/
namespace Yulang.SpecConformanceIndex

inductive Status where
  | provedComponent
  | provedSettled
  | provedSource
  | localOnly
  | unavailable
  deriving DecidableEq, Repr

structure Entry where
  id : Nat
  status : Status
  entry : String
  evidence : List String
  boundary : String
  deriving Repr

def entries : List Entry := [
  ⟨1, .provedComponent, "Yulang.CheckedRoles.checkImpl",
    ["Yulang.SpecExamples.x1_declaration_accepted"], "Declaration check; not Core.infer"⟩,
  ⟨2, .provedComponent, "Yulang.CheckedRoles.checkImpl",
    ["Yulang.SpecExamples.x2_declaration_rejected"], "Declaration rejection; not Core.infer"⟩,
  ⟨3, .provedComponent, "Yulang.CommonRoleNormalizedDeclarations.checkImpl",
    ["Yulang.SpecExamples.x3_shadow_rejected"], "Normalized declaration check"⟩,
  ⟨4, .unavailable, "", [], "Source record-tail scheduler/resolver missing"⟩,
  ⟨5, .provedComponent, "Yulang.CommonRoleStablePaterson.check",
    ["Yulang.SpecExamples.x5_rejected"], "Stable declaration check"⟩,
  ⟨6, .provedSettled, "Yulang.CommonRoleSettledResolver.classify",
    ["Yulang.CommonRoleSettledExamples.x6_single_selected",
     "Yulang.CommonRoleSettledExamples.x6_ambiguous",
     "Yulang.CommonRoleSettledExamples.x6_source_lowered"], "Lowered settled fragment only"⟩,
  ⟨7, .unavailable, "", [], "Associated-type declaration checker for record heads missing"⟩,
  ⟨8, .provedSettled, "Yulang.CommonRoleSettledResolver.classify",
    ["Yulang.CommonRoleSettledExamples.x8_len_selected"], "Lowered settled fragment only"⟩,
  ⟨9, .provedSettled, "Yulang.CommonRoleSettledResolver.classify",
    ["Yulang.CommonRoleSettledExamples.x9_where_tree", "Yulang.CommonRoleSettledExamples.x9_show_rejected"],
    "where_tree uses CommonRoleSettledResolver.resolve; final rejection uses classify"⟩,
  ⟨10, .provedSettled, "Yulang.CommonRoleSettledResolver.classify",
    ["Yulang.CommonRoleSettledExamples.x10_inspection_rejected"], "Lowered settled fragment only"⟩,
  ⟨11, .provedSettled, "Yulang.CommonRoleSettledResolver.classify",
    ["Yulang.CommonRoleSettledExamples.x11_rejection_before_ambiguity"], "Lowered settled K2 priority"⟩,
  ⟨12, .provedSettled, "Yulang.CommonRoleSettledResolver.classify",
    ["Yulang.CommonRoleSettledExamples.x12_named_selected"], "Lowered opaque nominal fragment"⟩,
  ⟨13, .unavailable, "", [], "Source bounds/co-occurrence outer bridge missing"⟩,
  ⟨14, .unavailable, "", [], "Non-singleton nested source interval outer pipeline missing"⟩,
  ⟨15, .localOnly, "Yulang.CommonRoleOpenNormalization.normalize",
    ["Yulang.CommonRoleOpenNormalization.normalize_prefix"],
    "Same-head lifting only; no outer resolve proof of X15"⟩,
  ⟨16, .localOnly, "Yulang.CommonRoleOpenNormalization.normalize",
    ["Yulang.CommonRoleOpenNormalization.normalize_different"],
    "Different-head interval retained locally; no outer resolve proof of X16"⟩,
  ⟨17, .unavailable, "", [], "Invariant function interval source bridge missing"⟩,
  ⟨18, .provedComponent, "Yulang.CommonDeclarationVarianceTable.deriveVariance",
    ["Yulang.SpecExamples.x18_box_covariant", "Yulang.SpecExamples.x18_box2_covariant",
     "Yulang.SpecExamples.x18_reset_covariant", "Yulang.SpecExamples.x18_stream_covariant"],
    "Declaration-derived variance table; not full carrier/cast adequacy"⟩,
  ⟨19, .provedComponent, "Yulang.CommonDeclarationVarianceTable.deriveVariance",
    ["Yulang.SpecExamples.x19_chain_invariant", "Yulang.SpecExamples.x19_mutual_invariant"],
    "Declaration-derived variance table; not full carrier/cast adequacy"⟩,
  ⟨20, .provedComponent, "Yulang.CommonDeclarationVarianceTable.deriveVariance",
    ["Yulang.SpecExamples.x20_phantom_unused"], "Declaration-derived unused classification"⟩,
  ⟨21, .unavailable, "", [], "Rank-2 actual sub source-body bridge missing"⟩,
  ⟨22, .provedSource, "Yulang.CommonSourceArmsSolved.infer",
    ["Yulang.CommonSourceOptionalX22.x22_source_generated",
     "Yulang.CommonSourceOptionalX22.x22_real_scheme_instance",
     "Yulang.CommonSourceOptionalX22.x22_absent_case_result",
     "Yulang.CommonSourceOptionalX22.x22_present_case_result",
     "Yulang.CommonSourceOptionalX22.x22_proved"],
    "New structural source entry; legacy strict entry remains MISMATCH; Core.infer not replaced"⟩,
  ⟨23, .unavailable, "", [], "Complete source static-effect-row generator missing"⟩,
  ⟨24, .unavailable, "", [], "Source pipe/catch and handler execution bridge missing"⟩
]

/-- Exactly one row per requested ID, in order. This proves table coverage,
not semantic completeness of the language. -/
theorem ids_exact : entries.map Entry.id = List.range' 1 24 := by decide

#check Yulang.CheckedRoles.checkImpl
#check Yulang.CommonRoleNormalizedDeclarations.checkImpl
#check Yulang.CommonRoleStablePaterson.check
#check Yulang.CommonRoleSettledResolver.classify
#check Yulang.CommonRoleSettledResolver.resolve
#check Yulang.CommonRoleOpenNormalization.normalize
#check Yulang.CommonDeclarationVarianceTable.deriveVariance
#check Yulang.CommonSourceArmsSolved.infer
#check Yulang.SpecExamples.x1_declaration_accepted
#check Yulang.SpecExamples.x2_declaration_rejected
#check Yulang.SpecExamples.x3_shadow_rejected
#check Yulang.SpecExamples.x5_rejected
#check Yulang.CommonRoleSettledExamples.x6_single_selected
#check Yulang.CommonRoleSettledExamples.x6_ambiguous
#check Yulang.CommonRoleSettledExamples.x6_source_lowered
#check Yulang.CommonRoleSettledExamples.x8_len_selected
#check Yulang.CommonRoleSettledExamples.x9_where_tree
#check Yulang.CommonRoleSettledExamples.x9_show_rejected
#check Yulang.CommonRoleSettledExamples.x10_inspection_rejected
#check Yulang.CommonRoleSettledExamples.x11_rejection_before_ambiguity
#check Yulang.CommonRoleSettledExamples.x12_named_selected
#check Yulang.CommonRoleOpenNormalization.normalize_prefix
#check Yulang.CommonRoleOpenNormalization.normalize_different
#check Yulang.SpecExamples.x18_box_covariant
#check Yulang.SpecExamples.x18_box2_covariant
#check Yulang.SpecExamples.x18_reset_covariant
#check Yulang.SpecExamples.x18_stream_covariant
#check Yulang.SpecExamples.x19_chain_invariant
#check Yulang.SpecExamples.x19_mutual_invariant
#check Yulang.SpecExamples.x20_phantom_unused
#check Yulang.CommonSourceOptionalX22.x22_source_generated
#check Yulang.CommonSourceOptionalX22.x22_real_scheme_instance
#check Yulang.CommonSourceOptionalX22.x22_absent_case_result
#check Yulang.CommonSourceOptionalX22.x22_present_case_result
#check Yulang.CommonSourceOptionalX22.x22_proved
#check Yulang.SpecExamples.x22_strict_rejects
#check Yulang.SpecExamples.x22_main_generator_rejects

end Yulang.SpecConformanceIndex
