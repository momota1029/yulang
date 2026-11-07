import Yulang.CommonRoleCanonicalRows

/-!
# Payload unions produced by the actual tag-merging operation

No source producer-union annotation is assumed. A raw finite row repeats one
tag and one ordinary data pattern. `Variants.Merged.normalize` makes its tag
unique but retains right-associated union syntax in that tag's payload.
Canonical matching contracts identical payload branches before ordinary rigid
data capture. There are no record tails or arbitrary union splits here.
-/

namespace Yulang.CommonRoleMergedPayload

open CommonRoleLinearClock (Pattern Ground Rule Linear)

def dataTerm (pattern : Pattern) : Roles.Term :=
  (CommonRoleInspectedSemantics.liftPattern pattern).encode

def joinTerm (first last : Roles.Term) : Roles.Term := .app 4 [first, last]

def padded : Nat → Roles.Term → Roles.Term
  | 0, term => term
  | count + 1, term => joinTerm term (padded count term)

def rawRow (copies : Nat) (pattern : Pattern) : Variants.Row Nat Roles.Term :=
  List.replicate (copies + 1) (0, dataTerm pattern)

def mergedRow (copies : Nat) (pattern : Pattern) : Variants.Merged.Row Nat Roles.Term :=
  Variants.Merged.normalize joinTerm (rawRow copies pattern)

theorem merged_entries (copies : Nat) (pattern : Pattern) :
    (mergedRow copies pattern).entries = [(0, padded copies (dataTerm pattern))] := by
  induction copies with
  | zero => rfl
  | succ copies ih =>
      change (Variants.Merged.normalize joinTerm ((0, dataTerm pattern) :: rawRow copies pattern)).entries = _
      change Variants.Merged.Raw.insert joinTerm 0 (dataTerm pattern) (mergedRow copies pattern).entries = _
      rw [ih]
      rfl

theorem merged_tag_unique (copies : Nat) (pattern : Pattern) :
    ((mergedRow copies pattern).entries.map Prod.fst).Nodup := (mergedRow copies pattern).unique

def headTerm (copies : Nat) (pattern : Pattern) : Roles.Term := .app 3 [padded copies (dataTerm pattern)]
def plainTerm (pattern : Pattern) : Roles.Term := headTerm 0 pattern

def interpret (term : Roles.Term) (substitution : Nat → Common.Ty) : Option Common.Ty :=
  match term with
  | .var name => some (substitution name)
  | .app 0 [] => some (.base .int)
  | .app 1 [first, last] => do return Common.pair (← interpret first substitution) (← interpret last substitution)
  | .app 4 [first, last] => do return .union (← interpret first substitution) (← interpret last substitution)
  | .app (tag + 3) [payload] => do return Common.variant tag (← interpret payload substitution)
  | _ => none

@[simp] theorem interpret_data (pattern : Pattern) (substitution : Nat → Common.Ty) :
    interpret (dataTerm pattern) substitution = some (pattern.eval substitution) := by
  induction pattern <;> simp_all [dataTerm, CommonRoleInspectedSemantics.liftPattern,
    CommonRoleInspectedSemantics.Pattern.encode, interpret, CommonRoleLinearClock.Pattern.eval]

def paddedType : Nat → Common.Ty → Common.Ty
  | 0, type => type
  | copies + 1, type => .union type (paddedType copies type)

@[simp] theorem interpret_padded (copies : Nat) (pattern : Pattern) (substitution : Nat → Common.Ty) :
    interpret (padded copies (dataTerm pattern)) substitution = some (paddedType copies (pattern.eval substitution)) := by
  induction copies <;> simp_all [padded, joinTerm, interpret, paddedType]

theorem padded_equivalent (copies : Nat) (type : Common.Ty) : Common.Equivalent (paddedType copies type) type := by
  induction copies with
  | zero => exact Common.equivalent_refl _
  | succ copies ih =>
      exact ⟨(Common.common_union_is_join _ _ _).mpr ⟨Common.subtype_refl _, ih.1⟩,
        CommonBoundCoalescing.le_union_left _ _⟩

@[simp] theorem interpret_head (copies : Nat) (pattern : Pattern) (substitution : Nat → Common.Ty) :
    interpret (headTerm copies pattern) substitution =
      some (Common.variant 0 (paddedType copies (pattern.eval substitution))) := by
  simp [headTerm, interpret]

theorem head_meaning (copies : Nat) (pattern : Pattern) (substitution : Nat → Common.Ty) :
    Common.Equivalent (Common.variant 0 (paddedType copies (pattern.eval substitution)))
      (Common.variant 0 (pattern.eval substitution)) :=
  (CommonCanonicalShapes.variant_equivalent_iff 0 _ _).mpr (padded_equivalent copies _)

def unlift : CommonRoleInspectedSemantics.Pattern → Option Pattern
  | .var name => some (.var name)
  | .int => some .int
  | .pair first last => do return .pair (← unlift first) (← unlift last)
  | .variant tag payload => do return .variant tag (← unlift payload)
  | _ => none

theorem unlift_lift (pattern : Pattern) : unlift (CommonRoleInspectedSemantics.liftPattern pattern) = some pattern := by
  induction pattern <;> simp_all [unlift, CommonRoleInspectedSemantics.liftPattern]

def decodeData (term : Roles.Term) : Option Pattern :=
  (CommonRoleInspectedSemantics.decodePattern term).bind unlift

@[simp] theorem decode_data (pattern : Pattern) : decodeData (dataTerm pattern) = some pattern := by
  simp [decodeData, dataTerm, unlift_lift]

/-- Only identical duplicate branches are contracted. No noncanonical split
of a union payload is selected. Unsupported compound forms are outside this
verified counterfamily; this is not a full-language head decoder. -/
def contract : Roles.Term → Option Pattern
  | .app 4 [first, last] => do
      let a ← contract first
      let b ← contract last
      if a = b then some a else none
  | term => decodeData term

theorem contract_data (pattern : Pattern) : contract (dataTerm pattern) = some pattern := by
  cases pattern with
  | var name => rfl
  | int => rfl
  | pair first last => simpa [contract, dataTerm, CommonRoleInspectedSemantics.liftPattern,
      CommonRoleInspectedSemantics.Pattern.encode] using decode_data (.pair first last)
  | variant tag payload => simpa [contract, dataTerm, CommonRoleInspectedSemantics.liftPattern,
      CommonRoleInspectedSemantics.Pattern.encode] using decode_data (.variant tag payload)

@[simp] theorem contract_padded (copies : Nat) (pattern : Pattern) :
    contract (padded copies (dataTerm pattern)) = some pattern := by
  induction copies <;> simp_all [padded, joinTerm, contract, contract_data]

def decodeHead (args : List Roles.Term) : Option Pattern :=
  match args with
  | [.app 3 [payload]] => contract payload
  | _ => none

@[simp] theorem decode_head (copies : Nat) (pattern : Pattern) :
    decodeHead [headTerm copies pattern] = some pattern := by simp [decodeHead, headTerm]

theorem data_size (pattern : Pattern) : (dataTerm pattern).size = pattern.encode.size :=
  CommonRoleFiniteShadowRegistry.lift_size pattern

theorem data_occurrences (pattern : Pattern) (name : Nat) :
    (dataTerm pattern).occurrences name = pattern.encode.occurrences name :=
  CommonRoleFiniteShadowRegistry.lift_occurrences pattern name

theorem padded_size (copies : Nat) (term : Roles.Term) :
    (padded copies term).size = (copies + 1) * term.size + copies := by
  induction copies <;> simp_all [padded, joinTerm, Roles.Term.size, Roles.argsSize, Nat.add_mul] <;> omega

theorem padded_occurrences (copies : Nat) (term : Roles.Term) (name : Nat) :
    (padded copies term).occurrences name = (copies + 1) * term.occurrences name := by
  induction copies <;> simp_all [padded, joinTerm, Roles.Term.occurrences, Roles.argsOccurrences, Nat.add_mul] <;> omega

end Yulang.CommonRoleMergedPayload
