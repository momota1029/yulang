import Yulang.GeneralDictionaryDefaultOverlap214

/-! Closed overlap/duplicate regression. A retained target may itself occur
on the right; the older target-disjoint extension premise rejects this case. -/
namespace Yulang.GeneralDictionaryDefaultOverlapRegression214
open GeneralNominalCenteredHeadMatExpressions GeneralNominalCenteredHeadMatSchemas
open GeneralNominalMaterialization (Mode)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryDefaultOverlap214
open CommonNominalFullCarrier

def resolve (_ : Mode) (name : Nat) : Nat := name
def self : Equation := ⟨0,.actual,.variable 0⟩
def copy : Equation := ⟨1,.actual,.variable 0⟩
def schema : Schema := ⟨[self,self,copy],false⟩
def keep : List Nat := [0]

theorem reads_retained : ReadsRetained keep resolve schema.equations := by
  intro equation member name used
  simp only [schema,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;>
    exact Or.inl (List.mem_singleton.mpr (List.mem_singleton.mp used))

theorem compatible (before : Assignment) :
    GeneralDictionaryDefaultSharedTargets212.Compatible resolve before schema.equations := by
  intro first one last two _
  simp only [schema,List.mem_cons,List.not_mem_nil,or_false] at one two
  rcases one with rfl | rfl | rfl <;> rcases two with rfl | rfl | rfl <;>
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem overlap (before : Assignment) : Overlap keep resolve before schema.equations := by
  intro equation member inside
  simp only [schema,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨subtype_refl _,subtype_refl _⟩
  · exact ⟨subtype_refl _,subtype_refl _⟩
  · have bad : (1:Nat) ∈ [0] := inside
    simp at bad

theorem constructed (before : Assignment) :
    schema.Holds (GeneralNominalCenteredHeadMatExtension.sources resolve
      (extendKeeping keep resolve before schema.equations))
      (extendKeeping keep resolve before schema.equations) :=
  holds reads_retained (compatible before) (overlap before)

theorem retained_value (before : Assignment) :
    extendKeeping keep resolve before schema.equations 0 = before 0 := kept (by simp [keep])

theorem repeated_targets : ¬ (schema.equations.map Equation.target).Nodup := by decide +kernel

theorem not_independent : ¬ GeneralDictionaryDefaultModeSupport212.Independent resolve schema.equations := by
  intro independent
  exact independent self (by simp [schema]) 0 (by simp [self,resolve,GeneralDictionaryDefaultModeSupport212.reads])
    (by simp [schema,self,copy])
end Yulang.GeneralDictionaryDefaultOverlapRegression214

namespace Yulang.GeneralDictionaryDefaultOverlapRegression214
open GeneralNominalCenteredHeadMatExpressions GeneralNominalCenteredHeadMatSchemas
open GeneralDictionaryDefaultOverlap214
open CommonNominalFullCarrier

def semanticSelf : Equation := ⟨0,.actual,.join (.variable 0) (.variable 0)⟩
def semanticSchema : Schema := ⟨[self,semanticSelf],false⟩
def uniform : GeneralNominalCommonBridge.Assignment := fun _ => (.base .int,Common.rowEmpty)

theorem union_self (type : Ty) : Equivalent type (.union type type) := by
  constructor
  · intro depth
    exact CommonNominalFullDemand.producerLe_union_left _ _
  · exact (common_union_is_join type type type).mpr ⟨subtype_refl _,subtype_refl _⟩

theorem semantic_readback :
    Equivalent (uniform semanticSelf.target).1
      (value (GeneralNominalCenteredHeadMatExtension.sources resolve uniform)
        semanticSelf.mode semanticSelf.expression) := union_self _

theorem not_literal_readback :
    (uniform semanticSelf.target).1 ≠
      value (GeneralNominalCenteredHeadMatExtension.sources resolve uniform)
        semanticSelf.mode semanticSelf.expression := by
  intro equal
  change CommonNominalSyntax.Layer.base Inference.Base.int =
    CommonNominalSyntax.Layer.union (.base .int) (.base .int) at equal
  cases equal

theorem semantic_retained : ReadsRetained keep resolve semanticSchema.equations := by
  intro equation member name used
  rcases List.mem_cons.mp member with rfl | member
  · exact Or.inl (List.mem_singleton.mpr (List.mem_singleton.mp used))
  · cases List.mem_singleton.mp member
    have same : name = 0 := by simpa [semanticSelf,GeneralDictionaryDefaultModeSupport212.reads,resolve] using used
    exact Or.inl (List.mem_singleton.mpr same)

theorem semantic_overlap : Overlap keep resolve uniform semanticSchema.equations := by
  intro equation member _
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨subtype_refl _,subtype_refl _⟩
  · cases List.mem_singleton.mp member
    exact semantic_readback

theorem semantic_compatible :
    GeneralDictionaryDefaultSharedTargets212.Compatible resolve uniform semanticSchema.equations := by
  intro first one last two _
  have a := semantic_overlap first one (by
    rcases List.mem_cons.mp one with rfl | member
    · exact List.mem_singleton_self _
    · cases List.mem_singleton.mp member; exact List.mem_singleton_self _)
  have b := semantic_overlap last two (by
    rcases List.mem_cons.mp two with rfl | member
    · exact List.mem_singleton_self _
    · cases List.mem_singleton.mp member; exact List.mem_singleton_self _)
  exact GeneralDictionaryDefaultExpression209.equivalent_trans ⟨a.2,a.1⟩ b

theorem semantic_constructed :
    semanticSchema.Holds (GeneralNominalCenteredHeadMatExtension.sources resolve
      (extendKeeping keep resolve uniform semanticSchema.equations))
      (extendKeeping keep resolve uniform semanticSchema.equations) :=
  holds semantic_retained semantic_compatible semantic_overlap
end Yulang.GeneralDictionaryDefaultOverlapRegression214
