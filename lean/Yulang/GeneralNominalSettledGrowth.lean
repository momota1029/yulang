import Yulang.GeneralNominalSchemaBudget

/-! Constructor duplication is bounded by actual schema templates. A finite
settled readback tree therefore has an explicit growth bound; establishing
its source-fixed height remains the source producer's responsibility. -/
namespace Yulang.GeneralNominalSettledGrowth
open GeneralNominalRecipeBounds GeneralNominalSchemaBudget
open GeneralNominalOriginTerms GeneralNominalSharedSupport
open GeneralNominalRecursiveInspection GeneralNominalMaterialization

def growth (template input : Nat) : Nat → Nat
  | 0 => input + 1
  | depth+1 => template * (input + 1 + growth template input depth)

theorem growth_positive (positive : 0 < template) (input depth : Nat) :
    0 < growth template input depth := by
  cases depth with
  | zero => simp [growth]
  | succ depth => exact Nat.mul_pos positive (by omega)

theorem growth_step (positive : 0 < template) (input depth : Nat) :
    growth template input depth ≤ growth template input (depth+1) := by
  change _ ≤ template * (input + 1 + growth template input depth)
  have bound := Nat.mul_le_mul_right (input + 1 + growth template input depth) positive
  simp only [Nat.one_mul] at bound
  omega

theorem growth_mono (positive : 0 < template) (input : Nat) (bounded : first ≤ last) :
    growth template input first ≤ growth template input last := by
  induction bounded with
  | refl => exact Nat.le_refl _
  | step smaller ih => exact Nat.le_trans ih (growth_step positive input _)

/-- A finite substitution tree. This describes the shape of a readback proof,
not a replacement execution relation or a supplied ancestry rank. -/
inductive Assembly (template input : Nat) : Nat → Expr α → Prop
  | input (term : Expr α) (depth : Nat) : weight term ≤ input+1 → Assembly template input depth term
  | output (body : Expr Nat) (substitution : Nat → Expr α) : weight body ≤ template →
      (∀ name ∈ body.leaves, Assembly template input depth (substitution name)) →
      Assembly template input (depth+1) (body.bind substitution)

theorem assembly_bound (assembled : Assembly template input depth term) (positive : 0 < template) :
    weight term ≤ growth template input depth := by
  induction assembled with
  | input term depth bound => exact Nat.le_trans bound (growth_mono positive input (Nat.zero_le depth))
  | @output depth body substitution bounded children ih =>
    have substituted := weight_bind body substitution (input+1+growth template input depth) (by omega) (by
      intro name member
      have bounded := ih name member
      omega)
    exact Nat.le_trans substituted (Nat.mul_le_mul_right _ bounded)

/-- The actual output certificate's input uses are leaves. Output-only binders
substitute existing readbacks, so no fresh independent input leaf is introduced. -/
theorem certificate_growth (certificate : OutputCertificate state facts readbacks packet)
    (recipe : Recipe (GeneralNominalPacketSupport.namedSchema packet) root term)
    (prior : ∀ identity expression, (identity,expression) ∈ readbacks → weight expression ≤ previous) :
    weight (term.bind certificate.substitution) ≤
      treeBound (declarationBudget packet.context packet.declaration)
        (declarationBudget packet.context packet.declaration) * (previous+1) := by
  have substituted := weight_bind term certificate.substitution (previous+1) (by omega) (by
    intro name member
    obtain ⟨origin,use⟩ := recipe_leaf_use recipe member
    by_cases output : name ∈ packet.declaration.outputNames
    · have bounded := prior _ _ (certificate.binders _ use rfl output)
      dsimp only at bounded
      omega
    · obtain ⟨origin,equal,captured⟩ := certificate.inputs _ use rfl output
      rw [equal]
      simp only [weight]
      omega)
  exact Nat.le_trans substituted (Nat.mul_le_mul_right _ (packet_recipe_weight packet recipe))

theorem uniform_certificate_growth (context : GeneralNominalCandidates.Context)
    (certificate : OutputCertificate state facts readbacks packet)
    (visible : packet.declaration ∈ registry.declarations)
    (constructors : packet.context.state.constructors = context.state.constructors)
    (interpretation : packet.context.interpretation = context.interpretation)
    (recipe : Recipe (GeneralNominalPacketSupport.namedSchema packet) root term)
    (prior : ∀ identity expression, (identity,expression) ∈ readbacks → weight expression ≤ previous) :
    weight (term.bind certificate.substitution) ≤
      treeBound (registryBudget context registry) (registryBudget context registry) * (previous+1) := by
  have substituted := weight_bind term certificate.substitution (previous+1) (by omega) (by
    intro name member
    obtain ⟨origin,use⟩ := recipe_leaf_use recipe member
    by_cases output : name ∈ packet.declaration.outputNames
    · have bounded := prior _ _ (certificate.binders _ use rfl output)
      dsimp only at bounded
      omega
    · obtain ⟨origin,equal,captured⟩ := certificate.inputs _ use rfl output
      rw [equal]
      simp only [weight]
      omega)
  exact Nat.le_trans substituted (Nat.mul_le_mul_right _
    (uniform_packet_weight context packet visible constructors interpretation recipe))

end Yulang.GeneralNominalSettledGrowth
