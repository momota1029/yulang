import Yulang.CommonEffectArmGeneration
import Yulang.CommonEffectTypeNormalisation

/-! Actual universal elimination for operation-local payload-return arms.
This is a proved case of universal elimination, not a generic solver for all
operation bodies. Captured environments and all Common rows remain arbitrary. -/
namespace Yulang.CommonEffectUniversalPayload
open Core.PresenceGeneration
open CommonEffectRequestGeneration
open CommonEffectArmGeneration (generateArms generate_arms_exact)

/-- The operation-local value variable has no corresponding local row. -/
def localIdentity (key : Nat) : Declaration α where
  locals := 1
  key := key
  extra := []
  input := .var (.inr 0)
  output := .var (.inr 0)

theorem all_types_below_iff (upper : Common.Ty) :
    (∀ value : Common.Ty, Common.Subtype value upper) ↔ Common.Subtype .top upper :=
  ⟨fun all => all .top,
    fun topBound value => Common.subtype_trans (CommonEffectTypeNormalisation.subtype_top value) topBound⟩

theorem below_all_types_iff (lower : Common.Ty) :
    (∀ value : Common.Ty, Common.Subtype lower value) ↔ Common.Subtype lower .bottom :=
  ⟨fun all => all .bottom,
    fun bottomBound value => Common.subtype_trans bottomBound (CommonEffectTypeNormalisation.bottom_subtype value)⟩

/-- For the actual generated one-arm formula with body payload, arbitrary
local types force only a top value result. No universal check remains. -/
theorem generate_payload_arm_exact (environment : SchemeEnv α) (bindings : List (Binding Common.model))
    (assignment : α → Computation) (related : EnvRel Common.model assignment environment bindings)
    (key : Nat) (input out : CompTerm α) :
    (generateArms (scopes := scopes) environment (fun _ : Fin 1 => localIdentity key)
      input out (fun _ => .var 0)).Holds assignment ↔
      Common.Subtype .top (out.eval Common.model assignment).1 := by
  rw [generate_arms_exact environment bindings assignment related]
  simp only [localIdentity]
  constructor
  · intro universal
    obtain ⟨operated, valid⟩ := universal (fun _ _ => .top)
    have payloadBound : Comp.le Common.model (Comp.pure Common.model .top) (operated 0) := by
      simpa [localIdentity, Typing.var_iff, BindingLookup, BindingTyping.mono_iff,
        TyTerm.eval, localEnv, Comp.pure] using (valid 0).1
    exact Common.subtype_trans payloadBound.1 (valid 0).2.1
  · intro topBound locals
    refine ⟨fun i => Comp.pure Common.model (locals i 0), ?_⟩
    intro i
    constructor
    · apply Typing.var (b := .mono (Comp.pure Common.model (locals i 0))) rfl
      exact BindingTyping.mono ⟨Common.subtype_refl _, Common.rowLe_refl _⟩
    · exact ⟨Common.subtype_trans (CommonEffectTypeNormalisation.subtype_top _) topBound,
        Common.rowEmpty_le _⟩

/-- The elimination target is genuine finite syntax with no local binders,
not a semantic predicate embedded as an atom. -/
theorem eliminate_payload_arm (environment : SchemeEnv α) (bindings : List (Binding Common.model))
    (assignment : α → Computation) (related : EnvRel Common.model assignment environment bindings)
    (key : Nat) (input out : CompTerm α) :
    (generateArms (scopes := scopes) environment (fun _ : Fin 1 => localIdentity key)
      input out (fun _ => .var 0)).Holds assignment ↔
      (CommonEffectFormula.Formula.tyLe (scopes := scopes) .top out.ty).Holds assignment :=
  generate_payload_arm_exact environment bindings assignment related key input out
end Yulang.CommonEffectUniversalPayload
