import Yulang.CoreInference
import Yulang.RecursiveInference

/-! SCCs remain declaration blocks, not an expression constructor with invented
scope/evaluation rules. This interface separates heads from Core bodies. The
caller supplies the simultaneous environment, then the existing SCC solver and
closure/generalization protocol. No effect/case SCC inference is added (M3). -/
namespace Yulang.Core.Block
open Inference (Model Comp)
open RecursiveInference (Declaration FullAnnotation)

inductive Head (α : Type) where
  | inferred : α → Head α
  | annotated (parameters : Nat) : FullAnnotation α parameters → Head α

def entry : Declaration α → Head α × Required.Term
  | .inferred slot body => (.inferred slot, Required.embed body)
  | .annotated n annotation body => (.annotated n annotation, Required.embed body)

def embed (members : List (Declaration α)) : Core.SCC Signature.empty (Head α) :=
  ⟨members.map entry⟩

def DefinitionTyping (m : Model) (Γ : List (Required.Binding m)) (ρ : α → Comp m) :
    Head α × Required.Term → Prop
  | (.inferred slot, body) => Core.Typing (Required.model m) Γ body (ρ slot)
  | (.annotated _ annotation, body) =>
      ∀ locals, Core.Typing (Required.model m) Γ body (Comp.pure m (annotation.eval m ρ locals))

theorem definition_conservative (m : Model) (Γ : List (Inference.Binding m))
    (ρ : α → Comp m) (declaration : Declaration α) :
    RecursiveInference.DefinitionTyping m Γ ρ declaration ↔
      DefinitionTyping m (Γ.map Required.binding) ρ (entry declaration) := by
  cases declaration with
  | inferred slot body =>
    exact (RecursiveInference.DefinitionTyping.inferred_iff m Γ ρ slot body).trans
      (Required.conservative m Γ body (ρ slot))
  | annotated n annotation body =>
    rw [RecursiveInference.DefinitionTyping.annotated_iff]
    exact forall_congr' fun locals => Required.conservative m Γ body _

/-- This is simultaneous body checking under the supplied recursive context,
not SCC discovery, solving, annotation finalization or generalization. -/
def Typing (m : Model) (Γ : List (Required.Binding m)) (ρ : α → Comp m)
    (block : Core.SCC Signature.empty (Head α)) : Prop :=
  ∀ member ∈ block.members, DefinitionTyping m Γ ρ member

theorem conservative (m : Model) (Γ : List (Inference.Binding m)) (ρ : α → Comp m)
    (members : List (Declaration α)) :
    (∀ declaration ∈ members, RecursiveInference.DefinitionTyping m Γ ρ declaration) ↔
      Typing m (Γ.map Required.binding) ρ (embed members) := by
  simp only [Typing, embed, List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h member declaration present same
    cases same
    exact (definition_conservative m Γ ρ declaration).mp (h declaration present)
  · intro h declaration present
    exact (definition_conservative m Γ ρ declaration).mpr (h _ declaration present rfl)

theorem scc_conservative (m : Model) (Γ : List (Inference.Binding m)) (ρ : α → Comp m)
    (members : List (Declaration α)) :
    RecursiveInference.SCCTyping m Γ ρ members ↔
      Typing m ((RecursiveInference.bindings m ρ members Γ).map Required.binding)
        ρ (embed members) :=
  conservative m (RecursiveInference.bindings m ρ members Γ) ρ members

theorem generate_exact (m : Model) (Γ : List (Inference.Binding m)) (ρ : α → Comp m)
    (schemes : Inference.SchemeEnv α) (related : Inference.EnvRel m ρ schemes Γ)
    (members : List (Declaration α)) :
    (RecursiveInference.generateSCC schemes members).Holds m ρ ↔
      Typing m ((RecursiveInference.bindings m ρ members Γ).map Required.binding)
        ρ (embed members) :=
  (RecursiveInference.generateSCC_exact m ρ schemes Γ related members).trans
    (scc_conservative m Γ ρ members)

end Yulang.Core.Block
