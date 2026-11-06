import Yulang.CoreInference
import Yulang.CoreEffects
import Yulang.CoreQualified

/-! Existing principal schemes characterize exactly the corresponding Core
restrictions. This supplies no new solver or scheme for mixed Core syntax. -/
namespace Yulang.Core
open Inference (Model Comp)

theorem required_principal_exact (m : Model) (e : Inference.Expr)
    (schemes : Inference.SchemeEnv α) (Γ : List (Inference.Binding m))
    (ρ : α → Comp m) (related : Inference.EnvRel m ρ schemes Γ) (c : Comp m) :
    (Inference.principal schemes e).Holds m (Inference.extend ρ c) ↔
      Typing (Required.model m) (Γ.map Required.binding) (Required.embed e) c :=
  (Inference.principal_exact m e schemes Γ ρ related c).trans
    (Required.conservative m Γ e c)

theorem effects_principal_exact (m : Model)
    {algebra : RowInference.RowAlgebra Key Scope} (view : RowInference.RowView m algebra)
    (sigs : Op → RecursiveEffects.Signature m Key) (e : RecursiveEffects.Expr Op Key Scope)
    (signatureTerms : RecursiveEffects.Signatures Op Key α)
    (schemes : RecursiveEffects.SchemeEnv Key Scope α)
    (Γ : List (RecursiveEffects.Binding m Op Key Scope)) (ρ : α → Comp m)
    (related : RecursiveEffects.EnvRel m view sigs ρ schemes Γ)
    (signaturesRelated : RecursiveEffects.SigRel m ρ signatureTerms sigs) (c : Comp m) :
    (RecursiveEffects.principal signatureTerms schemes e).Holds m view (Inference.extend ρ c) ↔
      Typing (Effects.model m view sigs) (Γ.map Effects.binding) (Effects.embed e) c :=
  (RecursiveEffects.principal_exact m view sigs e signatureTerms schemes Γ ρ related signaturesRelated c).trans
    (Effects.conservative m view sigs Γ e c)

theorem qualified_principal_exact (m : Model) (methods : QualifiedInference.MethodTable)
    (theory : RoleConstraints.Theory m) (e : QualifiedInference.Expr)
    (schemes : QualifiedInference.SchemeEnv α) (Γ : List (QualifiedInference.Binding m))
    (ρ : α → Comp m) (related : QualifiedInference.EnvRel m theory ρ schemes Γ) (c : Comp m) :
    (QualifiedInference.principal methods schemes e).Holds m theory (Inference.extend ρ c) ↔
      Typing (Qualified.model m methods theory) Γ (Qualified.embed e) c :=
  (QualifiedInference.principal_exact m methods theory e schemes Γ ρ related c).trans
    (Qualified.conservative m methods theory Γ e c)

end Yulang.Core
