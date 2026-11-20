import Yulang.GeneralSourceRoleCstOtherRole295

/-! The language-facing naming environment remains explicit. Varying entries
outside the selected symbolic declaration cannot influence its lowering. -/
namespace Yulang.GeneralSourceRoleCstNamingScope295
open GeneralSourceRoleTrack292 (Tracked forget runTracked)
open GeneralSourceRoleHeadPacketRun292 (makePacket run)
open GeneralSourceRoleScopedShell292 (project)
open GeneralSourceRoleScopedExport292 (ScopedRole lower)
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceRoleLocalEnv292 (Agree role_agrees)
open GeneralSourceRoleExport292 (collect)
open GeneralSourceMetadataRoles291 (RoleSource)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleCstSelectedCompile295 (Boundary handoff compile)

def symbolic {S H : Type} (p : Tracked S H) : Option (ScopedRole S) :=
  (makePacket (forget p)).bind project

theorem tracked_symbolic {S H : Type} (p : Tracked S H) (env : S → Environment)
    (fallback : Nat) :
    runTracked env fallback [p] =
      (symbolic p).bind (fun r => lower env fallback [r]) := by
  cases h : makePacket (forget p) with
  | none => simp [runTracked,run,collect,symbolic,h]
  | some packet =>
    cases parsed : project packet with
    | none => simp [runTracked,run,collect,symbolic,h,GeneralSourceRoleScopedShell292.run,parsed]
    | some role => simp [runTracked,run,collect,symbolic,h,GeneralSourceRoleScopedShell292.run,parsed]

theorem tracked_env_congr {S H : Type} (p : Tracked S H) (fallback : Nat)
    (before after : S → Environment)
    (same : ∀ r, symbolic p = some r → Agree (before r.scope) (after r.scope) r.role) :
    runTracked before fallback [p] = runTracked after fallback [p] := by
  rw [tracked_symbolic,tracked_symbolic]
  cases h : symbolic p with
  | none => rfl
  | some r =>
    simp [lower,collect,role_agrees r.role (same r h)]

theorem compile_env_congr {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B) (sealed : Boundary S B)
    (before after : S → Environment) (fallback : Nat)
    (same : ∀ p, handoff policy scope w brand a sealed = some p →
      ∀ r, symbolic p = some r → Agree (before r.scope) (after r.scope) r.role) :
    compile policy scope w brand a sealed before fallback =
      compile policy scope w brand a sealed after fallback := by
  cases h : handoff policy scope w brand a sealed with
  | none => simp [compile,h]
  | some p =>
    simp only [compile,h,Option.bind_some]
    exact tracked_env_congr p fallback before after (same p h)

end Yulang.GeneralSourceRoleCstNamingScope295
