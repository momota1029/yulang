import Yulang.GeneralRebasePrivatePacket282

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebasePrivateClass282
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedFrame231 (binder_eq)
open GeneralRebasePrivateKey282 (port Excludes binder_private)
open GeneralRebasePrivateSchema282 (SiteSafe index_private port_nonzero)
open GeneralRebasePrivatePacket282 (Safe)
open GeneralDictionaryAssociatedProvenance (Body)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralDictionaryDefault214ActualBodyFrame (bodySources classSources)
open GeneralNominalCenteredHeadMatEffects (bodySchema compileBody BodyHolds)
open GeneralDictionaryDefaultModeSupport212 (reads readMany)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalMaterialization (Mode)

mutual
theorem reads_private (resolve : Mode → Nat → Nat) (safe : ∀ mode name, t ≠ resolve mode name)
    (mode : Mode) (e : Expr) : t ∉ reads resolve mode e := by
  cases e with
  | «variable» name => exact fun h => safe mode name (List.mem_singleton.mp h)
  | primitive _ es => exact many_private resolve safe mode es
  | nominal _ es => exact many_private resolve safe .actual es
  | record _ a b | join a b =>
    intro h
    exact (List.mem_append.mp h).elim (reads_private resolve safe mode a) (reads_private resolve safe mode b)
  | variant _ a => exact reads_private resolve safe mode a
theorem many_private (resolve : Mode → Nat → Nat) (safe : ∀ mode name, t ≠ resolve mode name)
    (mode : Mode) (es : List Expr) : t ∉ readMany resolve mode es := by
  cases es with
  | nil => intro h; cases h
  | cons a rest =>
    intro h
    exact (List.mem_append.mp h).elim (reads_private resolve safe mode a) (many_private resolve safe mode rest)
end

theorem center_lookup (q : Plan roles) (safe : Safe q owner decl tag) (name : Nat) :
    port q.packet.context.state.seed owner decl tag ≠ (List.ofFn q.input.center)[name]?.getD 0 := by
  apply index_private _ _ ?_ (port_nonzero _ _ _ _) _
  intro present
  obtain ⟨i,same⟩ := List.mem_ofFn.mp present
  exact (safe.input i).2.2 same.symm

theorem body_private {q : Plan roles} (safe : Safe q owner decl tag) {target : Nat}
    (out : port q.packet.context.state.seed owner decl tag ≠ target) (body : Body) :
    port q.packet.context.state.seed owner decl tag ∉ bodySources q target body := by
  cases body with
  | explicit e =>
    intro member
    rcases List.mem_cons.mp member with direct | args
    · exact out direct
    · obtain ⟨var,_,same⟩ := List.mem_map.mp args
      rw [← binder_eq] at same
      exact binder_private safe.excludes var same.symm
  | default role name term =>
    intro member
    obtain ⟨eqn,compiled,parts⟩ := List.mem_flatMap.mp member
    cases found : compileBody q (.default role name term) with
    | none => simp [bodySchema,found] at compiled
    | some e =>
      change eqn ∈ (bodySchema q target (.default role name term)).equations at compiled
      simp only [bodySchema,found,List.mem_singleton] at compiled
      subst eqn
      rcases List.mem_cons.mp parts with same | read
      · exact out same
      · exact reads_private _ (fun _ index => center_lookup q safe index) .actual e read

theorem class_private {q : Plan roles} (safe : Safe q owner decl tag)
    (core : GeneralNominalCenteredSteps.State roles) (focus : GeneralSourceDictionaries.Occurrence roles)
    (targets : ∀ output ∈ GeneralNominalCenteredHeadOutputs.requests core focus,
      port q.packet.context.state.seed owner decl tag ≠ output.target) :
    port q.packet.context.state.seed owner decl tag ∉ classSources core focus q := by
  intro member
  obtain ⟨out,requested,part⟩ := List.mem_flatMap.mp member
  rcases List.mem_cons.mp part with direct|body
  · exact targets out requested direct
  · obtain ⟨template,_,found⟩ := List.mem_flatMap.mp body
    exact body_private safe (targets out requested) template found

end Yulang.GeneralRebasePrivateClass282
