import Yulang.GeneralSourceRoleCstSymbolicChildren295

namespace Yulang.GeneralSourceRoleCstSymbolicTotal295
open GeneralSourceRoleTrack292 (Tracked forget)
open GeneralSourceRoleHeadShape292 (HeadShape Argument)
open GeneralSourceRoleCstShapes293 (toHead)
open GeneralSourceRoleCstSymbolicChildren295 (Compatible classified_compatible collect_compatible)
open GeneralSourceRoleScopedShell292 (Packet project project_exact)
open GeneralSourceRoleScopedExport292 (ScopedRole)
open GeneralSourceRoleHeadPacketRun292 (makePacket make_exact)
open GeneralSourceRoleCstNamingScope295 (symbolic)
open GeneralSourceRoleCstSelectedSeal295 (Selection select)
open GeneralSourceRoleCstSelectedMembers295 (selected_member_is_exact_original)
open GeneralSourceRoleCstHeadOrigin295 (selected_head_from_original)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstSelectedCompile295 (Boundary handoff handoff_exact)
open GeneralSourceRoleExport292 (Aligned)
open GeneralSourceRoleChildCoverage292 (Child)

theorem generated_head (n : String) (ps : List String) : HeadShape (toHead n ps) n ps := by
  refine ⟨rfl,rfl,?_⟩
  change Aligned (fun a s => a = .binder s) (ps.map Argument.binder) ps
  induction ps with
  | nil => exact .nil
  | cons s ps ih => exact .cons rfl ih

theorem compatible_to_symbolic {S H : Type} (p : Tracked S H) (n : String) (ps : List String)
    (head : HeadShape p.head n ps) (good : ∀ c ∈ p.body.map Prod.snd, Compatible c) :
    ∃ out, symbolic p = some out ∧ out.scope = p.scope ∧ out.role.spelling = n ∧
      out.role.binders = ps := by
  obtain ⟨shape,lowered,scan,related⟩ := collect_compatible _ good
  let packet : Packet S := ⟨p.scope,⟨n,ps,p.body.map Prod.snd⟩⟩
  let output : ScopedRole S := ⟨p.scope,⟨n,ps,lowered⟩⟩
  have ready : makePacket (forget p) = some packet := (make_exact ..).mpr ⟨rfl,rfl,head⟩
  have exported : project packet = some output := (project_exact ..).mpr
    ⟨rfl,⟨⟨n,ps,shape⟩,⟨rfl,rfl,scan⟩,rfl,rfl,related⟩⟩
  refine ⟨output,?_,rfl,rfl,rfl⟩
  simp [symbolic,ready,exported]

theorem selected_goes_symbolic {S B : Type} [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B) (chosen : Selection B)
    (p : Tracked S (Address B)) (produced : select policy scope w brand a chosen = some p) :
    ∃ out, symbolic p = some out ∧ out.scope = scope := by
  obtain ⟨tag,_,_,_,n,ps,_,_,_,head⟩ :=
    selected_head_from_original policy scope w brand a chosen p produced
  have allGood : ∀ c ∈ p.body.map Prod.snd, Compatible c := by
    intro c h
    obtain ⟨item,found,same⟩ := List.mem_map.mp h
    obtain ⟨_,_,t,raw,_,_,known⟩ :=
      selected_member_is_exact_original policy scope w brand a chosen p produced item found
    exact same ▸ classified_compatible known
  have shaped : HeadShape p.head n ps := by rw [head]; exact generated_head n ps
  obtain ⟨out,parsed,outScope,_,_⟩ := compatible_to_symbolic p n ps shaped allGood
  exact ⟨out,parsed,outScope.trans tag⟩

theorem handoff_goes_symbolic {S B : Type} [DecidableEq S] [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B) (sealed : Boundary S B)
    (p : Tracked S (Address B)) (produced : handoff policy scope w brand a sealed = some p) :
    ∃ out, symbolic p = some out ∧ out.scope = scope :=
  selected_goes_symbolic policy scope w brand a sealed.selected p ((handoff_exact ..).mp produced).2

end Yulang.GeneralSourceRoleCstSymbolicTotal295
