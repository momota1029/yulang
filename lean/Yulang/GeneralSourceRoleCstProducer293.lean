import Yulang.GeneralSourceRoleCstBody293

/-! A verified unresolved producer on the supplied tree; no symbol table, scope
resolution, or Rust serialization is hidden in the producer. -/
namespace Yulang.GeneralSourceRoleCstProducer293
open GeneralSourceRoleCstTree293
open GeneralSourceRoleCstShapes293
open GeneralSourceRoleCstBody293
open GeneralSourceRoleTrack292 (Tracked)
open GeneralSourceRoleChildCoverage292 (Child)
open GeneralSourceRoleExport292 (Aligned)
open GeneralSourceMetadataExprDomain291 (bind_success)

def dropVisibility : List (Nat × Tree) → List (Nat × Tree)
  | (_, .token .myKw _) :: rest
  | (_, .token .ourKw _) :: rest
  | (_, .token .pubKw _) :: rest => rest
  | rest => rest

def roleParts (t : Tree) : Option (Tree × (Nat × Tree)) :=
  match t with
  | .node .role cs =>
    match dropVisibility (significant cs) with
    | [(_, .token .roleKw _), (_,head), (_, .token .colon _), body] => some (head,body)
    | _ => none
  | _ => none

def extract {Scope : Type} (scope : Scope) (site : Path) (t : Tree) :
    Option (Tracked Scope Path) :=
  (roleParts t).bind fun (head,j,body) =>
  (headView head).bind fun (n,params) =>
  (members (site ++ [j]) body).map fun body => ⟨scope,toHead n params,site,body⟩

def Witness {Scope : Type} (scope : Scope) (site : Path) (t : Tree)
    (out : Tracked Scope Path) : Prop :=
  ∃ head j n ps cs,
    roleParts t = some (head,j,.node .indented cs) ∧ HasHead head n ps ∧
    out.scope = scope ∧ out.atRole = site ∧ out.head = toHead n ps ∧
    Aligned (fun p => IsStatement (site ++ [j] ++ [p.1]) p.2) (significant cs) out.body

theorem extract_exact {Scope : Type} (scope : Scope) (site : Path) (t : Tree)
    (out : Tracked Scope Path) : extract scope site t = some out ↔ Witness scope site t out := by
  constructor
  · intro ok
    obtain ⟨⟨head,j,body⟩,shell,c⟩ := bind_success ok
    obtain ⟨⟨n,ps⟩,ordered,produced⟩ := bind_success c
    cases r : members (site ++ [j]) body with
    | none => simp [r] at produced
    | some elems =>
      have eq : (⟨scope,toHead n ps,site,elems⟩ : Tracked Scope Path) = out := by
        simpa [r] using produced
      subst out
      obtain ⟨cs,rfl,all⟩ := (members_exact ..).mp r
      exact ⟨head,j,n,ps,cs,shell,(head_exact ..).mp ordered,rfl,rfl,rfl,all⟩
  · rintro ⟨head,j,n,ps,cs,shell,ordered,scopeID,siteID,headID,all⟩
    unfold extract
    rw [shell,Option.bind_some]
    change (headView head).bind (fun (n,params) =>
      (members (site ++ [j]) (.node .indented cs)).map fun body => ⟨scope,toHead n params,site,body⟩) = some out
    rw [(head_exact ..).mpr ordered,Option.bind_some]
    rw [(members_exact ..).mpr ⟨cs,rfl,all⟩]
    cases out
    simp_all [eq_comm]

end Yulang.GeneralSourceRoleCstProducer293
