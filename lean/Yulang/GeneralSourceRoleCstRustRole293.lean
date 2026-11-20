import Yulang.GeneralSourceRoleCstRustHead293

/-! Raw Rust-wrapper projection without modifying the original mixed-child
tree or its paths. An input is still a supplied snapshot, not Rust execution. -/
namespace Yulang.GeneralSourceRoleCstRustRole293
open GeneralSourceRoleCstTree293
open GeneralSourceRoleCstShapes293 (toHead)
open GeneralSourceRoleCstBody293
open GeneralSourceRoleCstProducer293 (roleParts)
open GeneralSourceRoleCstRustHead293 (readHead ActualHead head_exact_rust)
open GeneralSourceRoleTrack292 (Tracked)
open GeneralSourceRoleChildCoverage292 (Child)
open GeneralSourceRoleExport292 (Aligned)
open GeneralSourceMetadataExprDomain291 (bind_success)

def extract {Scope : Type} (scope : Scope) (site : Path) (t : Tree) :
    Option (Tracked Scope Path) :=
  (roleParts t).bind fun (head,j,body) =>
  (readHead head).bind fun (n,params) =>
  (members (site ++ [j]) body).map fun body => ⟨scope,toHead n params,site,body⟩

def Witness {Scope : Type} (scope : Scope) (site : Path) (t : Tree)
    (out : Tracked Scope Path) : Prop :=
  ∃ head j n ps cs,
    roleParts t = some (head,j,.node .indented cs) ∧ ActualHead head n ps ∧
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
      exact ⟨head,j,n,ps,cs,shell,(head_exact_rust ..).mp ordered,rfl,rfl,rfl,all⟩
  · rintro ⟨head,j,n,ps,cs,shell,ordered,scopeID,siteID,headID,all⟩
    unfold extract
    rw [shell,Option.bind_some]
    change (readHead head).bind (fun (n,params) =>
      (members (site ++ [j]) (.node .indented cs)).map fun body => ⟨scope,toHead n params,site,body⟩) = some out
    rw [(head_exact_rust ..).mpr ordered,Option.bind_some]
    rw [(members_exact ..).mpr ⟨cs,rfl,all⟩]
    cases out
    simp_all [eq_comm]

open GeneralSourceRoleCstPath293 (follow follow_append body_at_ordinal statement_at_last)

theorem extract_origin {Scope : Type} {scope : Scope} {site : Path} {whole role : Tree}
    {out : Tracked Scope Path} (selected : follow site whole = some role)
    (exported : extract scope site role = some out) (p : Path × Child) (member : p ∈ out.body) :
    ∃ raw, follow p.1 whole = some raw ∧ Classification raw p.2 := by
  obtain ⟨head,j,n,ps,cs,shape,ordered,sc,roleAt,headAt,all⟩ :=
    (extract_exact ..).mp exported
  obtain ⟨⟨idx,stmt⟩,located,classif⟩ := GeneralSourceRoleManifest292.aligned_right all member
  have located' : cs[idx]? = some stmt := (significant_exact.mp located).1
  have fromBody : follow [idx] (.node .indented cs) = some stmt := by
    simp [follow,located']
  obtain ⟨i,raw,place,rawRead,ca⟩ := statement_at_last classif
  change p.1 = site ++ [j] ++ [idx] ++ [i] at place
  refine ⟨raw,?_,ca⟩
  rw [place,follow_append,follow_append,follow_append,selected,Option.bind_some,body_at_ordinal shape,
    Option.bind_some,fromBody,Option.bind_some,rawRead]

end Yulang.GeneralSourceRoleCstRustRole293
