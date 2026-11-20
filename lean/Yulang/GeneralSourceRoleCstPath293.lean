import Yulang.GeneralSourceRoleCstProducer293

/-! Read back mixed-ordinal child paths from the same supplied CST. No
foreign parse, byte offset, or semantic declaration identity is inferred. -/
namespace Yulang.GeneralSourceRoleCstPath293
open GeneralSourceRoleCstTree293
open GeneralSourceRoleCstBody293
open GeneralSourceRoleCstProducer293
open GeneralSourceRoleChildCoverage292 (Child)
open GeneralSourceRoleTrack292 (Tracked)

def follow : Path → Tree → Option Tree
  | [],t => some t
  | i::tail,.node _ cs => cs[i]?.bind (follow tail)
  | _::_,.token _ _ => none

theorem follow_append (left right : Path) (root : Tree) :
    follow (left ++ right) root = (follow left root).bind (follow right) := by
  induction left generalizing root with
  | nil => rfl
  | cons i tail ih =>
    cases root with
    | token => rfl
    | node k cs =>
      cases h : cs[i]? with
      | none => simp [follow,h]
      | some child => simpa [follow,h] using ih child

theorem drop_subset {cs : List (Nat × Tree)} {p : Nat × Tree}
    (h : p ∈ dropVisibility cs) : p ∈ cs := by
  cases cs with
  | nil => cases h
  | cons a rest =>
    rcases a with ⟨i,el⟩
    cases el with
    | node k cs => exact h
    | token k text =>
      cases k <;> first
        | exact h
        | exact List.mem_cons_of_mem _ h

theorem body_at_ordinal {root : Tree} {head : Tree} {j : Nat} {body : Tree}
    (found : roleParts root = some (head,j,body)) : follow [j] root = some body := by
  cases root with
  | token => cases found
  | node kind cs =>
    cases kind <;> try cases found
    change (match dropVisibility (significant cs) with
      | [(_, .token .roleKw _), (_,head), (_, .token .colon _), body] => some (head,body)
      | _ => none) = some (head,j,body) at found
    generalize L : dropVisibility (significant cs) = xs at found
    split at found
    · rename_i _ _ _ _ _ _ _ payload
      have eq := Option.some.inj found
      have same : payload = (j,body) := congrArg Prod.snd eq
      have belongs : (j,body) ∈ dropVisibility (significant cs) := by
        rw [L,←same]
        simp
      have read := (significant_exact.mp (drop_subset belongs)).1
      simp [follow,read]
    · cases found

theorem statement_at_last {base : Path} {t : Tree} {result : Path × Child}
    (classified : IsStatement base t result) :
    ∃ i inner, result.1 = base ++ [i] ∧ follow [i] t = some inner ∧
      Classification inner result.2 := by
  obtain ⟨cs,i,inner,rfl,shape,whereAt,what⟩ := classified
  have member : (i,inner) ∈ significant cs := by rw [shape]; exact List.mem_cons_self
  have read := (significant_exact.mp member).1
  exact ⟨i,inner,whereAt,by simp [follow,read],what⟩

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

end Yulang.GeneralSourceRoleCstPath293
