import Yulang.GeneralSourceRoleCstJsonFixture293

/-! The direct-child producer is both sound and complete for its allowed
surface. On success every significant direct statement is represented once
at a distinct mixed ordinal, including non-type bindings. -/
namespace Yulang.GeneralSourceRoleCstCoverage293
open GeneralSourceRoleCstTree293
open GeneralSourceRoleCstBody293 (IsStatement statement statement_exact members members_exact)
open GeneralSourceRoleCstProducer293 (extract extract_exact roleParts)
open GeneralSourceRoleExport292 (Aligned)
open GeneralSourceRoleManifest292 (aligned_left aligned_right)
open GeneralSourceRoleTrack292 (Tracked)
open GeneralSourceRoleChildCoverage292 (Child)

theorem direct_complete (base : Path) (children : List Tree) (xs : List (Path × Child))
    (valid : Aligned (fun p => IsStatement (base ++ [p.1]) p.2) (significant children) xs)
    (p : Path × Child) :
    p ∈ xs ↔ ∃ index raw, children[index]? = some raw ∧ trivia raw = false ∧
      IsStatement (base ++ [index]) raw p := by
  constructor
  · intro member
    obtain ⟨⟨i,exactTree⟩,located,link⟩ := aligned_right valid member
    have read := significant_exact.mp located
    exact ⟨i,exactTree,read.1,read.2,link⟩
  · rintro ⟨i,raw,chosen,clean,classified⟩
    obtain ⟨next,seen,property⟩ := aligned_left valid
      (significant_exact.mpr ⟨chosen,clean⟩)
    have same : next = p := Option.some.inj
      (((statement_exact ..).mpr property).symm.trans ((statement_exact ..).mpr classified))
    exact same ▸ seen

theorem extract_direct_exact {Scope : Type} (scope : Scope) (s : Path) (t : Tree)
    (out : Tracked Scope Path) (ok : extract scope s t = some out)
    (head : Tree) (atBody : Nat) (children : List Tree)
    (selection : roleParts t = some (head,atBody,.node .indented children))
    (p : Path × Child) :
    p ∈ out.body ↔ ∃ i raw, children[i]? = some raw ∧ trivia raw = false ∧
      IsStatement (s ++ [atBody] ++ [i]) raw p := by
  obtain ⟨h,j,n,ps,cs,pick,headOK,scopeOK,siteOK,shapeOK,mapped⟩ := (extract_exact ..).mp ok
  have e := Option.some.inj (pick.symm.trans selection)
  have e₁ : j = atBody := congrArg (fun x => x.2.1) e
  have e₂ : cs = children := Tree.node.inj (congrArg (fun x => x.2.2) e) |>.2
  subst atBody
  subst children
  exact direct_complete _ _ _ mapped p

theorem cover_path_length {Scope : Type} (scope : Scope) (s : Path) (t : Tree)
    (out : Tracked Scope Path) (ok : extract scope s t = some out)
    (p : Path × Child) (inBody : p ∈ out.body) : p.1.length = s.length + 3 := by
  obtain ⟨h,j,n,ps,cs,pick,headOK,scopeOK,siteOK,shapeOK,mapped⟩ := (extract_exact ..).mp ok
  obtain ⟨i,raw,loc,clean,stmt⟩ := (extract_direct_exact scope s t out ok h j cs pick p).mp inBody
  obtain ⟨stmtChildren,k,inner,stmtShape,innerPicked,handle,kind⟩ := stmt
  simp only [handle,List.length_append,List.length_cons,List.length_nil]

end Yulang.GeneralSourceRoleCstCoverage293
