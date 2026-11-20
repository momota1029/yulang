import Yulang.GeneralSourceRoleCstSelectedEnd295

/-! Once a wrapped selection succeeds, its observed children satisfy the
existing symbolic rules. This is not a theorem about arbitrary Tracked data. -/
namespace Yulang.GeneralSourceRoleCstSymbolicChildren295
open GeneralSourceRoleCstTree293 (Tree)
open GeneralSourceRoleCstTypeRules293 (IsType IsRhs type_exact)
open GeneralSourceRoleCstBody293 (Classification)
open GeneralSourceRoleSyntaxBoundary292 (Shape Admitted Owner)
open GeneralSourceRoleChildCoverage292 (Child Collects)
open GeneralSourceRoleExport292 (Aligned)
open GeneralSourceRoleSpelling292 (Output)

def Compatible : Child → Prop
  | .other => True
  | .unknown => False
  | .typeDecl sh => ∃ out, Admitted .roleBodyDirect sh out

theorem type_admitted {t : Tree} {sh : Shape} (ok : IsType t sh) :
    ∃ o, Admitted .roleBodyDirect sh o := by
  cases ok with
  | required cs word name good => exact ⟨_,.required name⟩
  | defaulted cs word name eq b rhs good provided =>
    cases provided with
    | binder cs spelling h => exact ⟨_,.binder name spelling⟩
    | named cs spelling h => exact ⟨_,.nullary name spelling⟩

theorem classified_compatible {t : Tree} {c : Child} (ok : Classification t c) : Compatible c := by
  cases ok with
  | binding => trivial
  | associated cs sh found => exact type_admitted ((type_exact ..).mp found)

theorem collect_compatible (children : List Child)
    (ok : ∀ c ∈ children, Compatible c) :
    ∃ shapes outputs, Collects children shapes ∧
      Aligned (Admitted .roleBodyDirect) shapes outputs := by
  induction children with
  | nil => exact ⟨[],[],.nil,.nil⟩
  | cons c cs ih =>
    obtain ⟨tail,outs,scanned,lowered⟩ := ih (fun x m => ok x (List.mem_cons_of_mem _ m))
    have here := ok c List.mem_cons_self
    cases c with
    | other => exact ⟨tail,outs,.other scanned,lowered⟩
    | unknown => exact False.elim here
    | typeDecl sh =>
      obtain ⟨o,accepted⟩ := here
      exact ⟨sh::tail,o::outs,.typeDecl scanned,.cons accepted lowered⟩

end Yulang.GeneralSourceRoleCstSymbolicChildren295
