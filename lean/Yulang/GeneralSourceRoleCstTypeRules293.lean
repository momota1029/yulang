import Yulang.GeneralSourceRoleCstShapes293

/-! Declarative ordinary bare/default shapes for the adapter. A missing RHS
does not satisfy the bare rule just because it has no token spelling. -/
namespace Yulang.GeneralSourceRoleCstTypeRules293
open GeneralSourceRoleCstTree293
open GeneralSourceRoleCstShapes293
open GeneralSourceRoleSyntaxBoundary292 (Shape Rhs)

inductive IsRhs : Tree → Rhs → Prop
  | binder (cs : List Tree) (name : String) :
      visible cs = [.token .sigilIdentifier name] → IsRhs (.node .head cs) (.binder name)
  | named (cs : List Tree) (name : String) :
      visible cs = [.token .identifier name] → IsRhs (.node .head cs) (.nullary name)

theorem rhs_exact (t : Tree) (value : Rhs) :
    rhsView t = some value ↔ IsRhs t value := by
  constructor
  · intro h
    cases t with
    | token => cases h
    | node kind cs =>
      cases kind <;> try cases h
      cases shape : visible cs with
      | nil => simp [rhsView,shape] at h
      | cons x xs =>
        cases xs with
        | cons extra rest => cases x <;> simp [rhsView,shape] at h
        | nil =>
          cases x with
          | node => simp [rhsView,shape] at h
          | token k s =>
            cases k <;> simp [rhsView,shape] at h
            · subst value; exact .named cs s shape
            · subst value; exact .binder cs s shape
  · intro h
    cases h with
    | binder _ _ eq => simp [rhsView,eq]
    | named _ _ eq => simp [rhsView,eq]

inductive IsType : Tree → Shape → Prop
  | required (cs : List Tree) (word name : String) :
      visible cs = [.token .typeKw word,.token .identifier name] →
      IsType (.node .typeDecl cs) ⟨name,false,.absent,true⟩
  | defaulted (cs : List Tree) (word name equals : String) (body : Tree) (rhs : Rhs) :
      visible cs = [.token .typeKw word,.token .identifier name,.token .equals equals,body] →
      IsRhs body rhs →
      IsType (.node .typeDecl cs) ⟨name,true,rhs,true⟩

theorem type_exact (t : Tree) (out : Shape) :
    typeView t = some out ↔ IsType t out := by
  constructor
  · intro h
    cases t with
    | token => cases h
    | node k cs =>
      cases k <;> try cases h
      change (match visible cs with
        | [.token .typeKw _, .token .identifier n] => some ⟨n,false,.absent,true⟩
        | [.token .typeKw _, .token .identifier n,.token .equals _,rhs] =>
          (rhsView rhs).map (fun b => ⟨n,true,b,true⟩)
        | _ => none) = some out at h
      generalize shape : visible cs = elems at h
      split at h
      · rename_i _ word name
        cases Option.some.inj h
        exact .required cs word name shape
      · rename_i _ word name eq ready
        cases b : rhsView ready with
        | none => simp [b] at h
        | some rhs =>
          have e : (⟨name,true,rhs,true⟩ : Shape) = out := by simpa [b] using h
          subst out
          exact .defaulted cs word name eq ready rhs shape ((rhs_exact ..).mp b)
      · cases h
  · intro h
    cases h with
    | required cs w n shape => simp [typeView,shape]
    | defaulted cs w n eq raw rhs shape plain =>
      simp [typeView,shape,(rhs_exact ..).mpr plain]

theorem rhs_always_explicit (t : Tree) (r : Rhs) (valid : IsRhs t r) : r ≠ .absent := by
  intro same
  cases valid <;> cases same

theorem shape_never_fakes_required_after_equals {t : Tree} {out : Shape}
    (done : typeView t = some out) (equals : out.equalsToken = true) : out.rhs ≠ .absent := by
  cases (type_exact ..).mp done with
  | required => cases equals
  | defaulted _ _ _ _ raw rhs _ direct => exact rhs_always_explicit raw rhs direct

end Yulang.GeneralSourceRoleCstTypeRules293
