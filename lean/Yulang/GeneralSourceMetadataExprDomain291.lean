import Yulang.GeneralSourceMetadataApplication291

/-! The pure old output expression compiler succeeds exactly on its
declared explicit-pattern domain; no new type inference rule is added. -/
namespace Yulang.GeneralSourceMetadataExprDomain291
open GeneralNominalCenteredHeadMatExpressions (Expr application translate translateMany)
open GeneralNominalCenteredHeadWFSource (PatternCovered PatternsCovered)
open GeneralSourceMetadataApplication291 (application_sound)
open GeneralDeclarationPatterns (Constructors Pattern)
open GeneralNominalInspection (Interpretation)

theorem bind_success {α β : Type} {a : Option α} {f : α → Option β}
    {v : β} (h : a.bind f = some v) :
    ∃ x, a = some x ∧ f x = some v := by
  cases a with
  | none => cases h
  | some x => exact ⟨x,rfl,h⟩

theorem two_success {α β γ : Type} (a : Option α) (b : Option β) (f : α → β → γ)
    (v : γ) (h : (a.bind fun x => b.bind (fun y => some (f x y))) = some v) :
    ∃ x y, a = some x ∧ b = some y ∧ f x y = v := by
  obtain ⟨x,ax,tail⟩ := bind_success h
  cases b with
  | none => cases tail
  | some y => exact ⟨x,y,ax,rfl,Option.some.inj tail⟩

mutual
 theorem translate_sound (c : Constructors) (i : Interpretation) (p : Pattern)
    (v : Expr) (h : translate c i p = some v) : PatternCovered c i p := by
  cases p with
  | var name => trivial
  | app key ps =>
    have m : (translateMany c i ps).bind (application c i key) = some v := h
    obtain ⟨vs,decoded,applied⟩ := bind_success m
    obtain ⟨covered,arity⟩ := many_sound c i ps vs decoded
    have useCases := application_sound c i key vs v applied
    rw [arity] at useCases
    exact ⟨useCases,covered⟩
  | record tag a b =>
    obtain ⟨x,y,ax,by_,_⟩ := two_success (translate c i a) (translate c i b) (Expr.record tag) v h
    exact ⟨translate_sound c i a x ax,translate_sound c i b y by_⟩
  | variant tag a =>
    have statement : (translate c i a).bind (fun x => some (.variant tag x)) = some v := h
    obtain ⟨x,loaded,_⟩ := bind_success statement
    exact translate_sound c i a x loaded
  | join a b =>
    obtain ⟨x,y,ax,by_,_⟩ := two_success (translate c i a) (translate c i b) Expr.join v h
    exact ⟨translate_sound c i a x ax,translate_sound c i b y by_⟩

 theorem many_sound (c : Constructors) (i : Interpretation) (ps : List Pattern)
    (vs : List Expr) (h : translateMany c i ps = some vs) :
    PatternsCovered c i ps ∧ vs.length = ps.length := by
  cases ps with
  | nil =>
    have one : [] = vs := Option.some.inj h
    cases one
    exact ⟨trivial,rfl⟩
  | cons p ps =>
    obtain ⟨a,b,ax,bx,rfl⟩ := two_success (translate c i p) (translateMany c i ps) List.cons vs h
    obtain ⟨rest,size⟩ := many_sound c i ps b bx
    exact ⟨⟨translate_sound c i p a ax,rest⟩,congrArg Nat.succ size⟩
end

theorem compiler_domain (c : Constructors) (i : Interpretation) (p : Pattern) :
    (∃ v, translate c i p = some v) ↔ PatternCovered c i p :=
  ⟨fun ⟨v,h⟩ => translate_sound c i p v h,GeneralNominalCenteredHeadMatExpressions.translate_complete⟩

end Yulang.GeneralSourceMetadataExprDomain291
