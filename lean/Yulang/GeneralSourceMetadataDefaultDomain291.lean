import Yulang.GeneralSourceMetadataExprDomain291

/-! Exact success domain also for positional default terms. The term
language is not the explicit pattern language. -/
namespace Yulang.GeneralSourceMetadataDefaultDomain291
open GeneralNominalCenteredHeadMatExpressions (Expr application translateDefault translateDefaults)
open GeneralNominalCenteredHeadWFSource (TermCovered TermsCovered)
open GeneralSourceMetadataApplication291 (application_sound)
open GeneralSourceMetadataExprDomain291 (bind_success two_success)
open GeneralDeclarationPatterns (Constructors)
open GeneralNominalInspection (Interpretation)

mutual
 theorem default_sound (c : Constructors) (i : Interpretation) (p : Roles.Term)
    (v : Expr) (h : translateDefault c i p = some v) : TermCovered c i p := by
  cases p with
  | var name => trivial
  | app key ps =>
    have m : (translateDefaults c i ps).bind (application c i key) = some v := h
    obtain ⟨vs,decoded,applied⟩ := bind_success m
    obtain ⟨covered,arity⟩ := many_sound c i ps vs decoded
    have useCases := application_sound c i key vs v applied
    rw [arity] at useCases
    exact ⟨useCases,covered⟩

 theorem many_sound (c : Constructors) (i : Interpretation) (ps : List Roles.Term)
    (vs : List Expr) (h : translateDefaults c i ps = some vs) :
    TermsCovered c i ps ∧ vs.length = ps.length := by
  cases ps with
  | nil =>
    have one : [] = vs := Option.some.inj h
    cases one
    exact ⟨trivial,rfl⟩
  | cons p ps =>
    obtain ⟨a,b,ax,bx,rfl⟩ := two_success (translateDefault c i p) (translateDefaults c i ps) List.cons vs h
    obtain ⟨rest,size⟩ := many_sound c i ps b bx
    exact ⟨⟨default_sound c i p a ax,rest⟩,congrArg Nat.succ size⟩
end

theorem default_domain (c : Constructors) (i : Interpretation) (p : Roles.Term) :
    (∃ v, translateDefault c i p = some v) ↔ TermCovered c i p :=
  ⟨fun ⟨v,h⟩ => default_sound c i p v h,GeneralNominalCenteredHeadMatExpressions.translateDefault_complete⟩

end Yulang.GeneralSourceMetadataDefaultDomain291
