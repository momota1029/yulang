import Yulang.GeneralObservedMetadataBranch290

/-! The actual centered output-expression compiler is not the recursive
head-query translator: it preserves joins and arbitrary record tails. -/
namespace Yulang.GeneralObservedMetadataExpressions290
open GeneralDeclarationPatterns (Constructors Pattern)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadMatExpressions (Expr application translate translateMany translateDefault translateDefaults)
open GeneralObservedMetadataKeys290 (keys keysMany app_self)
open GeneralObservedMetadataEntry290 (LocalEqual EntryEqual)

theorem apply_eq {c d : Constructors} {i j : Interpretation} {name : Nat}
    (agree : EntryEqual c i d j name) :
    application c i name = application d j name := by
  funext args
  unfold application
  rw [agree.1,agree.2.1,agree.2.2]

mutual
 theorem explicit_eq (c : Constructors) (i : Interpretation) (d : Constructors) (j : Interpretation)
    (p : Pattern) (h : LocalEqual (keys p) c i d j) : translate c i p = translate d j p := by
  cases p with
  | var name => rfl
  | app name args =>
    have kids := explicits_eq c i d j args (h.restrict (fun _ k => List.mem_cons_of_mem _ k))
    have head := apply_eq (h name (app_self name args))
    simp only [translate,kids,head]
  | record label payload tail =>
    have payloadEq := explicit_eq c i d j payload (h.restrict (fun _ k => List.mem_append_left _ k))
    have tailEq := explicit_eq c i d j tail (h.restrict (fun _ k => List.mem_append_right _ k))
    simp only [translate,payloadEq,tailEq]
  | variant tag payload =>
    simp only [translate,explicit_eq c i d j payload h]
  | join a b =>
    have aEq := explicit_eq c i d j a (h.restrict (fun _ k => List.mem_append_left _ k))
    have bEq := explicit_eq c i d j b (h.restrict (fun _ k => List.mem_append_right _ k))
    simp only [translate,aEq,bEq]

 theorem explicits_eq (c : Constructors) (i : Interpretation) (d : Constructors) (j : Interpretation)
    (ps : List Pattern) (h : LocalEqual (keysMany ps) c i d j) :
    translateMany c i ps = translateMany d j ps := by
  cases ps with
  | nil => rfl
  | cons p ps =>
    have first := explicit_eq c i d j p (h.restrict (fun _ k => List.mem_append_left _ k))
    have rest := explicits_eq c i d j ps (h.restrict (fun _ k => List.mem_append_right _ k))
    simp only [translateMany,first,rest]
end

mutual
 def termKeys : Roles.Term → List Nat
  | .var _ => []
  | .app key args => key :: termsKeys args
 def termsKeys : List Roles.Term → List Nat
  | [] => []
  | p :: ps => termKeys p ++ termsKeys ps
end

mutual
 theorem default_eq (c : Constructors) (i : Interpretation) (d : Constructors) (j : Interpretation)
    (p : Roles.Term) (h : LocalEqual (termKeys p) c i d j) : translateDefault c i p = translateDefault d j p := by
  cases p with
  | var _ => rfl
  | app name args =>
    have kids := defaults_eq c i d j args (h.restrict (fun _ k => List.mem_cons_of_mem _ k))
    have head := apply_eq (h name (List.mem_cons_self ..))
    simp only [translateDefault,kids,head]

 theorem defaults_eq (c : Constructors) (i : Interpretation) (d : Constructors) (j : Interpretation)
    (ps : List Roles.Term) (h : LocalEqual (termsKeys ps) c i d j) :
    translateDefaults c i ps = translateDefaults d j ps := by
  cases ps with
  | nil => rfl
  | cons p ps =>
    have first := default_eq c i d j p (h.restrict (fun _ k => List.mem_append_left _ k))
    have rest := defaults_eq c i d j ps (h.restrict (fun _ k => List.mem_append_right _ k))
    simp only [translateDefaults,first,rest]
end

end Yulang.GeneralObservedMetadataExpressions290
