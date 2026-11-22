import Yulang.GeneralDeclarativeAlternativeNamedHeads333

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAlternativeMixed333
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarationPatterns (Constructors Pattern normalize)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarativeAlternativeRange333 (Known materialize materialize_exact materialize_exists)
open GeneralDeclarativeAlternativeNamedHeads333 (materialSpans located_spans)
open GeneralDeclarativeAlternativeNeeds333 (Planned Eventually eventually_pair)
open GeneralDeclarativeAlternativeView333 (Index)
open GeneralDeclarativeAlternativeCapture333 (Captured transport_one)
open GeneralDeclarativeAlternativeRead333 (read)
open GeneralDeclarativeAlternativeReadComplete333 (read_plan)
open GeneralDeclarativeStableReads329 (Heads One)
open GeneralDeclarativeStableTrace329 (Located from_trace)
open GeneralDeclarativeGrowth327 (Extends trans fits)
open GeneralDeclarativeOpaqueConserve328 (Retains refl chain)
open GeneralDeclarativeObserverGrowth330 (preserve sources_grow)
open CommonRoleOutermostResolver (All₂)

/-- No coercion between the old trace and the newer inline read is
assumed. Each argument carries its actual independent source branch. -/
def Input (p : Supported s done) (c : Constructors) (i : Interpretation)
    (a : Capture) (pat : Pattern) : Prop :=
  Bounds s a ∧
    ((∃ code used, translate c i (normalize pat) = some code ∧
      GeneralDeclarativeTrace321.Trace (restriction p) .actual a.center code used) ∨
     (∃ code used, translate c i (normalize pat) = some code ∧
      GeneralDeclarativeInlineTrace331.Read (restriction p) .actual (.variable a.center) code used))

abbrev Inputs (p : Supported s done) (c : Constructors) (i : Interpretation) :=
  All₂ (Input p c i)

def argument (view : Known s) (src : Index source) (fuel : Nat) (c : Constructors) (i : Interpretation)
    (keep : List Nat) (current : State) (a : Capture) (pat : Pattern) : List Captured :=
  (GeneralDeclarativeAlternativeNamedHeads333.normalized src fuel c i .actual a.center pat).map
    (fun used => (current,materialSpans view used)) ++
  (match translate c i (normalize pat) with
   | none => []
   | some code => (read src fuel .actual (.variable a.center) code).filterMap fun seen =>
       materialize view current a keep code seen.val)

theorem located_grows {s t : State} (grown : Extends s t) (known : All₂ (Located s) used spans) :
    All₂ (Located t) used spans := by
  induction known with
  | nil => exact .nil
  | cons x _ ih => exact .cons ⟨x.1,x.2.1,fits grown x.2.2⟩ ih

theorem argument_sound {s t : State} {p : Supported s done}
    (view : Known s) (src : Index (restriction p)) (previous : Extends s t) (bounds : Bounds s a)
    (found : (after,spans) ∈ argument view src fuel c i keep t a pat) :
    Retains t after keep ∧ One after c i a pat spans ∧ ∀ a ∈ spans, Bounds after a.2 := by
  rcases List.mem_append.mp found with named|inline
  · obtain ⟨used,remembered,exact⟩ := List.mem_map.mp named
    cases exact
    obtain ⟨code,printed,seen⟩ := GeneralDeclarativeAlternativeNamedHeads333.read_sound remembered
    obtain ⟨head,kept⟩ := from_trace (p := preserve p previous) (fits previous bounds) printed
      (GeneralDeclarativeObserverGrowth330.trace (sources_grow p previous) seen)
      (located_grows previous (located_spans view used))
    exact ⟨refl _ _,head,kept⟩
  · cases printed : translate c i (normalize pat) with
    | none => rw [printed] at inline; cases inline
    | some code =>
      rw [printed] at inline
      obtain ⟨read,_,material⟩ := List.mem_filterMap.mp inline
      exact materialize_exact view previous (fits previous bounds) printed
        (GeneralDeclarativeInlineGrowth331.extend (sources_grow p previous) read.property) material

theorem argument_plan {s : State} {p : Supported s done}
    (view : Known s) (given : Input p c i a pat) (keep : List Nat) :
    Planned (fun src : Index (restriction p) =>
      Eventually (fun f => ∀ (t : State), Extends s t →
        ∃ result, result ∈ argument view src f c i keep t a pat)) := by
  rcases given with ⟨bounds,old|inline⟩
  · obtain ⟨code,used,printed,original⟩ := old
    apply (GeneralDeclarativeAlternativeNamedHeads333.read_plan printed original).map
    intro src there
    obtain ⟨depth,actual⟩ := there
    exact ⟨depth,fun f enough t _ => ⟨(t,materialSpans view used),List.mem_append_left _
      (List.mem_map.mpr ⟨used,actual f enough,rfl⟩)⟩⟩
  · obtain ⟨code,used,printed,original⟩ := inline
    apply (read_plan original).map
    intro src there
    obtain ⟨depth,actual⟩ := there
    refine ⟨depth,fun f enough t previous => ?_⟩
    obtain ⟨out,spans,comp⟩ := materialize_exists view (fits previous bounds) printed
      (GeneralDeclarativeInlineGrowth331.extend (sources_grow p previous) original)
    refine ⟨(out,spans),List.mem_append_right _ ?_⟩
    rw [printed]
    exact List.mem_filterMap.mpr ⟨⟨used,original⟩,actual f enough,comp⟩

def captureMixed (view : Known s) (src : Index source) (fuel : Nat) (c : Constructors)
    (i : Interpretation) (keep : List Nat) (current : State) : List Capture → List Pattern → List Captured
  | [],[] => [(current,[])]
  | a::as,p::ps => (argument view src fuel c i keep current a p).flatMap fun (middle,first) =>
      (captureMixed view src fuel c i keep middle as ps).map fun (after,rest) => (after,first++rest)
  | _,_ => []

theorem capture_sound {s t : State} {p : Supported s done}
    (view : Known s) (src : Index (restriction p)) (previous : Extends s t)
    (bounds : ∀ a ∈ xs, Bounds s a)
    (found : (out,spans) ∈ captureMixed view src depth c i keep t xs ps) :
    Retains t out keep ∧ Heads out c i xs ps spans ∧ ∀ a ∈ spans, Bounds out a.2 := by
  induction xs generalizing ps t out spans with
  | nil =>
    cases ps with
    | nil =>
      cases List.mem_singleton.mp found
      exact ⟨refl _ _,.nil,fun _ absent => False.elim (List.not_mem_nil absent)⟩
    | cons => cases found
  | cons a as ih =>
    cases ps with
    | nil => cases found
    | cons pat pats =>
      obtain ⟨⟨middle,first⟩,chosen,rest⟩ := List.mem_flatMap.mp found
      obtain ⟨⟨out,tail⟩,after,equal⟩ := List.mem_map.mp rest
      cases equal
      obtain ⟨kept,head,known⟩ := argument_sound view src previous (bounds a List.mem_cons_self) chosen
      obtain ⟨all,heads,fit⟩ := ih (trans previous kept.grows)
        (fun arg listed => bounds arg (List.mem_cons_of_mem _ listed)) after
      exact ⟨chain kept all,.cons (transport_one all.grows head) heads,
        fun use seen => (List.mem_append.mp seen).elim (fun h => fits all.grows (known _ h)) (fit _)⟩

theorem capture_plan {s : State} {p : Supported s done} (view : Known s)
    (actual : Inputs p c i xs ps) (keep : List Nat) :
    Planned (fun src : Index (restriction p) =>
      Eventually (fun f => ∀ (t : State), Extends s t →
        ∃ out, out ∈ captureMixed view src f c i keep t xs ps)) := by
  induction actual with
  | nil => exact Planned.pure fun _ => ⟨0,fun _ _ t _ => ⟨(t,[]),List.mem_cons_self⟩⟩
  | cons first _ ih =>
    apply ((argument_plan view first keep).both ih).map
    intro src planned
    obtain ⟨least,ready⟩ := eventually_pair planned.1 planned.2
    refine ⟨least,fun f enough t grows => ?_⟩
    obtain ⟨front,back⟩ := ready f enough
    obtain ⟨⟨middle,spans⟩,there⟩ := front t grows
    obtain ⟨kept,_,_⟩ := argument_sound view src grows first.1 there
    obtain ⟨⟨last,rest⟩,actual⟩ := back middle (trans grows kept.grows)
    exact ⟨(last,spans++rest),List.mem_flatMap.mpr
      ⟨(middle,spans),there,List.mem_map.mpr ⟨(last,rest),actual,rfl⟩⟩⟩

theorem input_bounds {s : State} {p : Supported s done} (observed : Inputs p c i xs ps) :
    ∀ a ∈ xs, Bounds s a := by
  induction observed with
  | nil => intro a absent; cases absent
  | cons read _ ih =>
    intro a placed
    rcases List.mem_cons.mp placed with rfl|later
    · exact read.1
    · exact ih _ later

end Yulang.GeneralDeclarativeAlternativeMixed333
