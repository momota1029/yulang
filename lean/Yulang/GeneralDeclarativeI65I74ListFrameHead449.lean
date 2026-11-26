import Yulang.GeneralDeclarativeI65I74ListSiteEntry449
import Yulang.GeneralSourceMetadataFiniteLookup291

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ListSites449.Frame
open Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open GeneralDeclarativeWitnessSparseIntervals357 (visited)
open CommonRecursiveNominalIntervals (Endpoint ContextWellFormed)
open CommonRoleOutermostResolver (All₂)
open List410 (listPoint410 invariantValue410)

inductive AuthoredFrame (s : GeneralDeclarativeI65.State) : List Capture → List Pattern → Type where
  | nil : AuthoredFrame s [] []
  | cons {a p args heads}
      (site : WrittenListSite s a p) (rest : AuthoredFrame s args heads) :
      AuthoredFrame s (a :: args) (p :: heads)

def AuthoredFrame.bindings {s : GeneralDeclarativeI65.State} {args heads} :
    AuthoredFrame s args heads → List (Nat × Nat)
  | .nil => []
  | .cons first tail => (first.binder,first.payload) :: tail.bindings

def AuthoredFrame.capture {s : GeneralDeclarativeI65.State} {args heads}
    (a : AuthoredFrame s args heads) (name : Nat) : Capture :=
  match GeneralSourceMetadataFiniteLookup291.get name a.bindings with
  | none => emptyCapture403
  | some payload => point payload

theorem frame_lookup_preserves_original_capture449 {s args heads}
    (a : AuthoredFrame s args heads) (distinct : (a.bindings.map Prod.fst).Nodup)
    {binder payload} (observed : (binder,payload) ∈ a.bindings) :
    a.capture binder = point payload := by
  unfold AuthoredFrame.capture
  rw [GeneralSourceMetadataFiniteLookup291.some_complete distinct observed]

theorem AuthoredFrame.visits {s args heads} (a : AuthoredFrame s args heads) :
    ListFrameVisits s args heads (args.map Capture.lower) := by
  induction a with
  | nil => exact .nil
  | cons first _ ih => exact .next first ih

def WrittenListSite.comparison {s arg head} (a : WrittenListSite s arg head) :
    DeclaredComparison s.current.environment s.current.ordinary s.modes false
      (listPoint410 a.key a.payload) (listPoint410 a.key a.payload) where
  actualSource := by
    intro site inHead
    have exact : site = (a.key,1) := by
      simpa [listPoint410,visited.eq_def,
        GeneralDeclarativeWitnessSparseIntervals357.visitedList.eq_def] using inHead
    subst site
    exact ⟨a.use,[invariantValue410],a.mode,a.table⟩
  left := .nominal a.table (.cons (.valuePoint (.ordinary true (.var a.payload))) (.nil false))
  right := .nominal a.table (.cons (.valuePoint (.ordinary true (.var a.payload))) (.nil false))
  compared := .nominal a.table (.cons (.invariantValue
    (.ordinary a.atom) (.ordinary a.atom) (.ordinary a.atom) (.ordinary a.atom)) .nil)

theorem written_list_reads_real_binder449 {s arg head}
    (a : WrittenListSite s arg head) (capture : Nat → Capture)
    (actual : capture a.binder = point a.payload) :
    DeepHead s capture arg head := by
  rw [a.headSyntax]
  let window : ModeWindow s arg (.app a.key [.var a.binder]) :=
    ⟨a.origin,a.origin,a.lower ▸ .direct,a.upper ▸ .direct,a.authored,a.authored,
      a.key,[.var a.binder],rfl,_,_,a.endpoint,a.endpoint,
      by rw [a.endpoint]; exact WrittenListSite.comparison a⟩
  let b := Binding.value a.binder (.var a.payload) (.var a.payload)
  refine .declared (found := [b,b]) window ?_
  change DeepRead s capture false (.app a.key [.var a.binder])
    a.origin.endpoint a.origin.endpoint [b,b]
  rw [a.endpoint]
  refine .nominal a.use a.mode a.table ?_
  let p : Endpoint Nat := .ordinary (.var a.payload)
  let span : CommonRecursiveNominalIntervals.Bounds (Endpoint Nat) := .point p
  have bind : ValueBind s (capture a.binder) (.var a.payload) (.var a.payload) := by
    rw [actual]
    exact ⟨a.atom,a.atom,a.atom,a.atom⟩
  have single : DeepRead s capture true (.var a.binder) p p [b] := .bind bind
  have doubled : DeepArgument s capture true invariantValue410 (.var a.binder)
      (.inl span) (.inl span) ([b] ++ [b]) :=
    .invariantValue (a := span) (b := span) single single
  have actualArguments : DeepArguments s capture false [invariantValue410] [.var a.binder]
      [.inl span] [.inl span] (([b] ++ [b]) ++ []) := .cons doubled .nil
  exact actualArguments

theorem frame_head_reads_are_actual449 {s args heads} (a : AuthoredFrame s args heads)
    (cap : Nat → Capture) (actual : ∀ b p, (b,p) ∈ a.bindings → cap b = point p) :
    All₂ (DeepHead s cap) args heads := by
  induction a with
  | nil => exact .nil
  | cons first rest ih =>
    exact .cons (written_list_reads_real_binder449 first cap
        (actual _ _ List.mem_cons_self))
      (ih (fun b p used => actual b p (List.mem_cons_of_mem _ used)))

theorem distinct_authored_bindings_have_exact_list_heads449 {s args heads}
    (a : AuthoredFrame s args heads) (distinct : (a.bindings.map Prod.fst).Nodup) :
    All₂ (DeepHead s a.capture) args heads :=
  frame_head_reads_are_actual449 a a.capture fun _ _ used =>
    frame_lookup_preserves_original_capture449 a distinct used

end Yulang.GeneralDeclarativeI65.I72.ListSites449.Frame
