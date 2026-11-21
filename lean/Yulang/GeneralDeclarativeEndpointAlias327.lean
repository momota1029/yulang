import Yulang.GeneralDeclarativeAliasProbe327
import Yulang.GeneralDeclarativeAliasVisit327

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEndpointAlias327
open GeneralDeclarations (Registry)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported restriction backed_iff)
open GeneralDeclarativeLowerKnown321 (Alias Ready Delayed knows_alias alias_symm alias_mono ready_iff_not_delayed)
open GeneralDeclarativePriority321 (Candidates Visible Survives RootRecurs CandidateRecurs Recurs Blocked)
open GeneralDeclarativeK2Alias321 (AliasCycle cycle_alias)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeAliasProbe327 (Ends replay)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open CommonRoleOutermostResolver (All₂)

theorem paired {relation : α → β → Prop} (data : All₂ relation as bs)
    (entry : a ∈ as) : ∃ b ∈ bs, relation a b := by
  induction data with
  | nil => cases entry
  | cons first later ih =>
    rcases List.mem_cons.mp entry with rfl|rest
    · exact ⟨_,List.mem_cons_self,first⟩
    · obtain ⟨b,there,tied⟩ := ih rest
      exact ⟨b,List.mem_cons_of_mem _ there,tied⟩

theorem indexed {relation : α → β → Prop} (data : All₂ relation as bs) (idx : Nat)
    (entry : as[idx]? = some a) : ∃ b, bs[idx]? = some b ∧ relation a b := by
  induction data generalizing idx with
  | nil => cases entry
  | cons first later ih =>
    cases idx with
    | zero => cases Option.some.inj entry; exact ⟨_,rfl,first⟩
    | succ idx => exact ih idx entry

theorem symm {s : State} (given : All₂ (Ends s) as bs) : All₂ (Ends s) bs as := by
  induction given with
  | nil => exact .nil
  | cons h _ ih => exact .cons ⟨alias_symm h.lower,alias_symm h.upper,h.otherBounds,h.bounds⟩ ih

theorem ordinary_alias {s : State} {p : Supported s done} (old : Alias (restriction p) a b) :
    Alias s a b := by
  apply alias_mono (s := restriction p) (t := s) rfl _ old
  intro e known
  obtain ⟨_,witness,_⟩ := (backed_iff p e).mp known
  exact p.ordinary witness

theorem enough {s : State} {p : Supported s done}
    (align : All₂ (Ends (restriction p)) a.arguments b.arguments) :
    Ready p a ↔ Ready p b := by
  have transport {x y : Demand} (pairs : All₂ (Ends (restriction p)) x.arguments y.arguments)
      (ready : Ready p y) : Ready p x := by
    intro ax existsHere
    obtain ⟨byName,found,link⟩ := paired pairs existsHere
    obtain ⟨tag,know⟩ := ready byName found
    exact ⟨tag,knows_alias link.lower know⟩
  exact ⟨transport (symm align),transport align⟩

theorem no_unauthorized_delay {s : State} {p : Supported s done}
    (align : All₂ (Ends (restriction p)) a.arguments b.arguments) :
    Delayed p a ↔ Delayed p b := by
  classical
  have one := (ready_iff_not_delayed p a).symm.trans ((enough align).trans (ready_iff_not_delayed p b))
  exact ⟨fun a => Classical.byContradiction fun b => (one.mpr b) a,
    fun b => Classical.byContradiction fun a => (one.mp a) b⟩

theorem roots {s : State} {p : Supported s done}
    (align : All₂ (Ends (restriction p)) a.arguments b.arguments) :
    RootRecurs s a ↔ RootRecurs s b := by
  have transport {x y : Demand} (pairs : All₂ (Ends (restriction p)) x.arguments y.arguments)
      (recurs : RootRecurs s x) : RootRecurs s y := by
    obtain ⟨spot,found,cycle⟩ := recurs
    obtain ⟨other,there,same⟩ := paired pairs found
    exact ⟨other,there,cycle_alias (alias_symm (ordinary_alias same.lower)) cycle⟩
  exact ⟨transport align,transport (symm align)⟩

theorem matches_for {s : State} {p : Supported s done} {r : Registry}
    (align : All₂ (Ends (restriction p)) a.arguments b.arguments) :
    HeadMatches (restriction p) r.constructors i a decl ↔ HeadMatches (restriction p) r.constructors i b decl :=
  replay align

theorem survives_for {s : State} {p : Supported s done} (r : Registry)
    (align : All₂ (Ends (restriction p)) a.arguments b.arguments) (sameRole : a.role = b.role)
    (positive : ∀ d decl, tests.viable d decl ↔ HeadMatches (restriction p) r.constructors i d decl) :
    Survives r tests a decl ↔ Survives r tests b decl := by
  exact and_congr (by simp only [Visible,sameRole]) ((positive a decl).trans ((matches_for align).trans (positive b decl).symm))

theorem candidates {s : State} {p : Supported s done} (r : Registry)
    (align : All₂ (Ends (restriction p)) a.arguments b.arguments) (sameRole : a.role = b.role)
    (positive : ∀ d decl, tests.viable d decl ↔ HeadMatches (restriction p) r.constructors i d decl) :
    CandidateRecurs s r i tests a ↔ CandidateRecurs s r i tests b := by
  have transport {x y : Demand} (pairs : All₂ (Ends (restriction p)) x.arguments y.arguments)
      (role : x.role = y.role) (old : CandidateRecurs s r i tests x) :
      CandidateRecurs s r i tests y := by
    obtain ⟨decl,survives,j,arg,pat,code,seen,hp,printed,cycle⟩ := old
    obtain ⟨other,also,same⟩ := indexed pairs j seen
    exact ⟨decl,(survives_for r pairs role positive).mp survives,j,other,pat,code,also,hp,printed,
      (GeneralDeclarativeAliasVisit327.pattern (ordinary_alias same.lower)).mp cycle⟩
  exact ⟨transport align sameRole,transport (symm align) sameRole.symm⟩

theorem recur_exact {s : State} {p : Supported s done} (r : Registry)
    (align : All₂ (Ends (restriction p)) a.arguments b.arguments) (sameRole : a.role = b.role)
    (positive : ∀ d decl, tests.viable d decl ↔ HeadMatches (restriction p) r.constructors i d decl) :
    Recurs s r i tests a ↔ Recurs s r i tests b :=
  or_congr (roots align) (candidates r align sameRole positive)

end Yulang.GeneralDeclarativeEndpointAlias327
