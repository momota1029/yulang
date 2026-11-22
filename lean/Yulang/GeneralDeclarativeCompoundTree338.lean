import Yulang.GeneralDeclarativeCompoundRoutes338

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCompoundTree338
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeGrowth327 (Extends fits trans)
open GeneralDeclarativeClauseBatch327 (reflexive)
open GeneralDeclarativeFootprint321 (stateNames atomSources equationNames)
open GeneralDeclarativeEndpointOverlay336 (Entry)
open GeneralDeclarativeEndpointConserve336 (names refs)
open GeneralDeclarativeExactOverlay337 (ModelsExact)
open GeneralDeclarativeCompoundPattern338 (peel variables variables_peel)
open GeneralDeclarativeCompoundBatch338 (Ticket minted after afterSupport grows_after conserves)
open GeneralDeclarativeCompoundRoutes338 (dispatch dispatch_exact)
open GeneralNominalCommonBridge (Assignment)

abbrev Span := Nat × Capture

structure World (done : Nat → Prop) where
  state : State
  source : Supported state done
  reads : List Entry

def advance {done : Nat → Prop} (w : World done) {a} {f} (t : Ticket w.source a f)
    (keep : List Nat) : World done :=
  ⟨after w.state w.reads keep t.jobs,afterSupport w.source w.reads keep t.jobs,
    w.reads ++ minted w.state w.reads keep t.jobs⟩

def fitsModel (w : World done) (m : Assignment) : Prop := ModelsExact w.state w.reads m

def footprint (w : World done) (keep : List Nat) : List Nat :=
  stateNames w.state ++ (names w.reads ++ keep)

def World.Grows (w v : World done) : Prop :=
  Extends w.state v.state ∧ w.reads ⊆ v.reads ∧ Extends (restriction w.source) (restriction v.source)

theorem state_scope {s t : State} (h : Extends s t) : stateNames s ⊆ stateNames t := by
  intro n used
  simp only [stateNames,List.mem_append] at used ⊢
  rcases used with (a|b)|c
  · obtain ⟨x,present,written⟩ := List.mem_flatMap.mp a
    exact .inl (.inl (List.mem_flatMap.mpr ⟨x,h.constraints present,written⟩))
  · obtain ⟨x,present,written⟩ := List.mem_flatMap.mp b
    exact .inl (.inr (List.mem_flatMap.mpr ⟨x,h.intervals present,written⟩))
  · obtain ⟨x,present,written⟩ := List.mem_flatMap.mp c
    exact .inr (List.mem_flatMap.mpr ⟨x,h.equations present,written⟩)

theorem scope {w v : World done} (h : w.Grows v) : footprint w keep ⊆ footprint v keep := by
  intro n used
  rcases List.mem_append.mp used with one|two
  · exact List.mem_append_left _ (state_scope h.1 one)
  · apply List.mem_append_right
    rcases List.mem_append.mp two with old|stay
    · obtain ⟨e,listed,uses⟩ := List.mem_flatMap.mp old
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨e,h.2.1 listed,uses⟩)
    · exact List.mem_append_right _ stay

theorem together {w v z : World done} (a : w.Grows v) (b : v.Grows z) : w.Grows z :=
  ⟨trans a.1 b.1,fun _ h => b.2.1 (a.2.1 h),trans a.2.2 b.2.2⟩

theorem advance_grows {w : World done} (t : Ticket w.source a f) (keep) : w.Grows (advance w t keep) :=
  ⟨grows_after _ _ _ _,fun _ h => List.mem_append_left _ h,
    GeneralDeclarativeGrowth327.trans (GeneralDeclarativeObserverGrowth330.sources_grow w.source
      (GeneralDeclarativeEndpointBatch336.grows _ _ _))
      ⟨fun _ h => h,fun _ h => h,GeneralDeclarativeCompoundEndpoints338.old_backed _⟩⟩

mutual
/-- An actual finite endpoint read traverses the normalized pattern.
The traversal consumes computed source-aligned field receipts. Every
binder takes the real incoming triple; no whole-center RHS is tested. -/
inductive Tree {done : Nat → Prop} (keep : List Nat) : World done → Capture → Pattern → World done → List Span → Prop where
  | binder : Bounds w.state arg → Tree keep w arg (.var n) w [(n,arg)]
  | record {w : World done} (t : Ticket w.source arg fs) :
      fs ≠ [] → peel pat = (fs,endPat) →
      dispatch fs (minted w.state w.reads keep t.jobs) = some (kids,residual) →
      Forest keep (advance w t keep) kids between bodyUses →
      Tree keep between residual.2 endPat final tailUses →
      Tree keep w arg pat final (bodyUses ++ tailUses)

inductive Forest {done : Nat → Prop} (keep : List Nat) : World done → List (Entry × Pattern) → World done → List Span → Prop where
  | nil : Forest keep w [] w []
  | cons : Tree keep w one.1.2 one.2 between here →
      Forest keep between more final later →
      Forest keep w (one::more) final (here++later)
end

def Sound (keep : List Nat) (w v : World done) : Prop :=
  w.Grows v ∧ ∀ m, fitsModel w m → ∃ n, fitsModel v n ∧ ∀ x ∈ footprint w keep, n x = m x

theorem identity (w : World done) (keep) : Sound keep w w :=
  ⟨⟨reflexive _,fun _ h => h,reflexive _⟩,fun m fit => ⟨m,fit,fun _ _ => rfl⟩⟩

theorem chain {w v z : World done} (a : Sound keep w v) (b : Sound keep v z) : Sound keep w z := by
  refine ⟨together a.1 b.1,?_⟩
  intro m fit
  obtain ⟨n,good,kept⟩ := a.2 m fit
  obtain ⟨p,valid,unchanged⟩ := b.2 n good
  exact ⟨p,valid,fun x h => (unchanged x (scope a.1 h)).trans (kept x h)⟩

theorem stage {w : World done} (t : Ticket w.source a f) : Sound keep w (advance w t keep) :=
  ⟨advance_grows t keep,fun m fit => conserves t m fit keep⟩

def ForestVariables (ts : List (Entry × Pattern)) : List Nat :=
  ts.flatMap (fun e => e.2.variables)

theorem routed_variables {fs} {ts : List (Entry × Pattern)} (names : ts.map Prod.snd = fs.map Prod.snd) :
    ForestVariables ts = variables fs := by
  have changed := congrArg (List.flatMap Pattern.variables) names
  simpa [ForestVariables,variables,List.flatMap_map,Function.comp_def] using changed

def TreeExact (keep : List Nat) (w : World done) (p : Pattern) (v : World done) (uses : List Span) : Prop :=
  Sound keep w v ∧ uses.map Prod.fst = p.variables ∧ ∀ u ∈ uses, Bounds v.state u.2

def ForestExact (keep : List Nat) (w : World done) (ts : List (Entry × Pattern))
    (v : World done) (uses : List Span) : Prop :=
  Sound keep w v ∧ uses.map Prod.fst = ForestVariables ts ∧ ∀ u ∈ uses, Bounds v.state u.2

theorem combine_record {w between final : World done} (ticket : Ticket w.source arg fs)
    (split : peel pat = (fs,endPat))
    (dispatched : dispatch fs (minted w.state w.reads keep ticket.jobs) = some (kids,residual))
    (inFields : ForestExact keep (advance w ticket keep) kids between bodyUses)
    (inTail : TreeExact keep between endPat final tailUses) :
    TreeExact keep w pat final (bodyUses ++ tailUses) := by
  obtain ⟨fSound,fOrder,fBound⟩ := inFields
  obtain ⟨tSound,tOrder,tBound⟩ := inTail
  have shape := variables_peel pat
  rw [split] at shape
  have routed := routed_variables (dispatch_exact dispatched).1
  refine ⟨chain (stage ticket) (chain fSound tSound),?_,?_⟩
  · rw [List.map_append,fOrder,tOrder,routed,shape]
  · intro u seen
    rcases List.mem_append.mp seen with front|last
    · exact fits tSound.1.1 (fBound u front)
    · exact tBound u last

theorem combine_fields {w between final : World done}
    (a : TreeExact keep w one.2 between here) (b : ForestExact keep between more final later) :
    ForestExact keep w (one::more) final (here++later) := by
  obtain ⟨asound,orderA,boundsA⟩ := a
  obtain ⟨bsound,orderB,boundsB⟩ := b
  refine ⟨chain asound bsound,by simp [ForestVariables,orderA,orderB],?_⟩
  intro u seen
  rcases List.mem_append.mp seen with h|h
  · exact fits bsound.1.1 (boundsA u h)
  · exact boundsB u h

theorem tree_exact (observed : Tree keep w a p v uses) : TreeExact keep w p v uses := by
  refine Tree.rec (motive_1 := fun w _ p v uses _ => TreeExact keep w p v uses)
    (motive_2 := fun w ts v uses _ => ForestExact keep w ts v uses) ?_ ?_ ?_ ?_ observed
  · intros
    rename_i fit
    exact ⟨identity _ _,rfl,fun _ found => by cases List.mem_singleton.mp found; exact fit⟩
  · intros
    apply combine_record <;> assumption
  · intros
    exact ⟨identity _ _,rfl,fun _ h => False.elim (List.not_mem_nil h)⟩
  · intros
    apply combine_fields <;> assumption

theorem forest_exact (observed : Forest keep w ts v uses) : ForestExact keep w ts v uses := by
  refine Forest.rec (motive_1 := fun w _ p v uses _ => TreeExact keep w p v uses)
    (motive_2 := fun w ts v uses _ => ForestExact keep w ts v uses) ?_ ?_ ?_ ?_ observed
  · intros
    rename_i fit
    exact ⟨identity _ _,rfl,fun _ found => by cases List.mem_singleton.mp found; exact fit⟩
  · intros
    apply combine_record <;> assumption
  · intros
    exact ⟨identity _ _,rfl,fun _ h => False.elim (List.not_mem_nil h)⟩
  · intros
    apply combine_fields <;> assumption

end Yulang.GeneralDeclarativeCompoundTree338
