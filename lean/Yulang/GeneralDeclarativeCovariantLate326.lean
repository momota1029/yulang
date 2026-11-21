import Yulang.GeneralDeclarativeCovariantSupport326

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCovariantLate326
open GeneralDeclarativePairDecl326
open GeneralDeclarativeCovariantState326
open GeneralDeclarativeCovariantProbe326 (no_cycles)
open GeneralDeclarativeCovariantFrame326
open GeneralDeclarativeCovariantResolve326 (root_only child_only dict declared)
open GeneralDeclarativeCovariantSupport326
open GeneralDeclarativeProjectedFrame326 (Frame Rule readback sound)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeLowerKnown321 (Ready knows_row ready_iff_not_delayed)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativePriority321 (Candidates Recurs)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarationExamples (constructors)
open GeneralDeclarativeHead320 (Models Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeEvidence320 (Evidence)
open CommonRoleOutermostResolver (Classify)

def tests (done : Nat → Prop) : Candidates :=
  ⟨HeadMatches (restriction (controlled done)) constructors interpret,
   fun d impl => ¬ HeadMatches (restriction (controlled done)) constructors interpret d impl⟩

abbrev branch (done : Nat → Prop) := Rule final reg interpret (controlled done) (tests done)

theorem no_recurs (done : Nat → Prop) (d : Demand) : ¬Recurs final reg interpret (tests done) d := by
  rintro (⟨arg,_,cycle⟩|⟨_,_,_,_,_,_,_,_,_,site,_,cycle⟩)
  · exact no_cycles arg.lower cycle
  · exact no_cycles site cycle

theorem parent_ready (done : Nat → Prop) : Ready (controlled done) root := by
  intro arg included
  cases List.mem_singleton.mp included
  exact ⟨_,knows_row (source_outer done (show (⟨0,lo⟩ : Equation) ∈ sourceRows from List.mem_cons_self)
    (by decide +kernel)) rfl⟩

theorem parent_matches (done : Nat → Prop) :
    HeadMatches (restriction (controlled done)) constructors interpret root impl :=
  .cons ⟨root_range,normalCode,_,_,normalized,lower done,upper done⟩ .nil

theorem child_matches (done : Nat → Prop) :
    HeadMatches (restriction (controlled done)) constructors interpret child leaf :=
  .cons ⟨left_range,.variable 0,[⟨0,.lower,3⟩],[⟨0,.upper,4⟩],rfl,.capture,.capture⟩ .nil

theorem root_frame (done : Nat → Prop) : Frame final reg interpret (controlled done) root impl parentBase placement := by
  have old := parent_frame done
  refine ⟨.cons ⟨root_range,.projected normalized center .capture .capture ?_⟩ .nil,
    old.ranges,old.clauses,old.returned⟩
  intro o found
  rcases List.mem_cons.mp found with rfl|more
  · exact .refl _
  · cases List.mem_singleton.mp more
    exact .refl _

theorem leaf_frame (done : Nat → Prop) : Frame final reg interpret (controlled done) child leaf leafBase placement := by
  have old := child_frame done
  refine ⟨.cons ⟨left_range,.ordinary (.actual rfl .capture ?_)⟩ .nil,old.ranges,old.clauses,old.returned⟩
  intro o found
  cases List.mem_singleton.mp found
  exact .refl _

theorem parent_selected (done : Nat → Prop) : branch done root (.selected impl.id [child]) := by
  refine .selected (parent_ready done) (no_recurs done _) ?_
    ⟨⟨List.mem_cons_self,rfl⟩,parent_matches done⟩ ?_
    ⟨parentBase,placement,root_frame done,child_exact⟩
  · rintro ⟨c,⟨there,role⟩,blocked⟩
    cases root_only c there role
    exact blocked (parent_matches done)
  · rintro c ⟨⟨there,role⟩,_⟩
    rw [root_only c there role]

theorem pending_child (done : Nat → Prop) (waiting : ¬done 42) : branch done child .pending := by
  refine GeneralDeclarativePriority321.Local.unsupported ?_ (no_recurs done _)
  apply Classical.byContradiction
  intro notDelayed
  exact child_waits done waiting ((ready_iff_not_delayed (controlled done) child).mpr notDelayed)

theorem selected_child (done : Nat → Prop) (now : done 42) : branch done child (.selected leaf.id []) := by
  refine .selected ((child_ready_iff done).mpr now) (no_recurs done _) ?_
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,child_matches done⟩ ?_
    ⟨leafBase,placement,leaf_frame done,rfl⟩
  · rintro ⟨d,⟨there,role⟩,blocked⟩
    cases child_only d there role
    exact blocked (child_matches done)
  · rintro d ⟨⟨there,role⟩,_⟩
    rw [child_only d there role]

theorem pending_root (done : Nat → Prop) (waiting : ¬done 42) : Classify (branch done) root .pending :=
  ⟨.selected impl.id [.pending],
    .selected (parent_selected done) (.cons (.pending (pending_child done waiting)) .nil),
    .selected (.cons .pending .nil) (.pending (by simp) (by simp) (by simp))⟩

theorem chosen_root (done : Nat → Prop) (ready : done 42) : Classify (branch done) root (.selected dict) :=
  ⟨.selected impl.id [.selected leaf.id []],
    .selected (parent_selected done) (.cons (.selected (selected_child done ready) .nil) .nil),
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)⟩

/-- The same ordinary state and same visible projection need not change
at all: changing completed-origin authorization changes the child's
actual diagnostic, not its projected center or ordinary models. -/
theorem late_transition (m) (model : Models final m) :
    Classify (branch (fun _ => False)) root .pending ∧
    Classify (branch (fun n => n = 42)) root (.selected dict) ∧
    Evidence reg interpret m root dict :=
  ⟨pending_root _ id,chosen_root _ rfl,sound checked declared model (chosen_root _ rfl)⟩

end Yulang.GeneralDeclarativeCovariantLate326
