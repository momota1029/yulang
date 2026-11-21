import Yulang.GeneralWhereOriginFixtureCut318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 25000000
namespace Yulang.GeneralWhereOriginRealInstall318
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralLiveCompoundRegistry316 (sourceRegistry declaration otherChild boundary_checked)
open GeneralLiveCompoundLeafInstall316 (after reachable)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralLiveCompoundPostRootHead316 (frame)
open GeneralWhereVersionSnapshot317 (context)
open GeneralWhereVersionInstall317 (before fixed Models InstallStep)
open GeneralWhereVersionCase317 (expr lowerRow upperRow)
open GeneralWhereOriginDelta318 (Cell)
open GeneralWhereOriginFixture318 (initial_trace)
open GeneralWhereOriginCheckedLayout318 (validates)
open GeneralWhereOriginFixtureCut318 (legacy_cut current_guard)
open GeneralWhereOriginPartition318 (allClassified classified_iff fresh_iff)
open GeneralWhereOriginJoint318 (VisibleReads guard)
open GeneralWhereOriginSuccessor318 (SilentChildren)
open GeneralWhereOriginInstall318 (RawTicket executes)
open GeneralWhereOriginTrace318 (Trace)
open GeneralNominalCommonBridge (Assignment)
open GeneralWhereVersionCompiler317 (schema children)

theorem all_fresh : allClassified before rootPlan (guard before rootPlan) = true := by
  apply (classified_iff before rootPlan _).mpr
  intro cell
  apply List.mem_append_right
  apply (fresh_iff before cell _).mpr
  obtain ⟨k,tag,eq⟩ := cell.high (t := GeneralLiveCompoundPost316.raw) rfl
  exact eq.symm ▸ ⟨GeneralVersionedHighOrigins315.raw_absent reachable tag,legacy_cut tag,current_guard tag⟩

theorem scoped_reads : VisibleReads rootPlan := by
  intro c listed i code found n reads
  cases List.mem_singleton.mp listed
  have atZero : i = 0 := Fin.ext (Nat.eq_zero_of_le_zero (by
    have bound := i.isLt
    change i.val < 1 at bound
    omega))
  subst i
  have actual : code = expr := Option.some.inj found.symm
  subst code
  change n ∈ [0] at reads
  have name := List.mem_singleton.mp reads
  subst n
  exact Or.inl List.mem_cons_self

theorem source_sound : RawTicket before rootPlan context := by
  intro m valid h
  have lo : lowerRow ∈ (schema rootPlan).equations :=
    GeneralWhereVersionCase317.rows.symm ▸ List.mem_cons_of_mem _ List.mem_cons_self
  have hi : upperRow ∈ (schema rootPlan).equations :=
    GeneralWhereVersionCase317.rows.symm ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have ports := GeneralWhereVersionWitness317.both_values m valid.1 h.head (h.rows _ lo) (h.rows _ hi)
  exact GeneralWhereVersionSnapshot317.constrained m valid.1.1.1 ports.1 ports.2

theorem no_child_outputs : SilentChildren rootPlan := by
  intro s member
  rw [GeneralWhereVersionInstall317.fixture_emitted] at member
  cases List.mem_singleton.mp member
  exact GeneralWhereVersionCommit317.terminal_outputs

theorem executed :
    InstallStep sourceRegistry before fixed ∧ Trace sourceRegistry fixed ∧
    (∃ m, Models before m ∧ Models fixed m) ∧
    ∀ d ∈ children rootPlan, GeneralNominalSaturationState.Generated
      fixed.mixed.core.erased.current root d := by
  obtain ⟨m,common⟩ := GeneralWhereVersionWitness317.inhabited
  have prior : Models before m := ⟨common.1,fun _ impossible => by cases impossible⟩
  have selected := GeneralLiveCompoundPostRootSelect316.selected
  have semantic := GeneralWhereVersionSemantics317.full m common
  obtain ⟨step,trace,models,kids⟩ := executes (ctx := context) boundary_checked initial_trace frame
    (by rw [GeneralLiveCompoundPostRootHead316.root_children]; exact selected)
    GeneralLiveCompoundProposedRepair316.choice_compatible
    (GeneralWhereOriginLayout318.checkedDelta GeneralWhereVersionRefine317.refines rfl validates)
    rfl all_fresh (GeneralLiveCompoundRegistry316.coverage.1 _ List.mem_cons_self)
    scoped_reads no_child_outputs source_sound m prior
    ⟨semantic.head,semantic.input,semantic.captures,semantic.headSchema,common.2.2.2.1⟩
    (fun row found _ => semantic.rows row found)
    (fun c listed sig => (semantic.childSemantics c listed sig).2)
  obtain ⟨n,old,new,_⟩ := models
  exact ⟨step,trace,⟨n,old,new⟩,kids⟩

end Yulang.GeneralWhereOriginRealInstall318
