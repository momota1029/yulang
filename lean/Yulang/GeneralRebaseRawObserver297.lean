import Yulang.GeneralRebaseRawInstallScan297

namespace Yulang.GeneralRebaseRawObserver297
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalSaturationState (Generated)
open GeneralNominalRecursiveCandidates (Metadata)
open GeneralSourceState (Output)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded declChecked)
open GeneralRebaseHeadProbe267 (atFocus)
open GeneralRebaseSourceObserver267 (Probes installAt)
open GeneralRebaseExecutableGenerated267 (discover discover_exact)
open GeneralRebaseLiveProjection264 (project liveFacts)
open GeneralRebaseStep258 (Proposal write)
open GeneralRebaseMultiSelection263 (proposal ofPlan)
open GeneralRebaseCheckedLocal266 (affectedProposal)
open GeneralRebaseRawInstallScan297 (Known selected_raw)
open GeneralRebaseSourceWitnessProgram297 (Checks Observed callbacks questions)
open GeneralRebaseWitnessContracts297 (head_total honest install_coverage merge_exact)
open GeneralRebaseFiniteWitnessTable297 (Covers)

def installs (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) (probes : Probes roles)
    (safety : Occurrence roles → Bool) : List (Plan roles) :=
  ((discover s.core.erased.current root).filter safety).flatMap fun focus =>
    installAt r s root focus checked probes

def proposals (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) (probes : Probes roles)
    (safety : Occurrence roles → Bool) : List Proposal :=
  (installs r s root checked probes safety).map (fun p => proposal s.core (ofPlan p)) ++
  (GeneralRebaseMergeScan267.scan s root probes.mergeInputs).map fun pair => affectedProposal s pair.1 pair.2

theorem listed_install (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) (probes : Probes roles)
    (safety : Occurrence roles → Bool) (p : Plan roles) :
    p ∈ installs r s root checked probes safety ↔
      ∃ f, Generated s.core.erased.current root f ∧ safety f = true ∧ p ∈ installAt r s root f checked probes := by
  simp only [installs,List.mem_flatMap,List.mem_filter,discover_exact,and_assoc]

theorem listed (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) (probes : Probes roles)
    (safety : Occurrence roles → Bool) (result : Proposal) :
    result ∈ proposals r s root checked probes safety ↔
      (∃ p ∈ installs r s root checked probes safety, proposal s.core (ofPlan p) = result) ∨
      ∃ pair ∈ GeneralRebaseMergeScan267.scan s root probes.mergeInputs,
        affectedProposal s pair.1 pair.2 = result := by
  simp only [proposals,List.mem_append,List.mem_map]

variable {roles : Roles.RoleDecls} {r : Registry} {s : State roles} {root : Occurrence roles}
  {checked : (Boundary roles).Checked r} {xs : List Assignment} {c : Checks roles}
  {safety : Occurrence roles → Bool}

def ExactSafety (r : Registry) (s : State roles) (root : Occurrence roles)
    (safety : Occurrence roles → Bool) : Prop :=
  ∀ f, Generated s.core.erased.current root f → (safety f = true ↔ Known r s f)

theorem sound
    (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (metadata : Metadata (Encoded r) s.core.erased.current.context)
    (safe : ExactSafety r s root safety)
    (cover : Covers (GeneralRebaseSourceWitnessProgram297.Holds s) (questions r s root checked) xs)
    (cert : Observed s xs (GeneralRebaseSourceQuestions297.entries r s root checked) c)
    (owners : List Nat) (pool : List Output)
    (p : Proposal) (present : p ∈ proposals r s root checked (callbacks xs c) safety) :
    ∃ after, (Boundary roles).Step r root s after ∧
      write (project owners pool s) p = project owners pool after ∧ p ⊆ liveFacts after := by
  rcases (listed ..).mp present with ⟨plan,listed,eq⟩ | ⟨⟨a,b⟩,pair,eq⟩
  · subst p
    obtain ⟨focus,generated,passes,selected⟩ := (listed_install ..).mp listed
    have guards := GeneralRebaseSignedObserver297.sound_guards (base := ⟨fun _ p => some
        (GeneralRebaseFiniteWitnessTable297.hit xs c.head p),fun _ _ => false,fun _ _ => false,
        (callbacks xs c).mergeInputs⟩) reach (install_coverage cover) cert.2.1 focus generated
    obtain ⟨e,same,f,enabled,novel⟩ := selected_raw reach generated metadata
      ((safe focus generated).mp passes) (honest cover cert focus generated) guards plan selected
    subst plan
    exact ⟨install s e,⟨_,f.symm ▸ generated,.install e enabled novel⟩,
      (GeneralRebaseSourceInstallProjection264.project_install_current r checked root s reach
        e enabled owners pool).symm,
      GeneralRebaseCheckedLocal266.install_proposal_in_live r checked root s reach e enabled⟩
  · subst p
    have inside := (GeneralRebaseMergeScan267.linkedPairs_exact ..).mp ((GeneralRebaseMergeScan267.scan_exact ..).mp pair).1
    exact ⟨_,GeneralRebaseMergeScan267.source_step (Encoded r) s root (callbacks xs c).mergeInputs a b pair
      (merge_exact cover cert a inside.1 b inside.2.1).mp,
      (GeneralRebaseAffectedMerge264.project_merge owners pool s a b).symm,
      GeneralRebaseCheckedLocal266.merge_proposal_in_live s a b⟩

theorem complete
    (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (safe : ExactSafety r s root safety)
    (cover : Covers (GeneralRebaseSourceWitnessProgram297.Holds s) (questions r s root checked) xs)
    (cert : Observed s xs (GeneralRebaseSourceQuestions297.entries r s root checked) c)
    (owners : List Nat) (pool : List Output) (after : State roles)
    (real : (Boundary roles).Step r root s after)
    (changed : project owners pool after ≠ project owners pool s) :
    ∃ p ∈ proposals r s root checked (callbacks xs c) safety,
      write (project owners pool s) p = project owners pool after := by
  rcases GeneralRebaseStrictSourceCases267.strict_inversion r root s after reach real
    owners pool changed with ⟨e,generated,enabled,novel,rfl⟩ | ⟨a,b,one,two,generated,matching,openPair,rfl⟩
  · let f := e.plan.packet.site.occurrence
    have guards := GeneralRebaseSignedObserver297.complete_guards (base := ⟨fun _ p => some
        (GeneralRebaseFiniteWitnessTable297.hit xs c.head p),fun _ _ => false,fun _ _ => false,
        (callbacks xs c).mergeInputs⟩) reach (install_coverage cover) cert.2.1 f generated
    have onList : e.plan ∈ installAt r s root f checked (callbacks xs c) :=
      GeneralRebaseInstallCoverage267.all_real_installs r s root checked reach e generated enabled novel
        ((callbacks xs c).head f) ((callbacks xs c).novelty f) ((callbacks xs c).joint f)
        (honest cover cert f generated) (head_total (checked := checked) f) guards
    have kept := (listed_install r s root checked (callbacks xs c) safety e.plan).mpr
      ⟨f,generated,(safe f generated).mpr enabled.safe,onList⟩
    exact ⟨_,(listed ..).mpr (Or.inl ⟨e.plan,kept,rfl⟩),
      (GeneralRebaseSourceInstallProjection264.project_install_current r checked root s reach
        e enabled owners pool).symm⟩
  · have kept := GeneralRebaseMergeScan267.actual_covered s root (callbacks xs c).mergeInputs
      a b one two generated openPair matching (merge_exact cover cert a one b two).mpr
    exact ⟨_,(listed ..).mpr (Or.inr ⟨(a,b),kept,rfl⟩),
      (GeneralRebaseAffectedMerge264.project_merge owners pool s a b).symm⟩

def observe (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) (xs : List Assignment) (c : Checks roles)
    (safety : Occurrence roles → Bool) (owners : List Nat) (pool : List Output) :
    GeneralRebaseStep258.Observer (GeneralRebaseCompression266.Basis owners pool) :=
  fun selected =>
    if selected.remaining = (project owners pool s).remaining then
      proposals r s root checked (callbacks xs c) safety
    else []

theorem observe_at (r : Registry) (s : State roles) (root : Occurrence roles)
    (checked : (Boundary roles).Checked r) (xs : List Assignment) (c : Checks roles)
    (safety : Occurrence roles → Bool) (owners : List Nat) (pool : List Output) :
    observe r s root checked xs c safety owners pool (project owners pool s) =
      proposals r s root checked (callbacks xs c) safety := by simp [observe]

theorem strict_exact
    (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (metadata : Metadata (Encoded r) s.core.erased.current.context)
    (safe : ExactSafety r s root safety)
    (cover : Covers (GeneralRebaseSourceWitnessProgram297.Holds s) (questions r s root checked) xs)
    (cert : Observed s xs (GeneralRebaseSourceQuestions297.entries r s root checked) c)
    (owners : List Nat) (pool : List Output)
    (target : GeneralRebaseStep258.State (GeneralRebaseCompression266.Basis owners pool)) :
    GeneralRebaseStep258.Step (observe r s root checked xs c safety owners pool)
      (project owners pool s) target ↔
    ∃ after, (Boundary roles).Step r root s after ∧
      project owners pool after = target ∧ target ≠ project owners pool s := by
  constructor
  · rintro ⟨p,member,recorded,diff⟩
    rw [observe_at] at member
    obtain ⟨after,step,same,_⟩ := sound reach metadata safe cover cert owners pool p member
    exact ⟨after,step,same.symm.trans recorded.symm,
      fun eq => diff (congrArg GeneralRebaseStep258.State.remaining eq)⟩
  · rintro ⟨after,step,recorded,diff⟩
    obtain ⟨p,member,same⟩ := complete reach safe cover cert owners pool after step (recorded.symm ▸ diff)
    refine ⟨p,?_,(same.trans recorded).symm,?_⟩
    · rwa [observe_at]
    · exact fun eq => diff (GeneralRebaseStep258.state_ext _ _ eq)

theorem same_projection_only
    (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (metadata : Metadata (Encoded r) s.core.erased.current.context)
    (safe : ExactSafety r s root safety)
    (cover : Covers (GeneralRebaseSourceWitnessProgram297.Holds s) (questions r s root checked) xs)
    (cert : Observed s xs (GeneralRebaseSourceQuestions297.entries r s root checked) c)
    (owners : List Nat) (pool : List Output) :
    (∀ next, ¬ GeneralRebaseStep258.Step (observe r s root checked xs c safety owners pool)
      (project owners pool s) next) ↔
    ∀ after, (Boundary roles).Step r root s after → project owners pool after = project owners pool s := by
  constructor
  · intro none after actual
    apply Classical.byContradiction
    intro unequal
    exact none _ ((strict_exact reach metadata safe cover cert owners pool _).mpr ⟨after,actual,rfl,unequal⟩)
  · intro all target transition
    obtain ⟨after,actual,recorded,diff⟩ := (strict_exact reach metadata safe cover cert owners pool _).mp transition
    exact diff (recorded.symm.trans (all after actual))

end Yulang.GeneralRebaseRawObserver297
