import Yulang.GeneralNominalDownstreamDepth
import Yulang.GeneralNominalReobservationMergeDiamond

/-! Certified observation-only changes do not increase support depth. The
finite closure includes both refresh and descriptor replacement. Installations
and merges change the dependency journal and are deliberately not covered. -/
namespace Yulang.GeneralNominalBudgetObservation
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalDownstreamSupport GeneralNominalDownstreamDepth

variable {roles : Roles.RoleDecls}

structure SameJournal (before after : State roles) : Prop where
  packets : before.packets = after.packets
  sites : before.sites = after.sites
  edges : before.edges = after.edges
  aliases : before.aliases = after.aliases

theorem SameJournal.symm (same : SameJournal before after) : SameJournal after before :=
  ⟨same.packets.symm,same.sites.symm,same.edges.symm,same.aliases.symm⟩

theorem view_journal (view : View before after) : SameJournal before after := by
  induction view with
  | current => exact ⟨rfl,rfl,rfl,rfl⟩
  | refresh _ _ ih => exact ⟨ih.packets,ih.sites,ih.edges,ih.aliases⟩
  | reobserve _ _ _ ih => exact ⟨ih.packets,ih.sites,ih.edges,ih.aliases⟩

theorem view_trans (first : View before middle) (last : View middle after) : View before after := by
  induction last with
  | current => exact first
  | refresh _ certificate ih => exact .refresh ih certificate
  | reobserve revision _ certificate ih => exact .reobserve revision ih certificate

theorem discharge_transport (same : SameJournal before after) (done : Discharged before producer) : Discharged after producer := by
  induction done with
  | packet packet member _ ih => exact .packet packet (same.packets ▸ member) ih
  | alias first last one two related _ ih =>
    exact .alias first last (same.sites ▸ one) (same.sites ▸ two)
      (GeneralNominalReobservationMergeDiamond.alias_of_same_edges same.aliases related) ih

theorem waiting_transport (same : SameJournal before after) (path : Waiting before root child) : Waiting after root child := by
  induction path with
  | root unresolved => exact .root (fun done => unresolved (discharge_transport same.symm done))
  | child _ edge unresolved ih =>
    exact .child ih (same.edges ▸ edge) (fun done => unresolved (discharge_transport same.symm done))
  | alias first last _ one two related unresolved ih =>
    exact .alias first last ih (same.sites ▸ one) (same.sites ▸ two)
      (GeneralNominalReobservationMergeDiamond.alias_of_same_edges same.aliases related)
      (fun done => unresolved (discharge_transport same.symm done))

/-- The pre-view guard already quantifies over every later certified view. -/
theorem need_before (state : Tracked roles) (view : View state.current after)
    (needed : Need registry {state with current := after} focus identity test) :
    Need registry state focus identity test := by
  cases needed with
  | input index test available => exact .input index test available
  | inspection observed more declaration member role bounds located slot read test available =>
    exact .inspection observed (view_trans view more) declaration member role bounds located slot read test available

theorem depth_nonincreasing (state : Tracked roles) (view : View state.current after)
    (known : AtDepth registry state depth producer) :
    AtDepth registry {state with current := after} depth producer := by
  have journal := view_journal view
  induction depth generalizing producer with
  | zero => exact discharge_transport journal known
  | succ depth ih =>
    rcases known with done | heads
    · exact Or.inl (discharge_transport journal done)
    · refine Or.inr ?_
      intro child path unresolved identity test needed
      have oldPath := waiting_transport journal.symm path
      have oldOpen : ¬ Discharged state.current child := fun done => unresolved (discharge_transport journal done)
      obtain ⟨support,entailed,smaller⟩ := heads child oldPath oldOpen identity test (need_before state view needed)
      exact ⟨support,entailed,fun dependency member => ih (smaller dependency member)⟩

theorem grounded_preserved (state : Tracked roles) (view : View state.current after)
    (grounded : Grounded registry state producer) : Grounded registry {state with current := after} producer := by
  obtain ⟨depth,known⟩ := grounded_depth grounded
  exact depth_grounded (depth_nonincreasing state view known)

/-- In particular both currently implemented observation update constructors
preserve every prior depth certificate, without a source-size premise. -/
theorem refresh_depth (state : Tracked roles) (context : GeneralNominalCandidates.Context)
    (certificate : GeneralNominalFeedbackSteps.Refresh state.current context)
    (known : AtDepth registry state depth producer) :
    AtDepth registry {state with current := regenerate state.current context} depth producer :=
  depth_nonincreasing state (.refresh .current certificate) known

theorem revision_depth (state : Tracked roles) (revision : GeneralNominalReobservationSteps.Revision state.current)
    (certificate : GeneralNominalReobservationSteps.Certified revision)
    (known : AtDepth registry state depth producer) :
    AtDepth registry {state with current := revision.result} depth producer :=
  depth_nonincreasing state (.reobserve revision .current certificate) known

end Yulang.GeneralNominalBudgetObservation
