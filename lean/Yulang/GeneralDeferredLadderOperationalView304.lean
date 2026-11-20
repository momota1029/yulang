import Yulang.GeneralNominalVersionedMixedKernel234

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderOperationalView304
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedInstallStep232 (Committed)
open GeneralNominalSaturationState (Alias Generated)
open GeneralNominalVersionedEffects231 (ClassEffects)
open GeneralNominalCommonBridge (Assignment)

variable {roles : Roles.RoleDecls} {a b : State roles}

/-- The data that determine generated occurrences and semantic commitment.
In particular, equality of old effect and plan snapshots is not required. -/
structure View (a b : State roles) : Prop where
  sites : a.core.erased.current.sites = b.core.erased.current.sites
  edges : a.core.erased.current.edges = b.core.erased.current.edges
  aliases : a.core.erased.current.aliases = b.core.erased.current.aliases
  models : ∀ model, Models a model ↔ Models b model

theorem View.symm (ab : View a b) : View b a :=
  ⟨ab.sites.symm,ab.edges.symm,ab.aliases.symm,fun m => (ab.models m).symm⟩

theorem alias_forward (ab : View a b) (path : Alias a.core.erased.current i j) :
    Alias b.core.erased.current i j := by
  induction path with
  | refl => exact .refl _
  | edge member => exact .edge (ab.aliases ▸ member)
  | symm _ ih => exact .symm ih
  | trans _ _ ih jh => exact .trans ih jh

theorem generated_forward (ab : View a b) (path : Generated a.core.erased.current root node) :
    Generated b.core.erased.current root node := by
  induction path with
  | root => exact .root
  | child _ found ih => exact .child ih (ab.edges ▸ found)
  | alias _ first last joined ih =>
    exact .alias ih (ab.sites ▸ first) (ab.sites ▸ last) (alias_forward ab joined)

theorem generated_iff (ab : View a b) :
    Generated a.core.erased.current root node ↔ Generated b.core.erased.current root node :=
  ⟨generated_forward ab,generated_forward ab.symm⟩

theorem requests_iff (ab : View a b) (root : GeneralSourceDictionaries.Occurrence roles)
    (output : GeneralSourceState.Output) :
    output ∈ GeneralNominalCenteredHeadOutputs.requests a.core root ↔
      output ∈ GeneralNominalCenteredHeadOutputs.requests b.core root :=
  GeneralNominalVersionedRefresh232.requests_iff_of_same_lists ab.sites ab.aliases

theorem classes_iff (ab : View a b) (p : GeneralNominalCenters.Plan roles)
    (root : GeneralSourceDictionaries.Occurrence roles) (m : Assignment) :
    ClassEffects a.core root p m ↔ ClassEffects b.core root p m := by
  unfold ClassEffects GeneralNominalCenteredHeadOutputs.EqualOutputs
  constructor
  · rintro ⟨effects,outputs⟩
    exact ⟨fun x h => effects x ((requests_iff ab root x).mpr h),
      fun x hx y hy => outputs x ((requests_iff ab root x).mpr hx)
        y ((requests_iff ab root y).mpr hy)⟩
  · rintro ⟨effects,outputs⟩
    exact ⟨fun x h => effects x ((requests_iff ab root x).mp h),
      fun x hx y hy => outputs x ((requests_iff ab root x).mp hx)
        y ((requests_iff ab root y).mp hy)⟩

theorem committed_forward (ab : View a b) (p : GeneralNominalCenters.Plan roles)
    (prior : Committed a p) : Committed b p := by
  constructor
  · intro m mb
    have h := prior.1 m ((ab.models m).mpr mb)
    exact ⟨h.1,(classes_iff ab p p.packet.site.occurrence m).mp h.2⟩
  · intro c member
    exact ab.edges ▸ prior.2 c member

theorem committed_iff (ab : View a b) (p : GeneralNominalCenters.Plan roles) :
    Committed a p ↔ Committed b p := ⟨committed_forward ab p,committed_forward ab.symm p⟩

theorem after_install (ab : View a b) (e f : GeneralNominalVersionedJournal232.Effect roles)
    (rows : GeneralNominalVersionedChildren232.rawSites e.plan =
      GeneralNominalVersionedChildren232.rawSites f.plan)
    (children : GeneralNominalVersionedChildren232.edges e.plan =
      GeneralNominalVersionedChildren232.edges f.plan)
    (semantic : ∀ m, Models (install a e) m ↔ Models (install b f) m) :
    View (install a e) (install b f) := by
  refine ⟨?_,?_,ab.aliases,semantic⟩
  · change a.core.erased.current.sites ++ _ = b.core.erased.current.sites ++ _
    rw [ab.sites,rows]
  · change a.core.erased.current.edges ++ _ = b.core.erased.current.edges ++ _
    rw [ab.edges,children]

/-- Only the name and chosen declaration of an old packet affect the
choice guard. The old packet context can differ between the journals. -/
def choices (a : State roles) : List (Nat × Nat) :=
  a.core.erased.current.packets.map fun p => (p.site.occurrence.identity,p.declaration.id)

theorem choice_forward (ab : View a b) (selected : choices a = choices b)
    (given : GeneralNominalCycleSteps.ChoiceCompatible a.core.erased.current p) :
    GeneralNominalCycleSteps.ChoiceCompatible b.core.erased.current p := by
  intro prior listed joined
  have mapped : (prior.site.occurrence.identity,prior.declaration.id) ∈ choices b :=
    List.mem_map.mpr ⟨prior,listed,rfl⟩
  rw [← selected] at mapped
  obtain ⟨old,recorded,ids⟩ := List.mem_map.mp mapped
  have same := Prod.mk.inj ids
  exact (given old recorded (same.1.symm ▸ alias_forward ab.symm joined)).trans same.2

theorem choice_iff (ab : View a b) (selected : choices a = choices b) :
    GeneralNominalCycleSteps.ChoiceCompatible a.core.erased.current p ↔
      GeneralNominalCycleSteps.ChoiceCompatible b.core.erased.current p :=
  ⟨choice_forward ab selected,choice_forward ab.symm selected.symm⟩

theorem after_choices (selected : choices a = choices b)
    (e f : GeneralNominalVersionedJournal232.Effect roles)
    (key : e.plan.packet.declaration.id = f.plan.packet.declaration.id)
    (focus : e.plan.packet.site.occurrence.identity = f.plan.packet.site.occurrence.identity) :
    choices (install a e) = choices (install b f) := by
  change (_,_) :: choices a = (_,_) :: choices b
  rw [selected,key,focus]

theorem frame_forward (ab : View a b) (context : a.core.erased.current.context = b.core.erased.current.context)
    (rows : a.core.sites = b.core.sites) (frame : GeneralNominalVersionedEvidence231.Frame registry a.core root key p) :
    GeneralNominalVersionedEvidence231.Frame registry b.core root key p :=
  ⟨frame.registry_eq,frame.context_eq.trans context,frame.occurrence_eq,frame.key_eq,
    ab.sites ▸ frame.raw_recorded,rows ▸ frame.center_recorded,frame.visible,frame.role_eq,
    frame.located,context ▸ frame.prepared⟩

end Yulang.GeneralDeferredLadderOperationalView304
