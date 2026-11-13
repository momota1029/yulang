import Yulang.GeneralNominalCenteredSelectedCompletion
import Yulang.GeneralNominalRecursiveExamples
import Yulang.GeneralDictionaryReachableEvidenceInitial
set_option backward.isDefEq.respectTransparency false

/-! One ground source has two equal scalar endpoint names. Certified nominal
revision can choose either name as a point descriptor without changing models. -/
namespace Yulang.GeneralNominalCenteredTerminalForkSource
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralDeclarationExamples (roles constructors display display_checked)
open GeneralSourceState (equationAtoms equationAtoms_exact)
open Core.PresenceGeneration (TyTerm)
open CommonNominalFullCarrier
open GeneralNominalReobservationSteps

abbrev base : GeneralSourceState.State where
  slots := 3
  source := Fin.val
  source_injective := fun _ _ equal => Fin.ext equal
  rowSource := Fin.val
  ordinary := equationAtoms 1 (.base .int) ++ equationAtoms 2 (.base .int)
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := fun slot => if slot = 0 then .unresolved else .scalar .int
  intervals := []
  heads_sound := by
    intro assignment valid slot term recorded
    by_cases zero : slot = 0
    · simp [zero,GeneralSourceState.Head.equation] at recorded
    · have same : (.base .int : TyTerm (Fin 3)) = term := by
        simpa [zero,GeneralSourceState.Head.equation] using recorded
      subst term
      have casesSlot : slot = 1 ∨ slot = 2 := by
        have bound := slot.isLt
        have nonzero : slot.val ≠ 0 := fun h => zero (Fin.ext h)
        rcases show slot.val = 1 ∨ slot.val = 2 by omega with one | two
        · exact Or.inl (Fin.ext one)
        · exact Or.inr (Fin.ext two)
      rcases casesSlot with rfl | rfl
      · exact (equationAtoms_exact ..).mp ((PresenceNormalForm.all_append ..).mp valid).1
      · exact (equationAtoms_exact ..).mp ((PresenceNormalForm.all_append ..).mp valid).2
  intervals_sound := by intro _ _ _ member; cases member

abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun slot => if slot = 0 then .deferred .unresolved else .scalar .int
  checked := by
    intro slot term recorded
    by_cases zero : slot = 0
    · simp [zero,GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Deferred.term] at recorded
    · have same : (.base .int : TyTerm (Fin 3)) = term := by
        simpa [zero,GeneralNormalizedObservation.Head.term] using recorded
      subst term
      exact .head (by simp [base,zero,GeneralSourceState.Head.equation])

abbrev bounds : Option Bool → Fin 3 × Fin 3
  | none => (1,2)
  | some false => (1,1)
  | some true => (2,2)

abbrev descriptor (choice : Option Bool) : GeneralNominalState.Descriptor 3 :=
  ⟨0,⟨[.type],0⟩,[.type (bounds choice)],rfl⟩

abbrev snapshot (choice : Option Bool) : GeneralNominalState.State where
  base := base
  view := view
  constructors := constructors
  nominals := fun slot => if slot = 0 then some (descriptor choice) else none
  catalogue := by
    intro slot d recorded
    split at recorded
    · cases Option.some.inj recorded; rfl
    · cases recorded
  bodies_opaque := by
    intro slot d recorded
    by_cases zero : slot = 0
    · subst slot; rfl
    · simp [zero] at recorded

abbrev context (choice : Option Bool) : GeneralNominalCandidates.Context :=
  ⟨snapshot choice,GeneralNominalExamples.interpretation⟩
abbrev registry : Registry := ⟨constructors,roles,[display]⟩
abbrev root : Occurrence roles := ⟨700,⟨3,fun _ => (1,1),[],by intro _ h; cases h⟩⟩
abbrev observer : Occurrence roles := GeneralNominalExamples.displayRoot
abbrev start := GeneralNominalCenteredSteps.initial (context none) root
abbrev finish (side : Bool) := GeneralNominalCenteredSteps.refresh start (context (some side))

theorem registry_checked : Checked registry := ⟨by simp,fun d member => (List.mem_singleton.mp member) ▸ display_checked⟩

theorem scalar (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (snapshot choice) model) (slot : Fin 3) (nonzero : slot ≠ 0) :
    Equivalent (model slot.val).1 (.base .int) :=
  valid.1.2.1 slot (.base .int) (by simp [base,nonzero,GeneralSourceState.Head.equation])

theorem bounds_scalar (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (snapshot choice) model) (other : Option Bool) :
    Equivalent (model (bounds other).1.val).1 (.base .int) ∧
      Equivalent (model (bounds other).2.val).1 (.base .int) := by
  cases other with
  | none => exact ⟨scalar model valid 1 (by decide +kernel),scalar model valid 2 (by decide +kernel)⟩
  | some side => cases side <;> exact ⟨scalar model valid _ (by decide +kernel),scalar model valid _ (by decide +kernel)⟩

theorem models_forward (first last : Option Bool) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (snapshot first) model) : GeneralNominalState.Models (snapshot last) model := by
  refine ⟨valid.1,?_,valid.2.2⟩
  intro slot d recorded
  by_cases zero : slot = 0
  · subst slot
    have same : descriptor last = d := Option.some.inj recorded
    subst d
    obtain ⟨values,fits,equal⟩ := valid.2.1 0 (descriptor first) rfl
    change GeneralNominalState.FitsAll base model [.type (bounds first)] values at fits
    cases fits with
    | @cons parameter value parameters values fit rest =>
      cases rest
      cases value with
      | inr => cases fit
      | inl value =>
        have old := bounds_scalar model valid first
        have new := bounds_scalar model valid last
        exact ⟨[.inl value],.cons ⟨subtype_trans new.1.1 (subtype_trans old.1.2 fit.1),
          subtype_trans fit.2 (subtype_trans old.2.1 new.2.2)⟩ .nil,equal⟩
  · simp [snapshot,zero] at recorded

theorem models_iff (first last : Option Bool) (model : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalState.Models (snapshot first) model ↔ GeneralNominalState.Models (snapshot last) model :=
  ⟨models_forward first last model,models_forward last first model⟩

theorem all_known (choice : Option Bool) (source : Nat) (member : source ∈ GeneralNominalState.sources (snapshot choice)) :
    GeneralNominalState.Known (snapshot choice) source := by
  have present : source = 0 ∨ source = 1 ∨ source = 2 := by
    simp [GeneralNominalState.sources,List.ofFn_succ] at member
    omega
  rcases present with rfl | rfl | rfl
  · exact ⟨0,rfl,Or.inr ⟨descriptor choice,rfl⟩⟩
  · exact ⟨1,rfl,Or.inl (by intro bad; cases bad)⟩
  · exact ⟨2,rfl,Or.inl (by intro bad; cases bad)⟩

def revision (side : Bool) : Revision start.erased.current where
  entries := (snapshot (some side)).nominals
  catalogue := (snapshot (some side)).catalogue
  opaqueHeads := (snapshot (some side)).bodies_opaque
  domain := by
    intro slot
    change ((snapshot (some side)).nominals slot = none) ↔ (snapshot none).nominals slot = none
    by_cases zero : slot = (0 : Fin 3) <;> simp [snapshot,zero]

theorem revision_certified (side : Bool) : Certified (revision side) where
  raw := models_forward (some side) none
  exact := by
    intro model
    change GeneralNominalSaturationState.Models (GeneralNominalSaturationState.initial (context (some side)) root) model ↔
      GeneralNominalSaturationState.Models (GeneralNominalSaturationState.initial (context none) root) model
    rw [GeneralNominalSaturationState.initial_models,GeneralNominalSaturationState.initial_models]
    exact models_iff (some side) none model

theorem point_closed (side : Bool) : PointClosed (snapshot (some side)) := by
  intro slot d recorded
  by_cases zero : slot = 0
  · subst slot
    have same : descriptor (some side) = d := Option.some.inj recorded
    subst d
    intro parameter member
    cases List.mem_singleton.mp member
    cases side <;> rfl
  · simp [snapshot,zero] at recorded

theorem revision_improves (side : Bool) : Improves (revision side) := by
  have noPoint : ∀ slot, ¬ PointAt (snapshot none) slot := by
    rintro slot ⟨d,recorded,point⟩
    by_cases zero : slot = 0
    · subst slot
      have same : descriptor none = d := Option.some.inj recorded
      subst d
      have impossible := point (.type (1,2)) (List.mem_singleton_self _)
      cases impossible
    · simp [snapshot,zero] at recorded
  refine ⟨fun slot point => False.elim (noPoint slot point),(0 : Fin 3),noPoint 0,descriptor (some side),rfl,?_⟩
  exact point_closed side 0 _ rfl

theorem step (side : Bool) : GeneralNominalCenteredSteps.Step registry root start (finish side) :=
  ⟨root,.root,.administrative root _ (.reobserve root (revision side) (revision_certified side) (revision_improves side))⟩

theorem metadata (choice : Option Bool) : GeneralNominalRecursiveCandidates.Metadata registry (context choice) := by
  refine ⟨rfl,?_⟩
  intro name primitive recorded
  by_cases two : name = 2
  · subst name
    have equal : GeneralCandidateInspection.Primitive.scalar .int = primitive := Option.some.inj recorded
    subst primitive
    exact ⟨⟨[],2⟩,rfl,rfl⟩
  · simp [two] at recorded

theorem source (choice : Option Bool) : GeneralNominalSourceFormation.InitialSource registry (context choice) root where
  roles_agree := rfl
  metadata := metadata choice
  linked := by
    constructor
    · intro index
      constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
    · intro output member; cases member
  intervals := fun _ _ _ => subtype_refl _
  below_seed := by
    intro name member
    have bounded := GeneralNominalAllocation.member_le_max _ _ member
    have equal : (GeneralNominalState.sources (snapshot choice)).foldr max 0 = (snapshot choice).seed := rfl
    exact equal ▸ bounded
  unallocated := rfl

theorem ground : GeneralNominalGroundAccessibility.GroundRoots (context none) root [.app 2 []] := by
  refine ⟨rfl,?_⟩
  intro index
  have zero : index.val = 0 := by have h := index.isLt; change index.val < 1 at h; omega
  have indexEq : index = ⟨0,by decide +kernel⟩ := Fin.ext zero
  subst index
  refine ⟨(.node (.scalar .int) Fin.elim0 : GeneralNominalOriginTerms.Expr Nat),?_,?_⟩
  · refine ⟨?_,rfl,trivial,fun index => Fin.elim0 index⟩
    simp [GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,
      normalize,normalizeArgs,GeneralNominalCompoundReadback.quote]
  · intro model valid
    exact scalar model valid 1 (by decide +kernel)

theorem reachable (side : Bool) : B4TargetV5.Reachable
    (GeneralNominalCenteredAdministrativeLocal.boundary roles) registry root (finish side) :=
  ⟨start,⟨context none,[.app 2 []],source none,(fun _ => rfl),ground,rfl⟩,.tail .refl (step side)⟩

theorem generated_only_root (side : Bool) (focus : Occurrence roles)
    (generated : GeneralNominalSaturationState.Generated (finish side).erased.current root focus) : focus = root := by
  induction generated with
  | root => rfl
  | child prior member ih => cases member
  | alias prior one two same ih =>
    exact congrArg GeneralNominalDemandMerging.Site.occurrence (List.mem_singleton.mp two)

theorem stable (side : Bool) : GeneralNominalCenteredSteps.Stable registry (finish side) root := by
  intro focus generated after action
  have same := generated_only_root side focus generated
  cases action with
  | administrative focus after action =>
    cases action with
    | enqueue linked absent => exact absent _ (List.mem_singleton_self _) same.symm
    | refresh context certificate source member unknown known => exact unknown (all_known _ source member)
    | equate first last one two equal novel =>
      exact novel (GeneralDictionaryReachableEvidenceInitial.initial_equal_is_raw (context (some side)) root first last equal)
    | reobserve revision certificate improved => exact pointClosed_no_revision (point_closed side) revision improved
  | refresh focus context certificate source member unknown known => exact unknown (all_known _ source member)
  | install plan support enabled novel guard =>
    have declaration : plan.packet.declaration = display := List.mem_singleton.mp enabled.1.2.2.2.1
    have role := enabled.1.2.2.2.2.1
    rw [declaration,same] at role
    contradiction
  | merge first last support one two inputs novel guard =>
    have a := List.mem_singleton.mp one
    have b := List.mem_singleton.mp two
    subst first; subst last
    exact novel (.refl _)

theorem halted (side : Bool) : ∀ next, ¬ GeneralNominalCenteredSteps.Step registry root (finish side) next := by
  rintro next ⟨focus,generated,action⟩
  exact stable side focus generated next action

theorem finish_models (side : Bool) (model : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalCenteredSteps.Models (finish side) model ↔ GeneralNominalState.Models (snapshot (some side)) model :=
  GeneralNominalCenteredSteps.point_initial_models (context (some side)) root (fun _ => rfl) model

theorem same_models (model : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalCenteredSteps.Models (finish false) model ↔ GeneralNominalCenteredSteps.Models (finish true) model :=
  (finish_models false model).trans ((models_iff (some false) (some true) model).trans (finish_models true model).symm)

end Yulang.GeneralNominalCenteredTerminalForkSource
