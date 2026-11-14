import Yulang.GeneralNominalCenteredHeadAllocCollision
import Yulang.GeneralNominalCenteredHeadAllocComposition

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCenteredHeadAllocMergeSource
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection CommonNominalFullCarrier
open GeneralDeclarationExamples (constructors)

abbrev roles := GeneralNominalCenteredHeadMatCompletionCollisionSource.roles
abbrev firstClause : Clause := ⟨42,1,[],[⟨43,0,.app 2 []⟩]⟩
abbrev lastClause : Clause := ⟨44,1,[],[⟨43,0,.variant 0 (.app 2 [])⟩]⟩
abbrev parent : Declaration := ⟨37,0,[.app 2 []],[firstClause,lastClause],[],[]⟩
abbrev leaf : Declaration := ⟨38,1,[],[],[⟨45,0,.app 2 []⟩],[]⟩
abbrev sourceRegistry : Registry := ⟨constructors,roles,[parent,leaf]⟩
abbrev registry := GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry
abbrev declaration := GeneralNominalCenteredHeadAllocEncoding.declaration parent

theorem parent_checked : DeclarationChecked constructors roles parent := by
  constructor
  · refine ⟨rfl,by simp,?_,?_⟩
    · intro name body found; cases found
    · intro clause member
      rcases List.mem_cons.mp member with rfl | member
      · refine ⟨rfl,?_⟩
        intro equation member; cases List.mem_singleton.mp member; exact ⟨none,rfl⟩
      · cases List.mem_singleton.mp member
        refine ⟨rfl,?_⟩
        intro equation member; cases List.mem_singleton.mp member; exact ⟨none,rfl⟩
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro clause member; rcases List.mem_cons.mp member with rfl | member
    · exact ⟨rfl,rfl⟩
    · cases List.mem_singleton.mp member; exact ⟨rfl,rfl⟩
  · intro clause member; rcases List.mem_cons.mp member with rfl | member
    · exact (checkSmaller_exact _ _).mp (by decide +kernel)
    · cases List.mem_singleton.mp member; exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause member; rcases List.mem_cons.mp member with rfl | member
    · unfold ConservativeSmaller; decide +kernel
    · cases List.mem_singleton.mp member; unfold ConservativeSmaller; decide +kernel
  · intro clause member capture
    have empty : clause.arguments = [] := by
      rcases List.mem_cons.mp member with rfl | member
      · rfl
      · cases List.mem_singleton.mp member; rfl
    rw [empty]
    change Smaller [.app 2 []] []
    exact (checkSmaller_exact _ _).mp (by decide +kernel)

theorem leaf_checked : DeclarationChecked constructors roles leaf := by
  constructor
  · refine ⟨rfl,?_,?_,by simp⟩
    · intro equation member; cases List.mem_singleton.mp member; exact ⟨none,rfl⟩
    · intro name body found
      have same : name = 0 := by
        change (if name = 0 then some none else none) = some body at found
        split at found
        · assumption
        · cases found
      subst name
      exact Or.inl ⟨_,List.mem_singleton_self _,rfl⟩
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro clause member; cases member
  · intro clause member; cases member
  · intro clause member; cases member
  · intro clause member; cases member

theorem source_checked : Checked sourceRegistry := by
  refine ⟨by simp,?_⟩
  intro d member
  rcases List.mem_cons.mp member with rfl | member
  · exact parent_checked
  · cases List.mem_singleton.mp member; exact leaf_checked

theorem checked : Checked registry := GeneralNominalCenteredHeadAllocEncoding.registry_checked source_checked
theorem declaration_checked : DeclarationChecked constructors roles declaration :=
  GeneralNominalCenteredHeadAllocEncoding.declaration_checked parent_checked

abbrev base : GeneralSourceState.State where
  slots := 1
  source := Fin.val
  source_injective := fun _ _ same => Fin.ext same
  rowSource := Fin.val
  ordinary := GeneralSourceState.equationAtoms 0 (.base .int)
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := fun _ => .scalar .int
  intervals := []
  heads_sound := by
    intro assignment valid slot term recorded
    have zero : slot = 0 := Subsingleton.elim _ _
    subst slot
    cases Option.some.inj recorded
    exact (GeneralSourceState.equationAtoms_exact ..).mp valid
  intervals_sound := by intro _ _ _ member; cases member

abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun _ => .scalar .int
  checked := by
    intro slot term recorded
    cases Option.some.inj recorded
    exact .head rfl

abbrev snapshot : GeneralNominalState.State where
  base := base
  view := view
  constructors := constructors
  nominals := fun _ => none
  catalogue := by intro _ _ h; cases h
  bodies_opaque := by intro _ _ h; cases h

abbrev context : GeneralNominalCandidates.Context := ⟨snapshot,GeneralNominalExamples.interpretation⟩
abbrev root : Occurrence roles := ⟨100,⟨0,fun _ => (0,0),[],by intro _ h; cases h⟩⟩
abbrev start := GeneralNominalCenteredHeadMatStepJournal.initial context root

theorem source : GeneralNominalSourceFormation.InitialSource sourceRegistry context root where
  roles_agree := rfl
  metadata := GeneralNominalCenteredTerminalForkSource.metadata (some false)
  linked := ⟨by intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ],by intro _ h; cases h⟩
  intervals := fun _ _ _ => subtype_refl _
  below_seed := by
    intro identity member
    simp [GeneralNominalState.sources,List.ofFn_succ] at member
    subst identity; exact Nat.le_refl _
  unallocated := rfl

theorem scalar (valid : GeneralNominalState.Models snapshot assignment) : Equivalent (assignment 0).1 (.base .int) :=
  valid.1.2.1 0 _ rfl

theorem source_model (equal : (assignment 0).1 = .base .int) : GeneralNominalState.Models snapshot assignment := by
  refine ⟨⟨?_,?_,by intro _ member; cases member⟩,?_,?_⟩
  · intro atom member
    simp only [base,GeneralSourceState.equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · change Subtype (assignment 0).1 (.base .int)
      rw [equal]; exact subtype_refl _
    · change Subtype (.base .int) (assignment 0).1
      rw [equal]; exact subtype_refl _
  · intro slot term recorded
    have zero : slot = 0 := Subsingleton.elim _ _
    subst slot; cases Option.some.inj recorded
    change Equivalent (assignment 0).1 (.base .int)
    rw [equal]; exact ⟨subtype_refl _,subtype_refl _⟩
  · intro _ _ h; cases h
  · intro _ h; cases h

theorem ground : GeneralNominalGroundAccessibility.GroundRoots context root [.app 2 []] := by
  refine ⟨rfl,?_⟩
  intro index
  let term : GeneralNominalOriginTerms.Expr Nat := .node (.scalar .int) Fin.elim0
  refine ⟨term,?_,fun _ valid => scalar valid⟩
  refine ⟨?_,?_,?_⟩
  · simp [normalize,normalizeArgs,GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,
      GeneralNominalCompoundReadback.quote,term]
  · simp [term,GeneralNominalOriginTerms.Expr.leaves,List.ofFn_zero,GeneralNominalOriginTerms.arity]
  · exact ⟨trivial,fun index => Fin.elim0 index⟩

theorem coverage : GeneralNominalCenteredHeadWFSource.Coverage sourceRegistry context.interpretation := by
  constructor
  · intro d member
    rcases List.mem_cons.mp member with rfl | member
    · simp [GeneralNominalCenteredHeadWFSource.DeclarationCovered,
        GeneralNominalCenteredHeadWFSource.PatternsCovered,GeneralNominalCenteredHeadWFSource.PatternCovered,
        GeneralNominalCenteredHeadWFFixtures.int_constructor]
    · cases List.mem_singleton.mp member
      simp [GeneralNominalCenteredHeadWFSource.DeclarationCovered,
        GeneralNominalCenteredHeadWFSource.PatternsCovered,GeneralNominalCenteredHeadWFSource.PatternCovered,
        GeneralNominalCenteredHeadWFFixtures.int_constructor]
  · intro role name body found
    change (roles role).assoc name = some (some body) at found
    by_cases zero : role = 0
    · simp [roles,GeneralNominalCenteredHeadMatCompletionCollisionSource.roles,zero,GeneralDeclarationExamples.bareRole] at found
    · by_cases named : name = 0 <;> simp [roles,GeneralNominalCenteredHeadMatCompletionCollisionSource.roles,zero,named] at found

theorem initial_source : (GeneralNominalCenteredHeadAllocBoundary.boundary roles).Initial sourceRegistry root start :=
  ⟨context,[.app 2 []],source,(fun _ => rfl),ground,coverage,rfl⟩
theorem reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadAllocBoundary.boundary roles) sourceRegistry root start :=
  ⟨start,initial_source,.refl⟩
theorem compiled_reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadMatStepBoundary.boundary roles) registry root start :=
  GeneralNominalCenteredHeadAllocBoundary.reachable_compiled reachable

abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite root,declaration,declaration_checked,[(0,0)]⟩
abbrev plan : Plan roles := ⟨packet,rootSite snapshot.seed root,rfl⟩
noncomputable abbrev children := packet.children

end Yulang.GeneralNominalCenteredHeadAllocMergeSource
