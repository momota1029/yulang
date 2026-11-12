import Yulang.GeneralNominalK2Coverage

/-! A nine-field local boundary, with four source obligations left explicit.
The concrete candidate fields below still conservatively defer unsupported
inspection and materialization. Packaging and local totality do not prove
completeness of that source compilation. No executor occurs in any field. -/
namespace Yulang.GeneralNominalLocalBoundary

open CommonRoleOutermostResolver
universe u

structure Fields (v : B4Target.Vocabulary.{u}) where
  Checked : v.Registry → Prop
  Models : v.State → v.Model → Prop
  RootPending : v.Registry → v.State → v.Demand → Prop
  RootK2 : v.Registry → v.State → v.Demand → Prop
  CandidateK2 : v.Registry → v.State → v.Demand → Prop
  InspectionPending : v.Registry → v.State → v.Demand → Prop
  Survivor : v.Registry → v.State → v.Demand → Nat → List v.Demand → Prop
  Reorders : v.Registry → v.Registry → Prop
  DictionaryEquivalent : Dictionary → Dictionary → Prop

structure Remaining (v : B4Target.Vocabulary.{u}) where
  Step : v.Registry → v.Demand → v.State → v.State → Prop
  Stable : v.Registry → v.State → v.Demand → Prop
  Generated : v.Registry → v.State → v.Demand → v.Demand → Prop
  Evidence : v.Registry → v.State → v.Model → v.Demand → Dictionary → Prop

def complete (fields : Fields v) (remaining : Remaining v) : B4Target.SourceBoundary v where
  Checked := fields.Checked
  Models := fields.Models
  RootPending := fields.RootPending
  RootK2 := fields.RootK2
  CandidateK2 := fields.CandidateK2
  InspectionPending := fields.InspectionPending
  Survivor := fields.Survivor
  Reorders := fields.Reorders
  DictionaryEquivalent := fields.DictionaryEquivalent
  Step := remaining.Step
  Stable := remaining.Stable
  Generated := remaining.Generated
  Evidence := remaining.Evidence

def RejectReason (b : Fields v) (r : v.Registry) (s : v.State) (d : v.Demand) : Prop :=
  ¬ b.RootPending r s d ∧ (b.RootK2 r s d ∨ b.CandidateK2 r s d ∨
    (¬ b.InspectionPending r s d ∧ ∀ key children, ¬ b.Survivor r s d key children))

def SafeKnown (b : Fields v) (r : v.Registry) (s : v.State) (d : v.Demand) : Prop :=
  ¬ b.RootPending r s d ∧ ¬ b.RootK2 r s d ∧
    ¬ b.CandidateK2 r s d ∧ ¬ b.InspectionPending r s d

def Unique (b : Fields v) (r : v.Registry) (s : v.State) (d : v.Demand)
    (key : Nat) (children : List v.Demand) : Prop :=
  b.Survivor r s d key children ∧ ∀ key' children', b.Survivor r s d key' children' →
    key' = key ∧ children' = children

inductive Local (b : Fields v) (r : v.Registry) (s : v.State) :
    v.Demand → Frontier v.Demand → Prop where
  | pending : b.RootPending r s d → Local b r s d .pending
  | inspectionPending : ¬ b.RootPending r s d → b.InspectionPending r s d →
      ¬ b.RootK2 r s d → ¬ b.CandidateK2 r s d → Local b r s d .pending
  | rejected : RejectReason b r s d → Local b r s d .rejected
  | ambiguous : SafeKnown b r s d →
      b.Survivor r s d key₁ cs₁ → b.Survivor r s d key₂ cs₂ → key₁ ≠ key₂ →
      Local b r s d .ambiguous
  | selected : SafeKnown b r s d → Unique b r s d key children →
      Local b r s d (.selected key children)

variable {v : B4Target.Vocabulary.{u}} {b : Fields v} {r : v.Registry} {s : v.State} {d : v.Demand}

theorem rejection_not_pending (reason : RejectReason b r s d) : ¬ b.RootPending r s d := reason.1

theorem safe_survivor_not_rejected (safe : SafeKnown b r s d)
    (survivor : b.Survivor r s d key children) : ¬ RejectReason b r s d := by
  rintro ⟨_, root | candidate | empty⟩
  · exact safe.2.1 root
  · exact safe.2.2.1 candidate
  · exact empty.2 key children survivor

theorem unique_not_ambiguous (unique : Unique b r s d key children)
    (first : b.Survivor r s d key₁ cs₁) (last : b.Survivor r s d key₂ cs₂)
    (distinct : key₁ ≠ key₂) : False := by
  exact distinct ((unique.2 _ _ first).1.trans (unique.2 _ _ last).1.symm)

/-- Unfinished inspection is below either K2 reason and above empty rejection. -/
theorem inspection_not_rejected (pending : b.InspectionPending r s d)
    (root : ¬ b.RootK2 r s d) (candidate : ¬ b.CandidateK2 r s d) :
    ¬ RejectReason b r s d := by
  rintro ⟨_, hr | hc | he⟩
  · exact root hr
  · exact candidate hc
  · exact he.1 pending

/-- Functional on every abstract boundary, without a coherence premise. -/
theorem local_functional (first : Local b r s d left) (last : Local b r s d right) : left = right := by
  cases first with
  | pending pending =>
      cases last with
      | pending => rfl
      | inspectionPending => rfl
      | rejected reason => exact False.elim (reason.1 pending)
      | ambiguous safe _ _ _ => exact False.elim (safe.1 pending)
      | selected safe _ => exact False.elim (safe.1 pending)
  | inspectionPending started pending root candidate =>
      cases last with
      | pending => rfl
      | inspectionPending => rfl
      | rejected reason => exact False.elim (inspection_not_rejected pending root candidate reason)
      | ambiguous safe _ _ _ => exact False.elim (safe.2.2.2 pending)
      | selected safe _ => exact False.elim (safe.2.2.2 pending)
  | rejected reason =>
      cases last with
      | pending pending => exact False.elim (reason.1 pending)
      | inspectionPending _ pending root candidate =>
          exact False.elim (inspection_not_rejected pending root candidate reason)
      | rejected => rfl
      | ambiguous safe survivor _ _ => exact False.elim (safe_survivor_not_rejected safe survivor reason)
      | selected safe unique => exact False.elim (safe_survivor_not_rejected safe unique.1 reason)
  | ambiguous safe survivorFirst survivorLast distinct =>
      cases last with
      | pending pending => exact False.elim (safe.1 pending)
      | inspectionPending _ pending _ _ => exact False.elim (safe.2.2.2 pending)
      | rejected reason => exact False.elim (safe_survivor_not_rejected safe survivorFirst reason)
      | ambiguous => rfl
      | selected _ unique => exact False.elim (unique_not_ambiguous unique survivorFirst survivorLast distinct)
  | selected safe unique =>
      cases last with
      | pending pending => exact False.elim (safe.1 pending)
      | inspectionPending _ pending _ _ => exact False.elim (safe.2.2.2 pending)
      | rejected reason => exact False.elim (safe_survivor_not_rejected safe unique.1 reason)
      | ambiguous _ first last distinct => exact False.elim (unique_not_ambiguous unique first last distinct)
      | selected _ other =>
          obtain ⟨keys, children⟩ := unique.2 _ _ other.1
          cases keys
          cases children
          rfl


def SurvivorChildrenFunctional (b : Fields v) (r : v.Registry) (s : v.State) (d : v.Demand) : Prop :=
  ∀ key first last, b.Survivor r s d key first → b.Survivor r s d key last → first = last

theorem local_total (coherent : SurvivorChildrenFunctional b r s d) :
    ∃ frontier, Local b r s d frontier := by
  classical
  by_cases pending : b.RootPending r s d
  · exact ⟨.pending, .pending pending⟩
  by_cases root : b.RootK2 r s d
  · exact ⟨.rejected, .rejected ⟨pending, .inl root⟩⟩
  by_cases candidate : b.CandidateK2 r s d
  · exact ⟨.rejected, .rejected ⟨pending, .inr (.inl candidate)⟩⟩
  by_cases inspecting : b.InspectionPending r s d
  · exact ⟨.pending, .inspectionPending pending inspecting root candidate⟩
  have safe : SafeKnown b r s d := ⟨pending, root, candidate, inspecting⟩
  by_cases existsSurvivor : ∃ key children, b.Survivor r s d key children
  · obtain ⟨key, children, survivor⟩ := existsSurvivor
    by_cases other : ∃ key' children', b.Survivor r s d key' children' ∧ key ≠ key'
    · obtain ⟨key', children', found, distinct⟩ := other
      exact ⟨.ambiguous, .ambiguous safe survivor found distinct⟩
    · refine ⟨.selected key children, .selected safe ⟨survivor, ?_⟩⟩
      intro key' children' found
      have same : key' = key := by
        apply Classical.byContradiction
        intro distinct
        exact other ⟨key', children', found, Ne.symm distinct⟩
      subst key'
      exact ⟨rfl, coherent key children' children found survivor⟩
  · refine ⟨.rejected, .rejected ⟨pending, .inr (.inr ⟨inspecting, ?_⟩)⟩⟩
    intro key children survivor
    exact existsSurvivor ⟨key, children, survivor⟩


theorem local_total_decidable (coherent : SurvivorChildrenFunctional b r s d)
    [Decidable (b.RootPending r s d)] [Decidable (b.RootK2 r s d)]
    [Decidable (b.CandidateK2 r s d)] [Decidable (b.InspectionPending r s d)]
    [Decidable (∃ key children, b.Survivor r s d key children)]
    [∀ key : Nat, Decidable (∃ key' children', b.Survivor r s d key' children' ∧ key ≠ key')] :
    ∃ frontier, Local b r s d frontier := by
  by_cases pending : b.RootPending r s d
  · exact ⟨.pending, .pending pending⟩
  by_cases root : b.RootK2 r s d
  · exact ⟨.rejected, .rejected ⟨pending, .inl root⟩⟩
  by_cases candidate : b.CandidateK2 r s d
  · exact ⟨.rejected, .rejected ⟨pending, .inr (.inl candidate)⟩⟩
  by_cases inspecting : b.InspectionPending r s d
  · exact ⟨.pending, .inspectionPending pending inspecting root candidate⟩
  have safe : SafeKnown b r s d := ⟨pending, root, candidate, inspecting⟩
  by_cases existsSurvivor : ∃ key children, b.Survivor r s d key children
  · obtain ⟨key, children, survivor⟩ := existsSurvivor
    by_cases other : ∃ key' children', b.Survivor r s d key' children' ∧ key ≠ key'
    · obtain ⟨key', children', found, distinct⟩ := other
      exact ⟨.ambiguous, .ambiguous safe survivor found distinct⟩
    · refine ⟨.selected key children, .selected safe ⟨survivor, ?_⟩⟩
      intro key' children' found
      have same : key' = key := by
        by_cases same : key' = key
        · exact same
        · exact False.elim (other ⟨key', children', found, Ne.symm same⟩)
      subst key'
      exact ⟨rfl, coherent key children' children found survivor⟩
  · refine ⟨.rejected, .rejected ⟨pending, .inr (.inr ⟨inspecting, ?_⟩)⟩⟩
    intro key children survivor
    exact existsSurvivor ⟨key, children, survivor⟩


theorem local_extension (remaining : Remaining v) (frontier : Frontier v.Demand) :
    Local b r s d frontier ↔ B4TargetV3.Local (complete b remaining) r s d frontier := by
  constructor
  · intro h
    cases h with
    | pending h => exact .pending h
    | inspectionPending a p k c => exact .inspectionPending a p k c
    | rejected h => exact .rejected h
    | ambiguous a p q h => exact .ambiguous a p q h
    | selected a p => exact .selected a p
  · intro h
    cases h with
    | pending h => exact .pending h
    | inspectionPending a p k c => exact .inspectionPending a p k c
    | rejected h => exact .rejected h
    | ambiguous a p q h => exact .ambiguous a p q h
    | selected a p => exact .selected a p

/-- Existing cycle-127 interfaces are unchanged. This is a separately named
local package, not a completed general SourceBoundary. -/
def generalFields (roles : Roles.RoleDecls) : Fields (GeneralNominalCandidates.vocabulary roles) where
  Checked := fun registry => registry.roles = roles ∧ GeneralDeclarations.Checked registry
  Models := fun context => GeneralNominalState.Models context.state
  RootPending := fun _ context root => GeneralNominalState.RootPending context.state root.demand
  RootK2 := fun _ context root => GeneralNominalK2Coverage.RootK2 context.state root.demand
  CandidateK2 := GeneralNominalK2Coverage.CandidateK2
  InspectionPending := GeneralNominalCandidates.InspectionPending
  Survivor := GeneralNominalCandidates.Survivor
  Reorders := GeneralRegistryReordering.Reorders
  DictionaryEquivalent := GeneralDictionaryPayloadOrder.Equivalent

theorem survivor_functional (roles : Roles.RoleDecls) (registry : GeneralDeclarations.Registry)
    (checked : (generalFields roles).Checked registry) (context : GeneralNominalCandidates.Context)
    (root : GeneralSourceDictionaries.Occurrence roles) :
    SurvivorChildrenFunctional (generalFields roles) registry context root :=
  fun key first last one two =>
    GeneralNominalCandidates.survivor_children_functional registry checked.2 context root key first last one two

theorem general_local_total (roles : Roles.RoleDecls) (registry : GeneralDeclarations.Registry)
    (checked : (generalFields roles).Checked registry) (context : GeneralNominalCandidates.Context)
    (root : GeneralSourceDictionaries.Occurrence roles) :
    ∃ frontier, Local (generalFields roles) registry context root frontier :=
  local_total (survivor_functional roles registry checked context root)

theorem general_local_functional (roles : Roles.RoleDecls) (registry : GeneralDeclarations.Registry)
    (context : GeneralNominalCandidates.Context) (root : GeneralSourceDictionaries.Occurrence roles)
    (first last : Frontier (GeneralSourceDictionaries.Occurrence roles))
    (one : Local (generalFields roles) registry context root first)
    (two : Local (generalFields roles) registry context root last) : first = last :=
  local_functional one two

theorem candidate_trichotomy (registry : GeneralDeclarations.Registry)
    (context : GeneralNominalCandidates.Context) (root : GeneralSourceDictionaries.Occurrence roles)
    (ready : ¬ GeneralNominalState.RootPending context.state root.demand)
    (declaration : GeneralDeclarations.Declaration) (visible : declaration ∈ registry.declarations)
    (checked : GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
    (sameRole : declaration.role = root.demand.role) :
    GeneralNominalCandidates.Failed registry context root declaration ∨
      GeneralNominalCandidates.Prepared registry context root declaration checked ∨
      GeneralNominalCandidates.InspectionPending registry context root := by
  classical
  by_cases failed : GeneralNominalCandidates.Failed registry context root declaration
  · exact Or.inl failed
  by_cases prepared : GeneralNominalCandidates.Prepared registry context root declaration checked
  · exact Or.inr (Or.inl prepared)
  exact Or.inr (Or.inr (GeneralNominalCandidates.conservative_deferral registry context root ready
    declaration visible checked sameRole failed prepared))

theorem failed_not_prepared (registry : GeneralDeclarations.Registry)
    (context : GeneralNominalCandidates.Context) (root : GeneralSourceDictionaries.Occurrence roles)
    (declaration : GeneralDeclarations.Declaration)
    (checked : GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
    (failed : GeneralNominalCandidates.Failed registry context root declaration) :
    ¬ GeneralNominalCandidates.Prepared registry context root declaration checked := by
  rintro ⟨_,_,_,bounds,located,finished,_,consistent,_⟩
  obtain ⟨_,_,other,found,_,_,_,reason⟩ := failed
  have same := Option.some.inj (located.symm.trans found)
  subst other
  rcases reason with conflict | inconsistent
  · exact conflict finished.2.1
  · exact inconsistent consistent

theorem root_pending_excludes_candidates (roles : Roles.RoleDecls)
    (registry : GeneralDeclarations.Registry) (context : GeneralNominalCandidates.Context)
    (root : GeneralSourceDictionaries.Occurrence roles)
    (pending : GeneralNominalState.RootPending context.state root.demand) :
    (∀ key children, ¬ (generalFields roles).Survivor registry context root key children) ∧
      ¬ (generalFields roles).InspectionPending registry context root ∧
      ¬ (generalFields roles).CandidateK2 registry context root ∧
      ¬ (generalFields roles).RootK2 registry context root :=
  ⟨fun _ _ survivor => survivor.1 pending, fun inspecting => inspecting.1 pending,
    fun cycle => cycle.1 pending, fun cycle => cycle.2.1 pending⟩


theorem blocked_defers (registry : GeneralDeclarations.Registry)
    (context : GeneralNominalCandidates.Context) (root : GeneralSourceDictionaries.Occurrence roles)
    (ready : ¬ GeneralNominalState.RootPending context.state root.demand)
    (declaration : GeneralDeclarations.Declaration) (visible : declaration ∈ registry.declarations)
    (checked : GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
    (sameRole : declaration.role = root.demand.role)
    (bounds : List (GeneralNominalInspection.Bounds context.state))
    (located : GeneralNominalCandidates.arguments context root = some bounds)
    (blocked : (GeneralNominalCandidates.report context declaration bounds).blocked ≠ []) :
    GeneralNominalCandidates.InspectionPending registry context root := by
  apply GeneralNominalCandidates.conservative_deferral registry context root ready declaration visible checked sameRole
  · rintro ⟨_,_,other,found,empty,_⟩
    have same := Option.some.inj (located.symm.trans found)
    subst other
    exact blocked empty
  · rintro ⟨_,_,_,other,found,finished,_⟩
    have same := Option.some.inj (located.symm.trans found)
    subst other
    exact blocked finished.1

theorem unsupported_layout_deferred (constructors : GeneralDeclarationPatterns.Constructors)
    (interpretation : GeneralNominalInspection.Interpretation) (key : Nat)
    (arguments : List GeneralDeclarationPatterns.Pattern)
    (declaration : GeneralDeclarationPatterns.Constructor)
    (catalogue : constructors key = some declaration) (nominal : interpretation.primitives key = none)
    (layout : declaration.parameters.all (· == .type) = false) :
    GeneralNominalInspection.translate constructors interpretation (.app key arguments) =
      .deferred (.app key arguments) := by
  simp [GeneralNominalInspection.translate,nominal,catalogue,layout]

end Yulang.GeneralNominalLocalBoundary
