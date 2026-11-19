import Yulang.GeneralRebaseRegistryDiagnostics277

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseRegistryLocal277
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedDiagnostic232 (boundary v6 v7 Local)
open GeneralRebaseRegistryDiagnostics277
open GeneralRebaseRegistrySurface277 (symmetric)
variable {roles : Roles.RoleDecls} {a b : Registry} {s : State roles} {root : Occurrence roles}

theorem safe_forward (surface : On a b s root)
    (h : B4TargetV8.SafeKnown (boundary roles) a s root) :
    B4TargetV8.SafeKnown (boundary roles) b s root :=
  ⟨h.1,h.2.1,fun other => h.2.2.1 ((k2 surface).mpr other),
    fun other => h.2.2.2 ((inspection surface).mpr other)⟩

theorem unique_iff (surface : On a b s root) (k : Nat) (kids : List (Occurrence roles)) :
    B4TargetV8.Unique (boundary roles) a s root k kids ↔
      B4TargetV8.Unique (boundary roles) b s root k kids :=
  GeneralRebaseRegistrySurface277.unique surface

theorem priority_v7 (surface : On a b s root) :
    B4TargetV7.PriorityAmbiguity (v7 roles) a s root ↔
      B4TargetV7.PriorityAmbiguity (v7 roles) b s root := by
  unfold B4TargetV7.PriorityAmbiguity
  have k : (v7 roles).CandidateK2 a s root ↔ (v7 roles).CandidateK2 b s root := k2 surface
  have survivors : ∀ key ch, (v7 roles).Survivor a s root key ch ↔
      (v7 roles).Survivor b s root key ch := survivor_iff surface
  simp only [k,survivors]
  rfl

theorem priority_v8 (surface : On a b s root) :
    B4TargetV8.PriorityAmbiguity (boundary roles) a s root ↔
      B4TargetV8.PriorityAmbiguity (boundary roles) b s root :=
  priority_v7 surface

theorem reject_v6 (surface : On a b s root) :
    B4TargetV6.RejectReason (v6 roles) a s root ↔
      B4TargetV6.RejectReason (v6 roles) b s root := by
  unfold B4TargetV6.RejectReason
  have k : (v6 roles).CandidateK2 a s root ↔ (v6 roles).CandidateK2 b s root := k2 surface
  have p : (v6 roles).InspectionPending a s root ↔ (v6 roles).InspectionPending b s root := inspection surface
  have survived (key ch) : (v6 roles).Survivor a s root key ch ↔
      (v6 roles).Survivor b s root key ch := survivor_iff surface key ch
  have unique (key ch) : B4TargetV6.Unique (v6 roles) a s root key ch ↔
      B4TargetV6.Unique (v6 roles) b s root key ch := unique_iff surface key ch
  have conflict (key) : (v6 roles).OutputConflict a s root key ↔ (v6 roles).OutputConflict b s root key :=
    output_conflict surface key
  simp only [k,p,survived,unique,conflict]
  rfl

theorem local_v6_forward (surface : On a b s root)
    (h : B4TargetV6.Local (v6 roles) a s root frontier) :
    B4TargetV6.Local (v6 roles) b s root frontier := by
  cases h with
  | pending p => exact .pending p
  | inspectionPending known pending rootclear candclear =>
    exact .inspectionPending known ((inspection surface).mp pending) rootclear
      (fun rejected => candclear ((k2 surface).mpr rejected))
  | rejected reason => exact .rejected ((reject_v6 surface).mp reason)
  | ambiguous safe first last different =>
    exact .ambiguous (safe_forward surface safe) ((survivor_iff surface _ _).mp first)
      ((survivor_iff surface _ _).mp last) different
  | selected safe unique clear =>
    exact .selected (safe_forward surface safe) ((unique_iff surface _ _).mp unique)
      (fun conflict => clear ((output_conflict surface _).mpr conflict))

theorem local_v7 (surface : On a b s root) (frontier) :
    B4TargetV7.Local (v7 roles) a s root frontier ↔ B4TargetV7.Local (v7 roles) b s root frontier :=
  B4TargetV7.local_transport (b := v7 roles) (other := v7 roles) (r := a) (rr := b)
    (s := s) (ss := s) (d := root) (dd := root) (fun _ =>
    ⟨local_v6_forward surface,local_v6_forward (symmetric surface)⟩)
    Iff.rfl (priority_v7 surface) frontier

theorem sharing_forward (surface : On a b s root)
    (h : (boundary roles).SharingConflict a s root) :
    (boundary roles).SharingConflict b s root := by
  obtain ⟨key,kids,unique,safe,bad⟩ := h
  exact ⟨key,kids,(unique_iff surface _ _).mp unique,safe_forward surface safe,
    at_key_forward surface _ bad⟩

theorem local_v8 (surface : On a b s root) (frontier) :
    Local a s root frontier ↔ Local b s root frontier :=
  B4TargetV8.local_transport (b := boundary roles) (other := boundary roles) (r := a) (rr := b)
    (s := s) (ss := s) (d := root) (dd := root) (local_v7 surface)
    ⟨sharing_forward surface,sharing_forward (symmetric surface)⟩ (priority_v8 surface) frontier

/-- At any state reached from the true mixed source adapter, unchanged
role-local declaration membership suffices for all V8 local judgments after
keeping the constructor carrier fixed. The tested demand may be any demand,
not necessarily the saturation root. The underlying source state is fixed. -/
theorem reached_local
    (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles)
      sourceReg sourceRoot s)
    (ctors : a.constructors = b.constructors)
    (roster : ∀ d : Declaration, d.role = root.demand.role → (d ∈ a.declarations ↔ d ∈ b.declarations))
    (frontier) :
    GeneralNominalVersionedMixedBoundary234.Local a s root frontier ↔
      GeneralNominalVersionedMixedBoundary234.Local b s root frontier := by
  have owned := (GeneralRebaseMixedOwnedTrace277.adapter_reachable reachable).owns
  exact GeneralNominalVersionedMixedBoundary234.local_iff.trans
    ((local_v8 (surface_of_covered owned ctors roster) frontier).trans
      GeneralNominalVersionedMixedBoundary234.local_iff.symm)

end Yulang.GeneralRebaseRegistryLocal277
