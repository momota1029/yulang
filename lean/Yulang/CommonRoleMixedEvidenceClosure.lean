import Yulang.CommonRoleFiniteAssociatedDeclaration
import Yulang.CommonRoleEvidenceReplay

/-! One finite closure alternates actual associated outputs and reciprocal-edge
scalar transfer. The source graph and slot universe remain explicit inputs.
No dynamic child generation or general ordinary entailment is claimed. -/
namespace Yulang.CommonRoleMixedEvidenceClosure
open CommonRoleSettledConstraints (State)
open CommonRoleFiniteAssociatedClosure (Source Occurrence Fact request)
open CommonRoleOrdinaryKnownness (Evidence)
open CommonRoleEvidenceSaturation (Linked)
open CommonRoleAssociatedDeclarationExact (DeclarativeComputed)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All Atom)

/-- No executable resolver or cache occurs in this independent judgment. -/
inductive Derives (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (p : Source n) (s : State n) : Fact n → Prop
  | initial {i b} : Evidence s.atoms i b → Derives env roles p s (i,b)
  | identity {i j b} : p.identity i = p.identity j →
      Derives env roles p s (i,b) → Derives env roles p s (j,b)
  | transfer {i j b} : Linked s i j →
      Derives env roles p s (j,b) → Derives env roles p s (i,b)
  | associated {q head output} : q ∈ p.occurrences →
      Derives env roles p s (q.receiver,head) →
      DeclarativeComputed env roles (request q head) output →
      Derives env roles p s (q.output,output)

def rules (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n) :=
  CommonRoleFiniteAssociatedClosure.rules env roles wf p s ++
    CommonRoleEvidenceSaturation.rules s

def saturate (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n) : List (Fact n) :=
  FiniteHorn.saturate (rules env roles wf p s) (CommonRoleEvidenceSaturation.facts n)

private theorem rules_valid (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Source n) (s : State n) :
    ∀ rule ∈ rules env roles wf p s, FiniteHorn.Valid (Derives env roles p s) rule := by
  intro rule member premises
  rcases List.mem_append.mp member with assoc | ordinary
  · rcases List.mem_append.mp assoc with earlier | assoc
    · rcases List.mem_append.mp earlier with init | identities
      · obtain ⟨⟨i,b⟩,present,rfl⟩ := List.mem_map.mp init
        exact .initial ((CommonRoleFiniteAssociatedClosure.initial_exact ..).mp present)
      · obtain ⟨i,_,member⟩ := List.mem_flatMap.mp identities
        obtain ⟨j,_,member⟩ := List.mem_flatMap.mp member
        split at member
        · rename_i same
          obtain ⟨b,_,rfl⟩ := List.mem_map.mp member
          exact .identity same (premises _ (by simp [CommonRoleFiniteAssociatedClosure.unary]))
        · simp at member
    · obtain ⟨q,qmem,present⟩ := List.mem_flatMap.mp assoc
      obtain ⟨head,_,result⟩ := List.mem_filterMap.mp present
      obtain ⟨output,computed,rfl⟩ := Option.map_eq_some_iff.mp result
      exact .associated qmem (premises _ (by simp [CommonRoleFiniteAssociatedClosure.unary]))
        ((CommonRoleAssociatedDeclarationExact.computed_iff_declarative env roles wf awf ..).mp
          ((CommonRoleAssociatedStateFlow.value_exact ..).mp computed))
  · rcases List.mem_append.mp ordinary with seeds | transfer
    · obtain ⟨⟨i,b⟩,present,rfl⟩ := List.mem_map.mp seeds
      exact .initial ((CommonRoleEvidenceSaturation.seeds_exact ..).mp present)
    · obtain ⟨i,_,member⟩ := List.mem_flatMap.mp transfer
      obtain ⟨⟨j,b⟩,filtered,rfl⟩ := List.mem_map.mp member
      exact .transfer ((CommonRoleEvidenceSaturation.edge_exact ..).mp
        (List.mem_filter.mp filtered).2)
        (premises _ (by simp [CommonRoleEvidenceSaturation.transferRule]))

/-- Every enabled rule belongs to a fixed finite fact universe. -/
theorem saturate_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Source n) (s : State n) (f : Fact n) :
    f ∈ saturate env roles wf p s ↔ Derives env roles p s f := by
  constructor
  · exact FiniteHorn.saturate_preserves _ _ _ (rules_valid env roles wf awf p s) f
  · intro derived
    induction derived with
    | @initial i b evidence =>
      apply FiniteHorn.saturate_closed _ _ CommonRoleEvidenceSaturation.facts_complete
      refine ⟨CommonRoleEvidenceSaturation.seedRule (i,b), ?_, rfl, ?_⟩
      · apply List.mem_append_right
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨(i,b),(CommonRoleEvidenceSaturation.seeds_exact ..).mpr evidence,rfl⟩
      · simp [CommonRoleEvidenceSaturation.seedRule]
    | @identity i j b same _ ih =>
      apply FiniteHorn.saturate_closed _ _ CommonRoleEvidenceSaturation.facts_complete
      refine ⟨CommonRoleFiniteAssociatedClosure.unary (i,b) (j,b), ?_, rfl, ?_⟩
      · apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_right
        apply List.mem_flatMap.mpr
        refine ⟨i,by simp, List.mem_flatMap.mpr ⟨j,by simp,?_⟩⟩
        simp only [same, ↓reduceIte]
        apply List.mem_map.mpr
        refine ⟨b,?_,rfl⟩
        cases b <;> simp [CommonRoleFiniteAssociatedClosure.bases]
      · simpa [CommonRoleFiniteAssociatedClosure.unary,saturate] using ih
    | @transfer i j b linked _ ih =>
      apply FiniteHorn.saturate_closed _ _ CommonRoleEvidenceSaturation.facts_complete
      refine ⟨CommonRoleEvidenceSaturation.transferRule i (j,b), ?_, rfl, ?_⟩
      · apply List.mem_append_right
        apply List.mem_append_right
        apply List.mem_flatMap.mpr
        refine ⟨i,by simp,List.mem_map.mpr ⟨(j,b),?_,rfl⟩⟩
        exact List.mem_filter.mpr ⟨CommonRoleEvidenceSaturation.facts_complete _,
          (CommonRoleEvidenceSaturation.edge_exact ..).mpr linked⟩
      · simpa [CommonRoleEvidenceSaturation.transferRule,saturate] using ih
    | @associated q head output member _ computed ih =>
      apply FiniteHorn.saturate_closed _ _ CommonRoleEvidenceSaturation.facts_complete
      refine ⟨CommonRoleFiniteAssociatedClosure.unary (q.receiver,head) (q.output,output), ?_, rfl, ?_⟩
      · apply List.mem_append_left
        apply List.mem_append_right
        apply List.mem_flatMap.mpr
        refine ⟨q,member,List.mem_filterMap.mpr ⟨head,?_,?_⟩⟩
        · cases head <;> simp [CommonRoleFiniteAssociatedClosure.bases]
        · rw [(CommonRoleAssociatedStateFlow.value_exact ..).mpr
            ((CommonRoleAssociatedDeclarationExact.computed_iff_declarative env roles wf awf ..).mpr computed)]
          rfl
      · simpa [CommonRoleFiniteAssociatedClosure.unary,saturate] using ih

theorem saturate_bounded (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n) :
    (saturate env roles wf p s).length ≤ n * 4 := by
  rw [← CommonRoleEvidenceSaturation.facts_length]
  exact FiniteHorn.saturate_length_le _ _ CommonRoleEvidenceSaturation.facts_complete

theorem saturate_nodup (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n) :
    (saturate env roles wf p s).Nodup := FiniteHorn.saturate_nodup ..

theorem saturate_stopped (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n) :
    FiniteHorn.firstFresh (rules env roles wf p s) (saturate env roles wf p s)
      (CommonRoleEvidenceSaturation.facts n) = none := by
  apply (FiniteHorn.firstFresh_none_iff ..).mpr
  intro f _ enabled
  exact FiniteHorn.saturate_closed _ _ CommonRoleEvidenceSaturation.facts_complete f enabled

def completed (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n) : State n :=
  CommonRoleFiniteAssociatedModels.emit (saturate env roles wf p s) s

/-- Associated equations may narrow models; every resulting constraint is explicit. -/
theorem completed_models (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Source n) (s : State n) (v : Fin n → Comp Common.model) :
    All Common.model v (completed env roles wf p s).atoms ↔
      All Common.model v s.atoms ∧ ∀ f, Derives env roles p s f →
        Common.Equivalent (v f.1).1 (.base f.2) := by
  rw [completed,CommonRoleFiniteAssociatedModels.emit_models]
  simp only [saturate_exact env roles wf awf]

theorem completed_evidence (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Source n) (s : State n) (i : Fin n) (b : Inference.Base) :
    Evidence (completed env roles wf p s).atoms i b ↔ Derives env roles p s (i,b) := by
  rw [completed,CommonRoleFiniteAssociatedStable.emit_evidence,saturate_exact env roles wf awf]
  exact ⟨fun h => h.elim Derives.initial id,Or.inr⟩

private theorem emit_linked (fs : List (Fact n)) (s : State n) (i j : Fin n) :
    Linked (CommonRoleFiniteAssociatedModels.emit fs s) i j ↔ Linked s i j := by
  induction fs generalizing s with
  | nil => rfl
  | cons f fs ih =>
    rcases f with ⟨k,b⟩
    rw [CommonRoleFiniteAssociatedModels.emit,ih]
    simp [Linked,CommonRoleCandidateStateFrontier.extend,CommonRoleCandidateStateFrontier.equality]

theorem completed_linked (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (p : Source n) (s : State n) (i j : Fin n) :
    Linked (completed env roles wf p s) i j ↔ Linked s i j := emit_linked ..

/-- All alternations, including cyclic source/ordinary dependencies, are closed. -/
theorem completed_derived (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Source n) (s : State n) (f : Fact n) :
    Derives env roles p (completed env roles wf p s) f ↔ Derives env roles p s f := by
  constructor
  · intro derived
    induction derived with
    | initial evidence => exact (completed_evidence env roles wf awf ..).mp evidence
    | identity same _ ih => exact .identity same ih
    | transfer linked _ ih => exact .transfer ((completed_linked ..).mp linked) ih
    | associated member _ computed ih => exact .associated member ih computed
  · intro derived
    exact .initial ((completed_evidence env roles wf awf ..).mpr derived)

theorem completed_fixedpoint (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Source n) (s : State n) (f : Fact n) :
    f ∈ saturate env roles wf p (completed env roles wf p s) ↔
      f ∈ saturate env roles wf p s := by
  rw [saturate_exact env roles wf awf,completed_derived env roles wf awf,
    saturate_exact env roles wf awf]

/-- Source occurrence order and duplication do not change this mixed closure. -/
theorem derives_order_independent (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (p q : Source n) (s : State n)
    (same : CommonRoleFiniteAssociatedModels.SameSource p q) (f : Fact n) :
    Derives env roles p s f ↔ Derives env roles q s f := by
  constructor
  · intro derived
    induction derived with
    | initial evidence => exact .initial evidence
    | identity equal _ ih => exact .identity ((same.1 ..).mp equal) ih
    | transfer linked _ ih => exact .transfer linked ih
    | associated member _ computed ih => exact .associated ((same.2 _).mp member) ih computed
  · intro derived
    induction derived with
    | initial evidence => exact .initial evidence
    | identity equal _ ih => exact .identity ((same.1 ..).mpr equal) ih
    | transfer linked _ ih => exact .transfer linked ih
    | associated member _ computed ih => exact .associated ((same.2 _).mpr member) ih computed

theorem completed_models_order_independent (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p q : Source n) (s : State n)
    (same : CommonRoleFiniteAssociatedModels.SameSource p q) (v : Fin n → Comp Common.model) :
    All Common.model v (completed env roles wf p s).atoms ↔
      All Common.model v (completed env roles wf q s).atoms := by
  rw [completed_models env roles wf awf,completed_models env roles wf awf]
  simp only [derives_order_independent env roles p q s same]

end Yulang.CommonRoleMixedEvidenceClosure
