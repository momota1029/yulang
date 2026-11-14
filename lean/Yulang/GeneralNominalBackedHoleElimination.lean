import Yulang.GeneralNominalSourceHoleExposure

/-! An occurs check for a finite readback whose branches are backed by the
actual K2 graph. The current hole set can already be smaller than the source
frontier. Semantic equality alone is not used to manufacture graph edges. -/
namespace Yulang.GeneralNominalBackedHoleElimination
open GeneralNominalOriginTerms GeneralNominalRecursiveInspection GeneralNominalHoleElimination
open GeneralNominalIndexedHoleReadback GeneralNominalFeedbackK2 GeneralNominalSaturationState
open GeneralNominalActualInspectionSteps GeneralNominalSharedEnumeration

variable {roles : Roles.RoleDecls}

inductive Backed (state : State roles) (identities : Nat → Nat) : Nat → Expr Nat → Prop
  | leaf : Equal state root (identities name) → Backed state identities root (.leaf name)
  | node (test : Test) (children : Fin (arity test) → Expr Nat) (sources : Fin (arity test) → Nat) :
      (∀ position, Edge state root (sources position)) →
      (∀ position, Backed state identities (sources position) (children position)) →
      Backed state identities root (.node test children)

theorem equal_symm (equal : Equal state first last) : Equal state last first :=
  fun model valid => ⟨(equal model valid).2,(equal model valid).1⟩

theorem edge_equal_target (edge : Edge state first middle) (equal : Equal state middle last)
    (member : last ∈ GeneralNominalState.sources state.context.state) : Edge state first last := by
  refine ⟨edge.1,member,?_⟩
  rcases edge.2.2 with structural | argument
  · obtain ⟨parent,child,recorded,one,two⟩ := structural
    exact Or.inl ⟨parent,child,recorded,one,equal_trans two equal⟩
  · exact Or.inr (argument_equal_target argument equal)

theorem path_equal_target (edge : Edge state first middle) (path : Path state middle last)
    (equal : Equal state last target)
    (member : target ∈ GeneralNominalState.sources state.context.state) :
    ∃ next, Edge state first next ∧ Path state next target := by
  induction path generalizing first with
  | nil => exact ⟨target,edge_equal_target edge equal member,.nil _⟩
  | cons step path ih =>
    obtain ⟨next,one,two⟩ := ih step equal
    exact ⟨_,edge,.cons one two⟩

theorem backed_path (backed : Backed state identities root term) (present : hole ∈ term.leaves) :
    ∃ last, Path state root last ∧ Equal state last (identities hole) := by
  induction backed with
  | leaf equal =>
    cases List.mem_singleton.mp present
    exact ⟨_,.nil _,equal⟩
  | node test children sources edges backed ih =>
    obtain ⟨parts,listed,member⟩ := List.mem_flatten.mp present
    obtain ⟨position,rfl⟩ := List.mem_ofFn.mp listed
    obtain ⟨last,path,equal⟩ := ih position member
    exact ⟨last,.cons (edges position) path,equal⟩

theorem occurs_cycle (backed : Backed state identities root (.node test children))
    (same : Equal state root (identities hole))
    (present : hole ∈ (Expr.node test children).leaves) : Cycle state root := by
  cases backed with
  | node test children sources edges backed =>
    obtain ⟨parts,listed,member⟩ := List.mem_flatten.mp present
    obtain ⟨position,rfl⟩ := List.mem_ofFn.mp listed
    obtain ⟨last,path,equal⟩ := backed_path (backed position) member
    exact path_equal_target (edges position) path (equal_trans equal (equal_symm same)) (edges position).1

theorem occurs_rejected (backed : Backed state identities root (.node test children))
    (same : Equal state root (identities hole))
    (present : hole ∈ (Expr.node test children).leaves)
    (inhabited : ∃ model, Models state model) : RecursAt state root :=
  ⟨occurs_cycle backed same present,inhabited⟩

theorem tested_occurrence_blocks {state : GeneralNominalSupport.Tracked roles}
    (member : (observed,tested) ∈ (inspection state.current packet).tests)
    (located : Represents state.current observed root)
    (backed : Backed state.current identities root (.node test children))
    (same : Equal state.current root (identities hole))
    (present : hole ∈ (Expr.node test children).leaves)
    (inhabited : ∃ model, Models state.current model) :
    ¬ PacketGuard state packet support :=
  tested_cycle_blocks member ⟨root,located,occurs_rejected backed same present inhabited⟩

/-- A supported constructor readback at an inspected safe source cannot
contain its own hole, even through several materialized graph positions. -/
theorem safe_closed (backed : Backed state identities root (.node test children))
    (same : Equal state root (identities hole))
    (inhabited : ∃ model, Models state model)
    (safe : ¬ RecursAt state root)
    (closed : Closed remaining (.node test children)) :
    Closed (remaining.erase hole) (.node test children) := by
  intro name member
  apply (List.mem_erase_of_ne ?_).mpr (closed name member)
  intro equal
  subst name
  exact safe (occurs_rejected backed same member inhabited)

/-- A uniform expansion at the observed origin replaces its old shared leaf
at the fixed original origin; the frontier is never reset to the later state. -/
theorem readback_at_hole (step : Step registry focus before after)
    (old : Readback (Models before.current) origins remaining observed (.leaf hole))
    (expanded : Readback (Models after.current) origins remaining observed value)
    (absent : hole ∉ value.leaves) :
    Readback (Models after.current) origins (remaining.erase hole) (origins hole) value := by
  have prior := step_preserves step old
  refine ⟨?_,?_⟩
  · intro model valid
    exact holds_transport (prior.1 model valid) (expanded.1 model valid)
  · intro name member
    apply (List.mem_erase_of_ne ?_).mpr (expanded.2 name member)
    intro same
    subst name
    exact absent member

/-- Every already represented origin, including captures and output origins,
is updated simultaneously once this local replacement has been established. -/
theorem actual_expansion {represented : Origin → Expr Nat → Prop}
    (step : Step registry focus before after)
    (old : Readback (Models before.current) origins remaining observed (.leaf hole))
    (expanded : Readback (Models after.current) origins remaining observed value)
    (absent : hole ∉ value.leaves)
    (readbacks : ∀ root term, represented root term → Readback (Models before.current) origins remaining root term) :
    hole ∈ remaining ∧
    ∀ root term, represented root term →
      Readback (Models after.current) origins (remaining.erase hole) root (replace hole value term) :=
  ⟨old.2 hole (List.mem_singleton_self _),
    actual_elimination step readbacks (readback_at_hole step old expanded absent)⟩

theorem backed_expansion {represented : Origin → Expr Nat → Prop}
    (step : Step registry focus before after)
    (old : Readback (Models before.current) origins remaining observed (.leaf hole))
    (expanded : Readback (Models after.current) origins remaining observed (.node test children))
    (backed : Backed after.current identities actual (.node test children))
    (same : Equal after.current actual (identities hole))
    (inhabited : ∃ model, Models after.current model)
    (safe : ¬ RecursAt after.current actual)
    (readbacks : ∀ root term, represented root term → Readback (Models before.current) origins remaining root term) :
    hole ∈ remaining ∧
    ∀ root term, represented root term →
      Readback (Models after.current) origins (remaining.erase hole) root (replace hole (.node test children) term) :=
  actual_expansion step old expanded
    (fun present => safe (occurs_rejected backed same present inhabited)) readbacks

end Yulang.GeneralNominalBackedHoleElimination
