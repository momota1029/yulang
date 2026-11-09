import Yulang.CommonRoleEvidenceSaturation

/-! Directed scalar bounds, with independent upper/lower propagation.
This finite fragment does not decide general semantic implication. -/
namespace Yulang.CommonRoleDirectedBounds
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All Atom)
open CommonRoleSettledConstraints (State)
open CommonRoleOrdinaryKnownness (upper lower upper_exact lower_exact)
open CommonRoleDiagnosticEvidenceTransfer (edgeTest edgeTest_exact)

abbrev Fact (n : Nat) := Bool × (Fin n × Inference.Base)
def facts (n : Nat) : List (Fact n) :=
  [true,false].flatMap fun side =>
    (CommonRoleEvidenceSaturation.facts n).map fun f => (side,f)
theorem facts_complete (f : Fact n) : f ∈ facts n := by
  rcases f with ⟨side,f⟩
  cases side <;> simp [facts, CommonRoleEvidenceSaturation.facts_complete]
theorem facts_length (n : Nat) : (facts n).length = n * 8 := by
  simp [facts, CommonRoleEvidenceSaturation.facts_length]
  omega

def atom (f : Fact n) : Atom (Fin n) :=
  if f.1 then .tyLe (.var f.2.1) (.base f.2.2)
  else .tyLe (.base f.2.2) (.var f.2.1)
def seedTest (s : State n) (f : Fact n) : Bool :=
  if f.1 then (upper s.atoms f.2.1).contains f.2.2
  else (lower s.atoms f.2.1).contains f.2.2
theorem seedTest_exact (s : State n) (f : Fact n) :
    seedTest s f = true ↔ atom f ∈ s.atoms := by
  rcases f with ⟨side,i,b⟩
  cases side <;> simp [seedTest, atom, upper_exact, lower_exact]
def edge (s : State n) (side : Bool) (i j : Fin n) : Bool :=
  if side then s.atoms.any (edgeTest i j) else s.atoms.any (edgeTest j i)
def Linked (s : State n) (side : Bool) (i j : Fin n) : Prop :=
  if side then Atom.tyLe (.var i) (.var j) ∈ s.atoms
  else Atom.tyLe (.var j) (.var i) ∈ s.atoms
theorem edge_exact (s : State n) (side : Bool) (i j : Fin n) :
    edge s side i j = true ↔ Linked s side i j := by
  cases side <;> simp [edge, Linked, List.any_eq_true, edgeTest_exact]
def seedRule (f : Fact n) : FiniteHorn.Rule (Fact n) := ⟨[],f⟩
def transferRule (i : Fin n) (f : Fact n) : FiniteHorn.Rule (Fact n) :=
  ⟨[f],(f.1,i,f.2.2)⟩
def transfers (s : State n) (i : Fin n) : List (FiniteHorn.Rule (Fact n)) :=
  ((facts n).filter fun f => edge s f.1 i f.2.1).map (transferRule i)
def rules (s : State n) : List (FiniteHorn.Rule (Fact n)) :=
  ((facts n).filter (seedTest s)).map seedRule ++ (List.finRange n).flatMap (transfers s)
def saturate (s : State n) : List (Fact n) := FiniteHorn.saturate (rules s) (facts n)
inductive Derived (s : State n) : Fact n → Prop where
  | seed : atom f ∈ s.atoms → Derived s f
  | transfer : Linked s side i j → Derived s (side,j,b) → Derived s (side,i,b)

theorem saturate_capacity (s : State n) : (saturate s).length ≤ n * 8 := by
  rw [← facts_length]
  exact FiniteHorn.saturate_length_le _ _ facts_complete

theorem saturate_seed (s : State n) (h : atom f ∈ s.atoms) : f ∈ saturate s := by
  apply FiniteHorn.saturate_closed _ _ facts_complete
  exact ⟨seedRule f, List.mem_append_left _
    (List.mem_map.mpr ⟨f,List.mem_filter.mpr ⟨facts_complete _,(seedTest_exact ..).mpr h⟩,rfl⟩),rfl,by simp [seedRule]⟩
theorem saturate_transfer (s : State n) (h : Linked s side i j)
    (present : (side,j,b) ∈ saturate s) : (side,i,b) ∈ saturate s := by
  apply FiniteHorn.saturate_closed _ _ facts_complete
  refine ⟨transferRule i (side,j,b), List.mem_append_right _ ?_, rfl, ?_⟩
  · apply List.mem_flatMap.mpr
    refine ⟨i,List.mem_finRange _,List.mem_map.mpr ⟨(side,j,b),?_,rfl⟩⟩
    exact List.mem_filter.mpr ⟨facts_complete _,(edge_exact ..).mpr h⟩
  · simpa [transferRule,saturate] using present

theorem rules_derived (s : State n) :
    ∀ rule ∈ rules s, FiniteHorn.Valid (Derived s) rule := by
  intro rule member premises
  rcases List.mem_append.mp member with hs | ht
  · obtain ⟨f,h,rfl⟩ := List.mem_map.mp hs
    exact .seed ((seedTest_exact ..).mp (List.mem_filter.mp h).2)
  · obtain ⟨i,_,h⟩ := List.mem_flatMap.mp ht
    unfold transfers at h
    obtain ⟨⟨side,j,b⟩,filtered,same⟩ := List.mem_map.mp h
    subst rule
    exact .transfer ((edge_exact ..).mp (List.mem_filter.mp filtered).2)
      (premises (side,j,b) (by simp [transferRule]))
theorem saturate_exact (s : State n) (f : Fact n) :
    f ∈ saturate s ↔ Derived s f := by
  constructor
  · exact FiniteHorn.saturate_preserves _ _ _ (rules_derived s) f
  · intro h
    induction h with
    | seed h => exact saturate_seed s h
    | transfer h _ ih => exact saturate_transfer s h ih

theorem saturate_stopped (s : State n) :
    FiniteHorn.firstFresh (rules s) (saturate s) (facts n) = none := by
  apply (FiniteHorn.firstFresh_none_iff ..).mpr
  intro f _ h
  exact FiniteHorn.saturate_closed _ _ facts_complete f h

theorem derived_models (s : State n) (f : Fact n) (h : Derived s f)
    (a : Fin n → Comp Common.model) (models : All Common.model a s.atoms) :
    Atom.Holds Common.model a (atom f) := by
  induction h with
  | seed h => exact models _ h
  | @transfer side i j b linked _ ih =>
    cases side
    · exact Common.subtype_trans ih (models _ linked)
    · exact Common.subtype_trans (models _ linked) ih

theorem saturate_least (s : State n) (P : Fact n → Prop)
    (seed : ∀ f, atom f ∈ s.atoms → P f)
    (transfer : ∀ side i j b, Linked s side i j → P (side,j,b) → P (side,i,b)) :
    ∀ f ∈ saturate s, P f := by
  intro f h
  have d := (saturate_exact s f).mp h
  clear h
  induction d with
  | seed evidence => exact seed _ evidence
  | transfer linked _ ih => exact transfer _ _ _ _ linked ih

theorem atom_in_equality (f : Fact n) : atom f ∈
    CommonRoleCandidateStateFrontier.equality f.2.1 f.2.2 := by
  rcases f with ⟨side,i,b⟩
  cases side <;> simp [atom,CommonRoleCandidateStateFrontier.equality]

theorem bounds_grammar (fs : List (Fact n)) :
    PresenceGeneratedChildGrammar.GoodAtoms (fs.map atom) ∧
    PresenceGeneratedWidth.WidthAtoms (fs.map atom) ∧
    PresenceSourceConstraintSupport.GoodAtoms (fs.map atom) := by
  refine ⟨?_,?_,?_⟩
  · intro a h
    obtain ⟨f,_,rfl⟩ := List.mem_map.mp h
    exact (CommonRoleCandidateStateFrontier.equality_grammar f.2.1 f.2.2).1 _ (atom_in_equality f)
  · intro left right h
    obtain ⟨f,_,hf⟩ := List.mem_map.mp h
    rcases f with ⟨side,i,b⟩
    cases side <;> simp only [atom, Bool.false_eq_true, ↓reduceIte] at hf
    all_goals cases hf; intro tail needed; cases needed
  · intro a h
    obtain ⟨f,_,rfl⟩ := List.mem_map.mp h
    exact (CommonRoleCandidateStateFrontier.equality_grammar f.2.1 f.2.2).2.2 _ (atom_in_equality f)

/-- Append sound bounds, including single-sided ones. -/
def normalize (s : State n) : State n :=
  let g := bounds_grammar (saturate s)
  ⟨s.atoms ++ (saturate s).map atom,s.child.append g.1,
    s.width.append g.2.1,s.rows.append g.2.2⟩
theorem normalize_models (s : State n) (a : Fin n → Comp Common.model) :
    All Common.model a (normalize s).atoms ↔ All Common.model a s.atoms := by
  rw [normalize, PresenceNormalForm.all_append]
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    intro bound member
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp member
    exact derived_models s f ((saturate_exact s f).mp hf) a h

theorem atom_injective : Function.Injective (atom : Fact n → Atom (Fin n)) := by
  rintro ⟨side,i,b⟩ ⟨side',j,c⟩ h
  cases side <;> cases side' <;> simp [atom] at h ⊢ <;> simp_all [and_comm]

theorem normalize_bound (s : State n) (f : Fact n) :
    atom f ∈ (normalize s).atoms ↔ Derived s f := by
  simp only [normalize, List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨g,hg,eq⟩)
    · exact .seed h
    · have same := atom_injective eq
      subst g
      exact (saturate_exact s f).mp hg
  · intro h
    exact Or.inr ⟨f,(saturate_exact s f).mpr h,rfl⟩

theorem normalize_evidence (s : State n) (i : Fin n) (b : Inference.Base) :
    CommonRoleOrdinaryKnownness.Evidence (normalize s).atoms i b ↔
      Derived s (true,i,b) ∧ Derived s (false,i,b) := by
  change atom (true,i,b) ∈ (normalize s).atoms ∧
    atom (false,i,b) ∈ (normalize s).atoms ↔ _
  rw [normalize_bound, normalize_bound]

theorem normalize_linked (s : State n) (side : Bool) (i j : Fin n) :
    Linked (normalize s) side i j ↔ Linked s side i j := by
  cases side <;> simp [Linked, normalize, atom]

theorem normalize_derived (s : State n) (f : Fact n) :
    Derived (normalize s) f ↔ Derived s f := by
  constructor
  · intro h
    induction h with
    | seed h => exact (normalize_bound ..).mp h
    | transfer h _ ih => exact .transfer ((normalize_linked ..).mp h) ih
  · intro h
    exact .seed ((normalize_bound ..).mpr h)

theorem saturate_fixedpoint (s : State n) (f : Fact n) :
    f ∈ saturate (normalize s) ↔ f ∈ saturate s := by
  rw [saturate_exact, normalize_derived, saturate_exact]

theorem materializes_int (s : State n) (i : Fin n)
    (hu : Derived s (true,i,.int)) (hl : Derived s (false,i,.int))
    (a : Fin n → Comp Common.model) (models : All Common.model a s.atoms) :
    CommonRoleOrdinaryKnownness.materialize (normalize s).atoms i = some Roles.Examples.int :=
  CommonRoleMaterializedDomain.evidence_int_materializes _ i a
    ((normalize_models s a).mpr models) ((normalize_evidence ..).mpr ⟨hu,hl⟩)

end Yulang.CommonRoleDirectedBounds
