import Yulang.CommonRoleStateMaterializedFrontier
import Yulang.CommonRoleIntervalDictionaryCompilation

/-! Actual ordinary evidence can materialize closed structural Forms, not only int.
The executable detector accepts one distinct syntactic payload, retaining the
original variable on zero or several payloads. This conservative restriction is
an implementation boundary, not semantic completeness or language rejection.
No visible implementation, selected model, fresh name or external head map is
consulted. Future dynamic closure and saturation termination remain separate. -/
namespace Yulang.CommonRoleStructuralOrdinaryMaterialization
open CommonRoleCaptureNormalization (Form)
open Core.PresenceGeneration (TyTerm Comp)
open PresenceNormalForm (Atom All)

/-- The existing Form grammar, restricted to variable-free payloads. -/
def Closed : Form → Prop
  | .var _ => False
  | .int => True
  | .pair a b | .join a b => Closed a ∧ Closed b
  | .tick a => Closed a

/-- Decode only the existing int/pair/union/tick fragment. Other terms stay
unsupported; no regular type is invented to complete a partial description. -/
def decode : TyTerm α → Option Form
  | .base .int => some .int
  | .pair a b => (decode a).bind fun x => (decode b).map (Form.pair x)
  | .union a b => (decode a).bind fun x => (decode b).map (Form.join x)
  | .variant 0 a => (decode a).map Form.tick
  | _ => none

/-- Decoding produces a closed payload with its original all-assignment meaning. -/
theorem decode_spec (t : TyTerm α) (f : Form) (h : decode t = some f)
    (v : α → Comp Common.model) (names : Nat → Common.Ty) :
    Closed f ∧ f.eval names = t.eval Common.model v := by
  induction t generalizing f with
  | base b => cases b <;> simp [decode] at h; subst f; exact ⟨True.intro,rfl⟩
  | pair a b ha hb =>
    simp only [decode,Option.bind_eq_some_iff,Option.map_eq_some_iff] at h
    obtain ⟨x,hx,y,hy,rfl⟩ := h
    obtain ⟨cx,ex⟩ := ha x hx
    obtain ⟨cy,ey⟩ := hb y hy
    exact ⟨⟨cx,cy⟩,by simp [Form.eval,TyTerm.eval,Common.model,ex,ey]⟩
  | union a b ha hb =>
    simp only [decode,Option.bind_eq_some_iff,Option.map_eq_some_iff] at h
    obtain ⟨x,hx,y,hy,rfl⟩ := h
    obtain ⟨cx,ex⟩ := ha x hx
    obtain ⟨cy,ey⟩ := hb y hy
    exact ⟨⟨cx,cy⟩,by simp [Form.eval,TyTerm.eval,Common.model,ex,ey]⟩
  | variant tag a ih =>
    cases tag with
    | zero =>
      obtain ⟨x,hx,rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨cx,ex⟩ := ih x hx
      exact ⟨cx,by simp [Form.eval,TyTerm.eval,Common.model,ex]⟩
    | succ k => simp [decode] at h
  | _ => simp [decode] at h

/-- Every closed existing Form is decoded from its ordinary lowering. -/
theorem decode_lower (slots : Nat → α) (f : Form) (closed : Closed f) :
    decode (CommonRoleIntervalDictionaryCompilation.lower slots f) = some f := by
  induction f with
  | var => contradiction
  | int => rfl
  | pair a b ha hb => simp [CommonRoleIntervalDictionaryCompilation.lower,decode,ha closed.1,hb closed.2]
  | join a b ha hb => simp [CommonRoleIntervalDictionaryCompilation.lower,decode,ha closed.1,hb closed.2]
  | tick a ha => simp [CommonRoleIntervalDictionaryCompilation.lower,decode,ha closed]

def upperHead (slot : Fin n) : Atom (Fin n) → Option Form
  | .tyLe (.var actual) term => if actual = slot then decode term else none
  | _ => none

def lowerHead (slot : Fin n) : Atom (Fin n) → Option Form
  | .tyLe term (.var actual) => if actual = slot then decode term else none
  | _ => none

def upper (atoms : List (Atom (Fin n))) (slot : Fin n) : List Form := atoms.filterMap (upperHead slot)
def lower (atoms : List (Atom (Fin n))) (slot : Fin n) : List Form := atoms.filterMap (lowerHead slot)

/-- Independent source evidence keeps both original term bounds. Decoding is
only their syntactic representation check; no detector or solver is inspected. -/
def Evidence (atoms : List (Atom (Fin n))) (slot : Fin n) (f : Form) : Prop :=
  (∃ t, Atom.tyLe (.var slot) t ∈ atoms ∧ decode t = some f) ∧
    ∃ t, Atom.tyLe t (.var slot) ∈ atoms ∧ decode t = some f

theorem upper_exact (atoms : List (Atom (Fin n))) (slot : Fin n) (f : Form) :
    f ∈ upper atoms slot ↔ ∃ t, Atom.tyLe (.var slot) t ∈ atoms ∧ decode t = some f := by
  simp only [upper,List.mem_filterMap]
  constructor
  · rintro ⟨a,ha,h⟩
    cases a with
    | rowLe _ _ => simp [upperHead] at h
    | tyLe l r =>
      cases l <;> simp only [upperHead] at h
      next actual =>
        split at h
        · rename_i same; subst actual; exact ⟨r,ha,h⟩
        · cases h
      all_goals cases h
  · rintro ⟨t,ht,h⟩; exact ⟨_,ht,by simpa [upperHead] using h⟩

theorem lower_exact (atoms : List (Atom (Fin n))) (slot : Fin n) (f : Form) :
    f ∈ lower atoms slot ↔ ∃ t, Atom.tyLe t (.var slot) ∈ atoms ∧ decode t = some f := by
  simp only [lower,List.mem_filterMap]
  constructor
  · rintro ⟨a,ha,h⟩
    cases a with
    | rowLe _ _ => simp [lowerHead] at h
    | tyLe l r =>
      cases r <;> simp only [lowerHead] at h
      next actual =>
        split at h
        · rename_i same; subst actual; exact ⟨l,ha,h⟩
        · cases h
      all_goals cases h
  · rintro ⟨t,ht,h⟩; exact ⟨_,ht,by simpa [lowerHead] using h⟩

def candidates (atoms : List (Atom (Fin n))) (slot : Fin n) : List Form :=
  (upper atoms slot).filter fun f => (lower atoms slot).contains f

theorem candidates_exact (atoms : List (Atom (Fin n))) (slot : Fin n) (f : Form) :
    f ∈ candidates atoms slot ↔ Evidence atoms slot f := by
  simp [candidates,Evidence,upper_exact,lower_exact]

def detect (atoms : List (Atom (Fin n))) (slot : Fin n) : Option Form :=
  match candidates atoms slot with
  | [] => none
  | f :: rest => if rest.all (fun other => other == f) then some f else none

theorem detect_exact (atoms : List (Atom (Fin n))) (slot : Fin n) (f : Form) :
    detect atoms slot = some f ↔ Evidence atoms slot f ∧
      ∀ other, Evidence atoms slot other → other = f := by
  simp only [← candidates_exact]
  cases eq : candidates atoms slot with
  | nil => simp [detect,eq]
  | cons a rest =>
    have all_iff : rest.all (fun other => other == a) = true ↔ ∀ other ∈ rest, other = a := by simp
    by_cases all : rest.all (fun other => other == a) = true
    · simp only [detect,eq,all,ite_true,Option.some.injEq]
      constructor
      · intro same
        subst f
        exact ⟨by simp,fun other mem => (List.mem_cons.mp mem).elim id ((all_iff.mp all) other)⟩
      · rintro ⟨_,unique⟩; exact unique a (by simp)
    · simp only [detect,eq,all,Bool.false_eq_true,ite_false,reduceCtorEq,false_iff]
      rintro ⟨_,unique⟩
      have af := unique a (by simp)
      apply all
      apply all_iff.mpr
      intro other mem
      exact (unique other (by simp [mem])).trans af.symm

theorem evidence_models (atoms : List (Atom (Fin n))) (slot : Fin n) (f : Form)
    (evidence : Evidence atoms slot f) (v : Fin n → Comp Common.model)
    (models : All Common.model v atoms) (names : Nat → Common.Ty) :
    Closed f ∧ Common.Equivalent (v slot).1 (f.eval names) := by
  obtain ⟨⟨a,ha,da⟩,b,hb,db⟩ := evidence
  obtain ⟨closed,ea⟩ := decode_spec a f da v names
  have eb := (decode_spec b f db v names).2
  exact ⟨closed,by
    constructor
    · rw [ea]; exact models _ ha
    · rw [eb]; exact models _ hb⟩

theorem detect_models (atoms : List (Atom (Fin n))) (slot : Fin n) (f : Form)
    (detected : detect atoms slot = some f) (v : Fin n → Comp Common.model)
    (models : All Common.model v atoms) (names : Nat → Common.Ty) :
    Closed f ∧ Common.Equivalent (v slot).1 (f.eval names) :=
  evidence_models atoms slot f ((detect_exact atoms slot f).mp detected).1 v models names

/-- Deterministic conservative replacement from actual state atoms. -/
def materialize (atoms : List (Atom (Fin n))) (slots : Nat → Fin n) : Form → Form
  | .var name => (detect atoms (slots name)).getD (.var name)
  | .int => .int
  | .pair a b => .pair (materialize atoms slots a) (materialize atoms slots b)
  | .join a b => .join (materialize atoms slots a) (materialize atoms slots b)
  | .tick a => .tick (materialize atoms slots a)

/-- Every model of the actual state preserves the entire original Form meaning. -/
theorem materialize_meaning (atoms : List (Atom (Fin n))) (slots : Nat → Fin n)
    (v : Fin n → Comp Common.model) (models : All Common.model v atoms) (f : Form) :
    Common.Equivalent ((materialize atoms slots f).eval (fun k => (v (slots k)).1))
      (f.eval (fun k => (v (slots k)).1)) := by
  induction f with
  | var name =>
    cases h : detect atoms (slots name) with
    | none => simp only [materialize,h,Option.getD_none]; exact Common.equivalent_refl _
    | some a =>
      simp only [materialize,h,Option.getD_some,Form.eval]
      exact Common.equivalent_symm (detect_models atoms (slots name) a h v models _).2
  | int => exact Common.equivalent_refl _
  | pair a b ha hb => exact (CommonCanonicalShapes.pair_equivalent_iff _ _ _ _).mpr ⟨ha,hb⟩
  | join a b ha hb => exact CommonRoleCaptureNormalization.join_congr _ _ _ _ ha hb
  | tick a ha => exact (CommonCanonicalShapes.variant_equivalent_iff 0 _ _).mpr ha

/-- Closed payloads are stable under every state, including inconsistent states. -/
theorem materialize_closed (atoms : List (Atom (Fin n))) (slots : Nat → Fin n)
    (f : Form) (closed : Closed f) : materialize atoms slots f = f := by
  induction f with
  | var => contradiction
  | int => rfl
  | pair a b ha hb => simp [materialize,ha closed.1,hb closed.2]
  | join a b ha hb => simp [materialize,ha closed.1,hb closed.2]
  | tick a ha => simp [materialize,ha closed]

/-- Idempotence at one state is not a saturation stopping condition. -/
theorem materialize_idempotent (atoms : List (Atom (Fin n))) (slots : Nat → Fin n) (f : Form) :
    materialize atoms slots (materialize atoms slots f) = materialize atoms slots f := by
  induction f with
  | var name =>
    cases h : detect atoms (slots name) with
    | none => simp [materialize,h]
    | some a =>
      obtain ⟨⟨t,ht,decoded⟩,_⟩ := ((detect_exact atoms (slots name) a).mp h).1
      have closed := (decode_spec t a decoded (fun _ => Comp.pure Common.model (.base .int))
        (fun _ => .base .int)).1
      simpa only [materialize,h,Option.getD_some] using materialize_closed atoms slots a closed
  | int => rfl
  | pair a b ha hb => simp [materialize,ha,hb]
  | join a b ha hb => simp [materialize,ha,hb]
  | tick a ha => simp [materialize,ha]

/-- No candidate order or repeated atom can change the conservative detector. -/
theorem detect_congr (before after : List (Atom (Fin n)))
    (same : ∀ a, a ∈ before ↔ a ∈ after) (slot : Fin n) :
    detect before slot = detect after slot := by
  apply Option.ext
  intro f
  simp only [detect_exact,Evidence,same]

theorem materialize_congr (before after : List (Atom (Fin n)))
    (same : ∀ a, a ∈ before ↔ a ∈ after) (slots : Nat → Fin n) (f : Form) :
    materialize before slots f = materialize after slots f := by
  induction f <;> simp_all [materialize,detect_congr before after same]

def materializeGoal (atoms : List (Atom (Fin n))) (slots : Nat → Fin n)
    (goal : CommonRoleIntervalPaterson.Goal) : CommonRoleIntervalPaterson.Goal :=
  ⟨goal.role,goal.arguments.map fun p => (materialize atoms slots p.1,materialize atoms slots p.2)⟩

/-- Reuse the actual checked structural frontier and common graph compiler. -/
def run (registry : List CommonRoleStablePaterson.Declaration) (slots : Nat → Fin n)
    (sources : CommonRoleGuardedIntervalPlans.Sources) (atoms : List (Atom (Fin n)))
    (old : CommonRoleGuardedIntervalPlans.Plan (Fin n)) (goal : CommonRoleIntervalPaterson.Goal) :=
  CommonRoleFrontierGraphs.run registry slots sources atoms old (materializeGoal atoms slots goal)

/-- Every model of every emitted ordinary graph retains the original state and
all original Form meanings, while satisfying the independent regenerated frontier.
The frontier judgment is for the materialized goal; equality of syntactic candidate
sets before materialization is neither assumed nor concluded. -/
theorem run_graph_reflects (registry : List CommonRoleStablePaterson.Declaration)
    (slots : Nat → Fin n) (sources : CommonRoleGuardedIntervalPlans.Sources)
    (atoms : List (Atom (Fin n))) (old : CommonRoleGuardedIntervalPlans.Plan (Fin n))
    (goal : CommonRoleIntervalPaterson.Goal) (output)
    (returned : run registry slots sources atoms old goal = some output)
    (graph : CommonPresenceConstraintGraph.Compiled n) (member : graph ∈ output.2)
    (rows : Fin n → Common.Row) (values : Fin graph.size → Common.Ty)
    (models : graph.Models rows values) :
    let v := graph.readback rows values
    CommonRoleIntervalWorkClosure.Checked registry ∧ All Common.model v atoms ∧
      (∀ f, Common.Equivalent ((materialize atoms slots f).eval (fun k => (v (slots k)).1))
        (f.eval (fun k => (v (slots k)).1))) ∧
      ∃ sourceValues, CommonRoleCaptureBatchModels.SharedFits v sourceValues old ∧
        CommonRoleGuardedIntervalPlans.Derives registry slots sources v sourceValues
          (materializeGoal atoms slots goal) := by
  have reflected := CommonRoleFrontierGraphs.graph_reflects registry slots sources atoms old
    (materializeGoal atoms slots goal) output returned graph member rows values models
  exact ⟨reflected.1,reflected.2.1,
    fun f => materialize_meaning atoms slots _ reflected.2.1 f,reflected.2.2⟩

end Yulang.CommonRoleStructuralOrdinaryMaterialization
