import Yulang.GeneralDeclarativeWitnessJoinedFixture357
import Yulang.GeneralDeclarativeWitnessPolarityFixture357
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
set_option maxHeartbeats 52000000
namespace Yulang.GeneralDeclarativeWitnessVarianceModel357
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty Equivalent Subtype)
open GeneralDeclarativeWitnessJoinedFixture357 (data Data here root written layout test)
open GeneralDeclarativeWitnessJoinedCheck357 (Answer replay replay_rule)
open GeneralDeclarativeWitnessDeclaredState357 (Value Views Current Seen ModelsCurrent authoredRegistry)
open GeneralDeclarativeWitnessClassifyVariance357 (Rule Evidence dictionary_sound)
open GeneralDeclarativeWitnessModeCoverage357 (Coverage check_exact)
open GeneralDeclarativeWitnessModeDeclaration357 (source_ready ready)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open CommonRoleOutermostResolver (Classify Dictionary All₂ Tree Resolves Summarizes Combine)
open PresenceNormalForm (Atom)

inductive Kind where
  | integer | boolean | merged
  deriving DecidableEq

def cat (n : Nat) : Kind := if n = 7 then .integer else if n = 8 then .boolean else .merged
def ty : Kind → Ty
  | .integer => .base .int
  | .boolean => .base .bool
  | .merged => .union (.base .int) (.base .bool)

def model : Assignment := fun n => (ty (cat n),Common.rowEmpty)

def views : Views := fun n =>
  if n = 17 then some ⟨13,20,[.inl (model 7).1]⟩ else
  if n = 18 then some ⟨13,20,[.inl (model 8).1]⟩ else
  if n = 20 then some ⟨13,20,[.inl (model 10).1]⟩ else none

def eqOK (e : Equation) : Bool :=
  match e.right with
  | .variable n => decide (cat e.left = cat n)
  | .join (.variable 7) (.variable 8) => decide (cat e.left = .merged)
  | _ => false

theorem eq_holds {e : Equation} (good : eqOK e = true) : Holds model e := by
  unfold eqOK at good
  split at good
  · rename_i n right
    have same : cat e.left = cat n := of_decide_eq_true good
    change Equivalent (ty (cat e.left)) _
    rw [right]
    change Equivalent (ty (cat e.left)) (ty (cat n))
    rw [same]
    exact eqv_refl _
  · rename_i right
    have same : cat e.left = .merged := of_decide_eq_true good
    change Equivalent (ty (cat e.left)) _
    rw [right,same]
    exact eqv_refl _
  · cases good

def atomOK : Atom Nat → Bool
  | .tyLe (.var a) (.var b) => decide (cat a = cat b)
  | _ => false

theorem atom_holds {a : Atom Nat} (good : atomOK a = true) :
    a.Holds CommonNominalFullCarrier.model model := by
  cases a with
  | rowLe a b => cases good
  | tyLe l r =>
    cases l <;> cases r <;> try cases good
    rename_i n p
    have same : cat n = cat p := of_decide_eq_true good
    change Subtype (ty (cat n)) (ty (cat p))
    rw [same]
    exact (eqv_refl _).1

def evidenceState (s : State) : Bool :=
  s.normal.ordinary.all atomOK &&
    s.normal.intervals.all (fun p => decide (cat p.1 = cat p.2)) &&
    s.equations.all eqOK

theorem data_checked (child : Bool) : ((data child).map (fun d => evidenceState d.current.ordinary)).getD false =
    true := by cases child <;> decide +kernel

theorem fits_data {child : Bool} {d : Data} (obtained : data child = some d) :
    ModelsCurrent d.current model views := by
  have ready_ := data_checked child
  rw [obtained] at ready_
  obtain ⟨facts,eqs⟩ := splitAnd (show evidenceState d.current.ordinary = true from ready_)
  obtain ⟨atoms,intervals⟩ := splitAnd facts
  have source : d.current.visible = here := by
    unfold data at obtained
    cases enc : GeneralDeclarativeWitnessJoinedFixture357.environment child with
    | none => simp [enc] at obtained
    | some e =>
      simp only [enc,Option.bind_eq_bind,Option.bind_some] at obtained
      generalize produced :
        GeneralDeclarativeWitnessCompiler350.execute (GeneralDeclarativeWitnessDeclaredState357.context
          ⟨e,GeneralDeclarativeWitnessJoinedFixture357.initial,here⟩ root
          (GeneralDeclarativeWitnessJoinedFixture357.rootDecl child) layout.named
          (GeneralDeclarativeWitnessDeclaredState357.pointSpans 31 32 10)
          layout.keep layout.fallback layout.via) = run at obtained
      cases run with
      | none => simp at obtained
      | some f => cases Option.some.inj obtained; rfl
  refine ⟨⟨⟨?_,?_⟩,?_⟩,?_⟩
  · intro atom used
    exact atom_holds (List.all_eq_true.mp atoms atom used)
  · intro bound present
    have catSame : cat bound.1 = cat bound.2 := of_decide_eq_true (List.all_eq_true.mp intervals bound present)
    change Subtype (ty (cat bound.1)) (ty (cat bound.2))
    rw [catSame]
    exact (eqv_refl _).1
  · intro row used
    exact eq_holds (List.all_eq_true.mp eqs row used)
  · rw [source]
    intro row used
    simp only [here,List.mem_cons,List.not_mem_nil,or_false] at used
    rcases used with rfl|rfl|rfl <;> exact ⟨_,rfl,rfl,rfl,rfl⟩

theorem leaf_classify {s : Current} {d : GeneralDeclarativeDemand320.Demand} {w}
    (a : Answer s d w) (noChildren : a.kids = []) :
    Classify (Rule s) d (.selected (.node a.impl.id [])) := by
  have found := replay_rule a
  rw [noChildren] at found
  exact ⟨.selected a.impl.id [],.selected found .nil,.selected .nil (.selected rfl)⟩

end Yulang.GeneralDeclarativeWitnessVarianceModel357
