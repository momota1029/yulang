import Yulang.GeneralStoppedShape335
import Yulang.GeneralNominalRebaseRawView243
import Yulang.GeneralDeclarativeOrigins321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralStoppedLower335
open GeneralNominalState (State Descriptor Denotes)
open Core.PresenceGeneration (CompTerm TyTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseRawView243 (atom all_exact slot)
open GeneralDeclarativeHead320 (Equation Models environment)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralStoppedShape335 (headExpr descriptorExpr head_semantics descriptor_semantics)
open CommonNominalFullCarrier (Equivalent Subtype)
open GeneralDeclarativeOrigins321 (Supported Origin)

/-- The scalar/point descriptor encoder never silently discards an
unsupported observation. A genuinely absent stored row is separate. -/
def record (name : Nat) (encode : α → Option Expr) : Option α → Option (List Equation)
  | none => some []
  | some x => (encode x).map (fun expr => [⟨name,expr⟩])

def holds (m : Assignment) (es : List Equation) : Prop :=
  ∀ row ∈ es, Equivalent (m row.left).1 (value (environment m) .actual row.right)

theorem record_exact {recorded : Option α} {encode : α → Option Expr} {check : α → Prop}
    (one : ∀ a expr, encode a = some expr →
      (check a ↔ Equivalent (m name).1 (value (environment m) .actual expr)))
    (computed : record name encode recorded = some es) :
    holds m es ↔ ∀ a, recorded = some a → check a := by
  cases recorded with
  | none =>
    have h : es = [] := (Option.some.inj computed).symm
    subst es
    simp [holds]
  | some actual =>
    unfold record at computed
    obtain ⟨expr,equation,same⟩ := Option.map_eq_some_iff.mp computed
    subst es
    constructor
    · intro fit other found
      cases Option.some.inj found
      exact (one _ _ equation).mpr (fit _ List.mem_cons_self)
    · intro fit row added
      cases List.mem_singleton.mp added
      exact (one _ _ equation).mp (fit _ rfl)

abbrev headAt (raw : State) (k : Fin raw.base.slots) :=
  record (raw.base.source k) headExpr (raw.base.heads k).equation
abbrev descriptorAt (raw : State) (k : Fin raw.base.slots) :=
  record (raw.base.source k) (descriptorExpr raw.base) (raw.nominals k)

def slotRows (raw : State) (k : Fin raw.base.slots) : Option (List Equation) := do
  let h ← headAt raw k
  let d ← descriptorAt raw k
  pure (h++d)

theorem at_exact (raw : State) (k : Fin raw.base.slots) (m : Assignment)
    (computed : slotRows raw k = some es) :
    holds m es ↔
      (∀ t, (raw.base.heads k).equation = some t →
        Equivalent (m (raw.base.source k)).1
          (t.eval CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment raw.base m))) ∧
      (∀ d, raw.nominals k = some d → Denotes raw.base m k d) := by
  cases first : headAt raw k with
  | none => simp [slotRows,first] at computed
  | some hs =>
    cases next : descriptorAt raw k with
    | none => simp [slotRows,first,next] at computed
    | some ds =>
      have same : hs++ds = es := by simpa [slotRows,first,next] using computed
      subst es
      have a := record_exact (recorded := (raw.base.heads k).equation)
        (check := fun t => Equivalent (m (raw.base.source k)).1
          (t.eval CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment raw.base m)))
        (m := m) (fun t expr e => by rw [head_semantics raw.base m t e]) first
      have b := record_exact (recorded := raw.nominals k) (check := Denotes raw.base m k)
        (m := m) (fun d expr e => descriptor_semantics raw.base k d m e) next
      rw [← a,← b]
      constructor
      · intro all
        exact ⟨fun e used => all e (List.mem_append_left _ used),fun e used => all e (List.mem_append_right _ used)⟩
      · rintro ⟨a,b⟩ e used
        exact (List.mem_append.mp used).elim (a e) (b e)

def collect (f : α → Option (List Equation)) : List α → Option (List Equation)
  | [] => some []
  | x::xs => do
    let hs ← f x
    let ds ← collect f xs
    pure (hs++ds)

theorem collect_exact (check : α → Prop)
    (one : ∀ x es, f x = some es → (holds m es ↔ check x))
    (computed : collect f xs = some all) :
    holds m all ↔ ∀ x ∈ xs, check x := by
  induction xs generalizing all with
  | nil =>
    have same : all = [] := (Option.some.inj computed).symm
    subst all
    simp [holds]
  | cons x xs ih =>
    cases h : f x with
    | none => simp [collect,h] at computed
    | some hs =>
      cases t : collect f xs with
      | none => simp [collect,h,t] at computed
      | some ts =>
        have same : hs++ts = all := by simpa [collect,h,t] using computed
        subst all
        constructor
        · intro fit key used
          rcases List.mem_cons.mp used with rfl|later
          · exact (one _ _ h).mp (fun e haveIt => fit e (List.mem_append_left _ haveIt))
          · exact (ih t).mp (fun e haveIt => fit e (List.mem_append_right _ haveIt)) _ later
        · intro fit e used
          rcases List.mem_append.mp used with first|last
          · exact (one _ _ h).mpr (fit x List.mem_cons_self) _ first
          · exact (ih t).mpr (fun k used => fit k (List.mem_cons_of_mem _ used)) _ last

def normal (raw : State) : GeneralDeclarativeWhere319.State :=
  ⟨raw.base.ordinary.map (atom (slot raw.base CompTerm.var)) ++ raw.ordinary,
    raw.base.intervals.map (fun ab => (raw.base.source ab.1,raw.base.source ab.2))⟩

def lower (raw : State) : Option GeneralDeclarativeHead320.State :=
  (collect (slotRows raw) (List.ofFn (fun k : Fin raw.base.slots => k))).map (fun es => ⟨normal raw,es⟩)

theorem exact_models (raw : State) (m : Assignment) (ok : lower raw = some s) :
    GeneralDeclarativeHead320.Models s m ↔ GeneralNominalState.Models raw m := by
  unfold lower at ok
  obtain ⟨es,found,rfl⟩ := Option.map_eq_some_iff.mp ok
  have checked := collect_exact (f := slotRows raw) (m := m) _ (fun k _ proof => at_exact raw k m proof) found
  unfold GeneralDeclarativeHead320.Models GeneralDeclarativeWhere319.Models
    GeneralNominalState.Models GeneralNominalCommonBridge.Models
  change ((PresenceNormalForm.All _ m ((raw.base.ordinary.map _) ++ raw.ordinary) ∧ _) ∧ holds m es) ↔ _
  rw [PresenceNormalForm.all_append,all_exact,checked]
  change ((_ ∧ _) ∧ _) ↔ _
  constructor
  · rintro ⟨⟨⟨ordinary,extra⟩,intervals⟩,shapes⟩
    refine ⟨⟨ordinary,fun k => (shapes k (List.mem_ofFn.mpr ⟨k,rfl⟩)).1,?_⟩,fun k => (shapes k (List.mem_ofFn.mpr ⟨k,rfl⟩)).2,extra⟩
    intro pair member
    exact intervals (raw.base.source pair.1,raw.base.source pair.2) (List.mem_map_of_mem member)
  · rintro ⟨⟨ordinary,heads,intervals⟩,desc,extra⟩
    refine ⟨⟨⟨ordinary,extra⟩,?_⟩,fun k _ => ⟨heads k,desc k⟩⟩
    intro pair member
    obtain ⟨ab,there,rfl⟩ := List.mem_map.mp member
    exact intervals ab there

/-- The initial source rows carry actual authorizing provenance.
New ordinary equalities in a stopped snapshot do not thereby
become authorized inputs. -/
def original (initial final : GeneralDeclarativeHead320.State) (kept : initial.equations ⊆ final.equations)
    (done : Nat → Prop) : Supported final done where
  derivesFrom := fun row origin => row ∈ initial.equations ∧ origin = .source
  ordinary := fun h => kept h.1

end Yulang.GeneralStoppedLower335
