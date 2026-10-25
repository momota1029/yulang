import YulangClosure.PaperTermSubstitution

/-!
Partial ordinary computation reduction for manuscript typing rules 203–240 and
reductions 305–316. `none` means only that this operator gives no reduction.
The full state preservation/display simulation theorem remains open.
-/
namespace YulangClosure.PaperTypes.PaperCoreStep

def singleReplacement (value : Value) : Nat → Value
  | 0 => value
  | n + 1 => .variable n

theorem singleReplacement_typed {d g e v a}
    (hv : PaperValueTyped d g e v a) :
    TermSubstitutionTyped d g (a :: e) e (singleReplacement v) := by
  intro n b hn
  cases n with
  | zero =>
      have hab : a = b := Option.some.inj hn
      subst b
      exact hv
  | succ n => exact .variable hn

def lookupRecord : List (Label × Presence × Value) → Label → Option Value
  | [], _ => none
  | (key, _, value) :: rest, label =>
      if key = label then some value else lookupRecord rest label

def recordLabels : Ty → List Label
  | .recordCons label _ _ tail => label :: recordLabels tail
  | _ => []

def requiredLabels : Ty → List Label
  | .recordCons label .immutable _ tail => label :: requiredLabels tail
  | .recordCons _ .mutable _ tail => requiredLabels tail
  | _ => []

def declaredType : Ty → Label → Option Ty
  | .recordCons key _ field tail, label =>
      if key = label then some field else declaredType tail label
  | _, _ => none

theorem shape_labels {r labels required} (hs : RecordShape r labels required) :
    recordLabels r = labels ∧ requiredLabels r = required ∧ labels.Nodup := by
  induction hs with
  | nil => simp [recordLabels, requiredLabels]
  | required hs unique ih =>
      rcases ih with ⟨hl, hr, hn⟩
      simp_all [recordLabels, requiredLabels, Presence.encode]
  | optional hs unique ih =>
      rcases ih with ⟨hl, hr, hn⟩
      simp_all [recordLabels, requiredLabels, Presence.encode]

theorem field_label_mem {r label presence a}
    (hf : RecordField r label presence a) : label ∈ recordLabels r := by
  induction hf with
  | here => simp [recordLabels]
  | there hf ih => exact List.mem_cons_of_mem _ ih

theorem field_required_mem {r label presence a}
    (hf : RecordField r label presence a) :
    presence = .required → label ∈ requiredLabels r := by
  induction hf with
  | here =>
      intro he
      subst presence
      simp [requiredLabels, Presence.encode]
  | @there label presence a tail other otherPresence otherType hf ih =>
      intro he
      have hm := ih he
      cases otherPresence <;> simp_all [requiredLabels, Presence.encode]

theorem field_declaredType {r label presence a}
    (hf : RecordField r label presence a) (hu : (recordLabels r).Nodup) :
    declaredType r label = some a := by
  induction hf with
  | here => simp [declaredType]
  | @there label presence a tail other otherPresence otherType hf ih =>
      have hnodup : other ∉ recordLabels tail ∧ (recordLabels tail).Nodup :=
        List.nodup_cons.mp hu
      have hne : other ≠ label := by
        intro he
        subst other
        exact hnodup.1 (field_label_mem hf)
      simp only [declaredType, if_neg hne]
      exact ih hnodup.2

theorem field_type_unique {r labels required label p q a b}
    (hs : RecordShape r labels required)
    (ha : RecordField r label p a) (hb : RecordField r label q b) : a = b := by
  have hl := shape_labels hs
  have hu : (recordLabels r).Nodup := hl.1.symm ▸ hl.2.2
  exact Option.some.inj ((field_declaredType ha hu).symm.trans (field_declaredType hb hu))

theorem lookupRecord_none_iff {fields label} :
    lookupRecord fields label = none ↔ label ∉ fields.map Prod.fst := by
  induction fields with
  | nil => simp [lookupRecord]
  | cons entry fields ih =>
      rcases entry with ⟨key, tag, value⟩
      by_cases he : key = label
      · subst key
        simp [lookupRecord]
      · simp [lookupRecord, he, ih, Ne.symm he]

theorem lookupRecord_typed {d g e fields r labels required label presence a v}
    (hs : RecordShape r labels required)
    (hp : RecordPayloadsTyped d g e fields r)
    (hf : RecordField r label presence a)
    (hl : lookupRecord fields label = some v) : PaperValueTyped d g e v a := by
  induction fields with
  | nil => simp [lookupRecord] at hl
  | cons entry fields ih =>
      rcases entry with ⟨key, tag, value⟩
      cases hp with
      | cons declared typed tail =>
          by_cases he : key = label
          · subst key
            simp only [lookupRecord, if_pos rfl] at hl
            have hv : value = v := Option.some.inj hl
            subst v
            have ht := field_type_unique hs declared hf
            cases ht
            exact typed
          · simp only [lookupRecord, if_neg he] at hl
            exact ih tail hl

def step : Computation → Option Computation
  | .letE (.ret value) body => termSubstituteComputation (singleReplacement value) body
  | .force (.delay body) => some body
  | .unionCase (.injectLeft value) _ left _ _ =>
      termSubstituteComputation (singleReplacement value) left
  | .unionCase (.injectRight value) _ _ _ right =>
      termSubstituteComputation (singleReplacement value) right
  | .unroll (.roll value) => some (.ret value)
  | .field (.record fields) label => (lookupRecord fields label).map Computation.ret
  | .lookup (.record fields) label =>
      some (.ret (match lookupRecord fields label with
        | some value => .injectRight value
        | none => .injectLeft (.literal .unit)))
  | _ => none

end YulangClosure.PaperTypes.PaperCoreStep
