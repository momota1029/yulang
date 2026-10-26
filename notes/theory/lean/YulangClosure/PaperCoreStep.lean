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
      cases he
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
      simp only [declaredType, ite_eq_right hne]
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
            simp only [lookupRecord] at hl
            have hv : value = v := Option.some.inj hl
            subst v
            have ht := field_type_unique hs declared hf
            cases ht
            exact typed
          · simp only [lookupRecord, ite_eq_right he] at hl
            exact ih tail hl

def step : Computation → Option Computation
  | .letE (.ret value) body => termSubstituteComputation (singleReplacement value) body
  | .force (.delay body) => some body
  | .unionCase (.injectLeft value) _ left _ _ =>
      termSubstituteComputation (singleReplacement value) left
  | .unionCase (.injectRight value) _ _ _ right =>
      termSubstituteComputation (singleReplacement value) right
  | .unroll (.roll value) => some (.ret value)
  | .choose (.both value) _ => some (.ret value)
  | .field (.record fields) label => (lookupRecord fields label).map Computation.ret
  | .lookup (.record fields) label =>
      some (.ret (match lookupRecord fields label with
        | some value => .injectRight value
        | none => .injectLeft (.literal .unit)))
  | _ => none


/-- The let/return redex applies and preserves the unchanged shared contexts. -/
theorem letRet_applicable {d g e value body a}
    (hc : PaperComputationTyped d g e (.letE (.ret value) body) a) :
    ∃ result, step (.letE (.ret value) body) = some result ∧
      PaperComputationTyped d g e result a := by
  cases hc with
  | letE hf hb =>
      cases hf with
      | ret hv => exact hb.termSubstitute (singleReplacement_typed hv)

/-- Force/Delay requires no substitution or change of result type. -/
theorem force_applicable {d g e body a}
    (hc : PaperComputationTyped d g e (.force (.delay body)) a) :
    ∃ result, step (.force (.delay body)) = some result ∧
      PaperComputationTyped d g e result a := by
  cases hc with
  | force hv =>
      cases hv with
      | delay hb => exact ⟨body, rfl, hb⟩

/-- Only the left injection's branch receives its payload. -/
theorem unionLeft_applicable {d g e value lb left rb right a}
    (hc : PaperComputationTyped d g e
      (.unionCase (.injectLeft value) lb left rb right) a) :
    ∃ result, step (.unionCase (.injectLeft value) lb left rb right) = some result ∧
      PaperComputationTyped d g e result a := by
  cases hc with
  | unionCase hv hl hr =>
      cases hv with
      | injectLeft hv => exact hl.termSubstitute (singleReplacement_typed hv)

/-- Only the right injection's branch receives its payload. -/
theorem unionRight_applicable {d g e value lb left rb right a}
    (hc : PaperComputationTyped d g e
      (.unionCase (.injectRight value) lb left rb right) a) :
    ∃ result, step (.unionCase (.injectRight value) lb left rb right) = some result ∧
      PaperComputationTyped d g e result a := by
  cases hc with
  | unionCase hv hl hr =>
      cases hv with
      | injectRight hv => exact hr.termSubstitute (singleReplacement_typed hv)

/-- Unrolling returns exactly the payload at the typing rule's unfolding. -/
theorem unroll_applicable {d g e value a}
    (hc : PaperComputationTyped d g e (.unroll (.roll value)) a) :
    ∃ result, step (.unroll (.roll value)) = some result ∧
      PaperComputationTyped d g e result a := by
  cases hc with
  | unroll hv =>
      cases hv with
      | roll hv => exact ⟨.ret value, rfl, .ret hv⟩

/-- Both sides return the same raw payload, with the selected typing derivation. -/
theorem choose_applicable {d g e value side resultType}
    (hc : PaperComputationTyped d g e (.choose (.both value) side) resultType) :
    ∃ result, step (.choose (.both value) side) = some result ∧
      PaperComputationTyped d g e result resultType := by
  cases hc with
  | chooseLeft hv =>
      cases hv with
      | both left right => exact ⟨.ret value, rfl, .ret left⟩
  | chooseRight hv =>
      cases hv with
      | both left right => exact ⟨.ret value, rfl, .ret right⟩

/-- The partial operational function gives Bottom elimination no principal step. -/
theorem absurd_no_step (value : Value) : step (.absurd value) = none := rfl

/-- Required-field coverage excludes a missing required runtime label. -/
theorem field_applicable {d g e fields label a}
    (hc : PaperComputationTyped d g e (.field (.record fields) label) a) :
    ∃ result, step (.field (.record fields) label) = some result ∧
      PaperComputationTyped d g e result a := by
  cases hc with
  | field hv hf =>
      cases hv with
      | record shape unique required payloads =>
          have hm : label ∈ fields.map Prod.fst := by
            apply required
            rw [← (shape_labels shape).2.1]
            exact field_required_mem hf rfl
          have hn : lookupRecord fields label ≠ none := by
            intro absent
            exact (lookupRecord_none_iff.mp absent) hm
          cases hl : lookupRecord fields label with
          | none => exact False.elim (hn hl)
          | some value =>
              exact ⟨.ret value, by simp [step, hl],
                .ret (lookupRecord_typed shape payloads hf hl)⟩

/-- Lookup handles runtime presence and absence for either declared presence. -/
theorem lookup_applicable {d g e fields label a}
    (hc : PaperComputationTyped d g e (.lookup (.record fields) label) a) :
    ∃ result, step (.lookup (.record fields) label) = some result ∧
      PaperComputationTyped d g e result a := by
  cases hc with
  | lookup hv hf =>
      cases hv with
      | record shape unique required payloads =>
          cases hl : lookupRecord fields label with
          | none =>
              exact ⟨.ret (.injectLeft (.literal .unit)), by simp [step, hl],
                .ret (.injectLeft .literal)⟩
          | some value =>
              exact ⟨.ret (.injectRight value), by simp [step, hl],
                .ret (.injectRight (lookupRecord_typed shape payloads hf hl))⟩

/-- Every successor of this partial raw step preserves the original result type. -/
theorem preservation {d g e c c' a}
    (hc : PaperComputationTyped d g e c a) (hs : step c = some c') :
    PaperComputationTyped d g e c' a := by
  have finish {redex : Computation}
      (hr : ∃ result, step redex = some result ∧ PaperComputationTyped d g e result a)
      (hstep : step redex = some c') : PaperComputationTyped d g e c' a := by
    rcases hr with ⟨result, he, ht⟩
    have heq : result = c' := Option.some.inj (he.symm.trans hstep)
    exact heq ▸ ht
  cases c with
  | letE first body =>
      cases first with
      | ret value => exact finish (letRet_applicable hc) hs
      | _ => simp [step] at hs
  | force thunk =>
      cases thunk with
      | delay body => exact finish (force_applicable hc) hs
      | _ => simp [step] at hs
  | unionCase value lb left rb right =>
      cases value with
      | injectLeft value => exact finish (unionLeft_applicable hc) hs
      | injectRight value => exact finish (unionRight_applicable hc) hs
      | _ => simp [step] at hs
  | unroll value =>
      cases value with
      | roll value => exact finish (unroll_applicable hc) hs
      | _ => simp [step] at hs
  | choose value side =>
      cases value with
      | both value => exact finish (choose_applicable hc) hs
      | _ => simp [step] at hs
  | field recordValue label =>
      cases recordValue with
      | record fields => exact finish (field_applicable hc) hs
      | _ => simp [step] at hs
  | lookup recordValue label =>
      cases recordValue with
      | record fields => exact finish (lookup_applicable hc) hs
      | _ => simp [step] at hs
  | _ => simp [step] at hs

end YulangClosure.PaperTypes.PaperCoreStep
