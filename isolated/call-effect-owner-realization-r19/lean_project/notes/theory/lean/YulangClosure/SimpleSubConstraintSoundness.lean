import YulangClosure.SimpleSubConstraintSyntax

/-! Directed extrusion and finite retained-constraint soundness.
See the syntax module for the exact source scope and remaining bridges. -/
namespace YulangClosure.SimpleSub

def Directed (p : Polarity) {k} (old fresh : Term k) : Prop :=
  match p with
  | .positive => Sub old fresh
  | .negative => Sub fresh old

structure Copy where
  kind : Kind
  parent : Nat
  child : Nat
  polarity : Polarity

def Copy.link (c : Copy) : Constraint :=
  match c.polarity with
  | .positive => ⟨c.kind, .var c.parent, .var c.child⟩
  | .negative => ⟨c.kind, .var c.child, .var c.parent⟩

def Copy.equalities (c : Copy) : Store :=
  [⟨c.kind, .var c.parent, .var c.child⟩, ⟨c.kind, .var c.child, .var c.parent⟩]

abbrev Levels := Kind → Nat → Nat
abbrev CopyNames := Kind → Polarity → Nat → Nat

/-- The structural traversal uses the actual memo coordinate (kind, polarity,
parent). Names/levels come from an invocation; the forward theorem needs no
freshness premise and therefore also covers all fresh/injective invocations.
This function is not the Rust allocator or a proof of its termination. -/
def extrudeTerm (levels : Levels) (target : Nat) (names : CopyNames)
    (p : Polarity) {k} : Term k → Term k
  | .var identity =>
      if target < levels k identity then .var (names k p identity) else .var identity
  | .atom identity => .atom identity
  | .bottom => .bottom
  | .top => .top
  | .union a b => .union (extrudeTerm levels target names p a) (extrudeTerm levels target names p b)
  | .intersection a b =>
      .intersection (extrudeTerm levels target names p a) (extrudeTerm levels target names p b)
  | .function a ae re r =>
      .function (extrudeTerm levels target names p.flip a)
        (extrudeTerm levels target names p.flip ae)
        (extrudeTerm levels target names p re) (extrudeTerm levels target names p r)
  | .recordNil => .recordNil
  | .recordCons label optional field tail =>
      .recordCons label optional (extrudeTerm levels target names p field)
        (extrudeTerm levels target names p tail)
  | .tupleNil => .tupleNil
  | .tupleCons head tail =>
      .tupleCons (extrudeTerm levels target names p head) (extrudeTerm levels target names p tail)
  | .variantNil => .variantNil
  | .variantCons tag payloads tail =>
      .variantCons tag (extrudeTerm levels target names p payloads)
        (extrudeTerm levels target names p tail)

/-- Exactly the visited parent/copy coordinates, in structural traversal order.
Repeated memo hits retain the same coordinate; duplicate list entries do not
allocate additional rows or assert independent witnesses. -/
def extrudeCopies (levels : Levels) (target : Nat) (names : CopyNames)
    (p : Polarity) {k} : Term k → List Copy
  | .var identity =>
      if target < levels k identity then [⟨k, identity, names k p identity, p⟩] else []
  | .atom _ | .bottom | .top => []
  | .union a b | .intersection a b =>
      extrudeCopies levels target names p a ++ extrudeCopies levels target names p b
  | .function a ae re r =>
      extrudeCopies levels target names p.flip a ++ extrudeCopies levels target names p.flip ae ++
        extrudeCopies levels target names p re ++ extrudeCopies levels target names p r
  | .recordNil | .tupleNil | .variantNil => []
  | .recordCons _ _ field tail =>
      extrudeCopies levels target names p field ++ extrudeCopies levels target names p tail
  | .tupleCons head tail =>
      extrudeCopies levels target names p head ++ extrudeCopies levels target names p tail
  | .variantCons _ payloads tail =>
      extrudeCopies levels target names p payloads ++ extrudeCopies levels target names p tail

def CopiesSatisfied (ρ : Valuation) (copies : List Copy) : Prop :=
  Store.Satisfied ρ (copies.map Copy.link)

@[simp] theorem copiesSatisfied_nil (ρ : Valuation) : CopiesSatisfied ρ [] := by
  exact Store.satisfied_nil ρ

@[simp] theorem copiesSatisfied_cons (ρ : Valuation) (c : Copy) (cs : List Copy) :
    CopiesSatisfied ρ (c :: cs) ↔ c.link.Satisfied ρ ∧ CopiesSatisfied ρ cs := by
  exact Store.satisfied_cons ρ c.link (cs.map Copy.link)

@[simp] theorem copiesSatisfied_append (ρ : Valuation) (left right : List Copy) :
    CopiesSatisfied ρ (left ++ right) ↔ CopiesSatisfied ρ left ∧ CopiesSatisfied ρ right := by
  simp only [CopiesSatisfied, List.map_append, Store.satisfied_append]

/-- The actual directed approximation is derived from the emitted links.
Neither the approximation nor a step-preservation law is an input. -/
theorem extrusion_directed (levels : Levels) (target : Nat) (names : CopyNames)
    (ρ : Valuation) {k} (t : Term k) (p : Polarity)
    (links : CopiesSatisfied ρ (extrudeCopies levels target names p t)) :
    Directed p (t.subst ρ) ((extrudeTerm levels target names p t).subst ρ) := by
  induction t generalizing p with
  | @var k identity =>
      by_cases high : target < levels k identity
      · cases p <;>
          simpa [extrudeCopies, extrudeTerm, high, Directed, Copy.link,
            Constraint.Satisfied, Term.subst] using links
      · cases p <;> simp only [extrudeTerm, high, ↓reduceIte, Term.subst, Directed] <;>
          exact .refl _
  | atom identity => cases p <;> exact .refl _
  | bottom => cases p <;> exact .refl _
  | top => cases p <;> exact .refl _
  | union a b iha ihb =>
      rcases (copiesSatisfied_append ρ _ _).mp links with ⟨ha, hb⟩
      cases p <;> exact .unionMono (iha _ ha) (ihb _ hb)
  | intersection a b iha ihb =>
      rcases (copiesSatisfied_append ρ _ _).mp links with ⟨ha, hb⟩
      cases p <;> exact .intersectionMono (iha _ ha) (ihb _ hb)
  | function a ae re r iha ihae ihre ihr =>
      simp only [extrudeCopies, copiesSatisfied_append] at links
      rcases links with ⟨⟨⟨ha, hae⟩, hre⟩, hr⟩
      cases p <;> exact .function (iha _ ha) (ihae _ hae) (ihre _ hre) (ihr _ hr)
  | recordNil => cases p <;> exact .refl _
  | recordCons label optional field tail ihf iht =>
      rcases (copiesSatisfied_append ρ _ _).mp links with ⟨hf, ht⟩
      cases p <;> exact .recordCons label optional (ihf _ hf) (iht _ ht)
  | tupleNil => cases p <;> exact .refl _
  | tupleCons head tail ihh iht =>
      rcases (copiesSatisfied_append ρ _ _).mp links with ⟨hh, ht⟩
      cases p <;> exact .tupleCons (ihh _ hh) (iht _ ht)
  | variantNil => cases p <;> exact .refl _
  | variantCons tag payloads tail ihp iht =>
      rcases (copiesSatisfied_append ρ _ _).mp links with ⟨hp, ht⟩
      cases p <;> exact .variantCons tag (ihp _ hp) (iht _ ht)

theorem negative_demand_reflection (levels : Levels) (target : Nat) (names : CopyNames)
    (ρ : Valuation) {k} (lower upper : Term k)
    (links : CopiesSatisfied ρ (extrudeCopies levels target names .negative upper))
    (rewritten : Sub (lower.subst ρ) ((extrudeTerm levels target names .negative upper).subst ρ)) :
    Sub (lower.subst ρ) (upper.subst ρ) :=
  .trans rewritten (extrusion_directed levels target names ρ upper .negative links)

theorem positive_demand_reflection (levels : Levels) (target : Nat) (names : CopyNames)
    (ρ : Valuation) {k} (lower upper : Term k)
    (links : CopiesSatisfied ρ (extrudeCopies levels target names .positive lower))
    (rewritten : Sub ((extrudeTerm levels target names .positive lower).subst ρ) (upper.subst ρ)) :
    Sub (lower.subst ρ) (upper.subst ρ) :=
  .trans (extrusion_directed levels target names ρ lower .positive links) rewritten

/-- Opposite-bound replay is a theorem of the stored lower/upper clauses. -/
theorem opposite_bound_replay (ρ : Valuation) {k} (lower upper : Term k) (row : Nat)
    (lowerBound : (Constraint.mk k lower (.var row)).Satisfied ρ)
    (upperBound : (Constraint.mk k (.var row) upper).Satisfied ρ) :
    (Constraint.mk k lower upper).Satisfied ρ :=
  .trans lowerBound upperBound

structure Occurrence where
  identity : Nat
  origin : Nat
  receiver : Nat
  copies : List Copy

structure Row where
  kind : Kind
  identity : Nat

def Occurrence.source (e : Occurrence) : YulangClosure.ExtrusionOccurrence Nat Row Nat :=
  ⟨e.identity, e.origin, e.receiver,
    e.copies.map (fun c => (⟨c.kind, c.parent⟩, ⟨c.kind, c.child⟩,
      match c.polarity with | .positive => true | .negative => false))⟩

def Occurrence.Qualifies (ref : Nat → Nat → Prop) (birth : Nat → Nat) (e : Occurrence) : Prop :=
  YulangClosure.Qualifies ref birth e.source

structure State where
  obligations : Store
  occurrences : List Occurrence

def State.Satisfied (ρ : Valuation) (state : State) : Prop := state.obligations.Satisfied ρ

/-- Actual operations on retained obligations. Extrusion records exactly the
traversal's copy coordinates. Intrusion selects only a retained event and its
actual copies, using the existing immutable-birth induced-path predicate.
The predicate is not redefined using the type-bound graph. -/
inductive Step (ref : Nat → Nat → Prop) (birth : Nat → Nat) : State → State → Prop where
  | reflexive (k : Kind) (t : Term k) (rest : Store) (events : List Occurrence) :
      Step ref birth ⟨⟨k, t, t⟩ :: rest, events⟩ ⟨rest, events⟩
  | bottom (k : Kind) (t : Term k) (rest : Store) (events : List Occurrence) :
      Step ref birth ⟨⟨k, .bottom, t⟩ :: rest, events⟩ ⟨rest, events⟩
  | top (k : Kind) (t : Term k) (rest : Store) (events : List Occurrence) :
      Step ref birth ⟨⟨k, t, .top⟩ :: rest, events⟩ ⟨rest, events⟩
  | function (a a' r r' : Term .value) (ae ae' re re' : Term .effect)
      (rest : Store) (events : List Occurrence) :
      Step ref birth ⟨⟨.value, .function a ae re r, .function a' ae' re' r'⟩ :: rest, events⟩
        ⟨⟨.value, a', a⟩ :: ⟨.effect, ae', ae⟩ :: ⟨.effect, re, re'⟩ ::
          ⟨.value, r, r'⟩ :: rest, events⟩
  | recordCons (label : Nat) (optional : Bool) (f f' t t' : Term .value)
      (rest : Store) (events : List Occurrence) :
      Step ref birth
        ⟨⟨.value, .recordCons label optional f t, .recordCons label optional f' t'⟩ :: rest, events⟩
        ⟨⟨.value, f, f'⟩ :: ⟨.value, t, t'⟩ :: rest, events⟩
  | tupleCons (h h' t t' : Term .value) (rest : Store) (events : List Occurrence) :
      Step ref birth ⟨⟨.value, .tupleCons h t, .tupleCons h' t'⟩ :: rest, events⟩
        ⟨⟨.value, h, h'⟩ :: ⟨.value, t, t'⟩ :: rest, events⟩
  | variantCons (tag : Nat) (p p' t t' : Term .value) (rest : Store) (events : List Occurrence) :
      Step ref birth ⟨⟨.value, .variantCons tag p t, .variantCons tag p' t'⟩ :: rest, events⟩
        ⟨⟨.value, p, p'⟩ :: ⟨.value, t, t'⟩ :: rest, events⟩
  | union (k : Kind) (a b upper : Term k) (rest : Store) (events : List Occurrence) :
      Step ref birth ⟨⟨k, .union a b, upper⟩ :: rest, events⟩
        ⟨⟨k, a, upper⟩ :: ⟨k, b, upper⟩ :: rest, events⟩
  | intersection (k : Kind) (lower a b : Term k) (rest : Store) (events : List Occurrence) :
      Step ref birth ⟨⟨k, lower, .intersection a b⟩ :: rest, events⟩
        ⟨⟨k, lower, a⟩ :: ⟨k, lower, b⟩ :: rest, events⟩
  | insertLower (k : Kind) (lower : Term k) (row : Nat) (state : State) :
      Step ref birth state ⟨⟨k, lower, .var row⟩ :: state.obligations, state.occurrences⟩
  | insertUpper (k : Kind) (row : Nat) (upper : Term k) (state : State) :
      Step ref birth state ⟨⟨k, .var row, upper⟩ :: state.obligations, state.occurrences⟩
  | replay (k : Kind) (lower upper : Term k) (row : Nat) (state : State)
      (hasLower : Constraint.mk k lower (.var row) ∈ state.obligations)
      (hasUpper : Constraint.mk k (.var row) upper ∈ state.obligations) :
      Step ref birth state ⟨⟨k, lower, upper⟩ :: state.obligations, state.occurrences⟩
  | extrudeUpper (levels : Levels) (target : Nat) (names : CopyNames)
      (k : Kind) (lower upper : Term k) (rest : Store) (events : List Occurrence)
      (identity origin receiver : Nat) :
      Step ref birth ⟨⟨k, lower, upper⟩ :: rest, events⟩
        ⟨(extrudeCopies levels target names .negative upper).map Copy.link ++
            ⟨k, lower, extrudeTerm levels target names .negative upper⟩ :: rest,
          ⟨identity, origin, receiver, extrudeCopies levels target names .negative upper⟩ :: events⟩
  | extrudeLower (levels : Levels) (target : Nat) (names : CopyNames)
      (k : Kind) (lower upper : Term k) (rest : Store) (events : List Occurrence)
      (identity origin receiver : Nat) :
      Step ref birth ⟨⟨k, lower, upper⟩ :: rest, events⟩
        ⟨(extrudeCopies levels target names .positive lower).map Copy.link ++
            ⟨k, extrudeTerm levels target names .positive lower, upper⟩ :: rest,
          ⟨identity, origin, receiver, extrudeCopies levels target names .positive lower⟩ :: events⟩
  | intrude (state : State) (event : Occurrence) (selected : List Copy)
      (retained : event ∈ state.occurrences) (qualifies : event.Qualifies ref birth)
      (actual : ∀ c, c ∈ selected → c ∈ event.copies) :
      Step ref birth state
        ⟨selected.flatMap Copy.equalities ++ state.obligations, state.occurrences⟩

theorem Step.sound {ref : Nat → Nat → Prop} {birth : Nat → Nat}
    {before after : State} (step : Step ref birth before after) (ρ : Valuation)
    (h : after.Satisfied ρ) : before.Satisfied ρ := by
  cases step <;>
    simp only [State.Satisfied, Store.satisfied_cons, Store.satisfied_append] at h ⊢
  case reflexive => exact ⟨.refl _, h⟩
  case bottom => exact ⟨.bottom _, h⟩
  case top => exact ⟨.top _, h⟩
  case function => exact ⟨.function h.1 h.2.1 h.2.2.1 h.2.2.2.1, h.2.2.2.2⟩
  case recordCons => exact ⟨.recordCons _ _ h.1 h.2.1, h.2.2⟩
  case tupleCons => exact ⟨.tupleCons h.1 h.2.1, h.2.2⟩
  case variantCons => exact ⟨.variantCons _ h.1 h.2.1, h.2.2⟩
  case union => exact ⟨.unionElim h.1 h.2.1, h.2.2⟩
  case intersection => exact ⟨.intersectionIntro h.1 h.2.1, h.2.2⟩
  case insertLower => exact h.2
  case insertUpper => exact h.2
  case replay => exact h.2
  case extrudeUpper =>
    exact ⟨negative_demand_reflection _ _ _ ρ _ _ h.1 h.2.1, h.2.2⟩
  case extrudeLower =>
    exact ⟨positive_demand_reflection _ _ _ ρ _ _ h.1 h.2.1, h.2.2⟩
  case intrude => exact h.2

/-- Replaying actual opposite bounds preserves the entire solution set,
because the added comparison follows from the two retained clauses. -/
theorem replay_solution_iff (ρ : Valuation) {k} (lower upper : Term k) (row : Nat)
    (store : Store)
    (hasLower : Constraint.mk k lower (.var row) ∈ store)
    (hasUpper : Constraint.mk k (.var row) upper ∈ store) :
    Store.Satisfied ρ (Constraint.mk k lower upper :: store) ↔ store.Satisfied ρ := by
  rw [Store.satisfied_cons]
  constructor
  · exact And.right
  · intro h
    exact ⟨opposite_bound_replay ρ lower upper row (h _ hasLower) (h _ hasUpper), h⟩

theorem Step.retains_occurrences {ref : Nat → Nat → Prop} {birth : Nat → Nat}
    {before after : State} (step : Step ref birth before after) :
    ∀ event, event ∈ before.occurrences → event ∈ after.occurrences := by
  cases step <;> intro event he <;> first | exact he | exact List.mem_cons_of_mem _ he

inductive History (ref : Nat → Nat → Prop) (birth : Nat → Nat) : State → State → Prop where
  | nil (state : State) : History ref birth state state
  | cons {first middle last : State} :
      Step ref birth first middle → History ref birth middle last → History ref birth first last

/-- A final solution reflects to every original generated constraint. Every
step's implication is proved above from its concrete constructors. -/
theorem History.sound {ref : Nat → Nat → Prop} {birth : Nat → Nat}
    {initial final : State} (history : History ref birth initial final) (ρ : Valuation)
    (solution : final.Satisfied ρ) : initial.Satisfied ρ := by
  induction history with
  | nil state => exact solution
  | cons step rest ih => exact step.sound ρ (ih solution)

theorem History.retains_occurrences {ref : Nat → Nat → Prop} {birth : Nat → Nat}
    {initial final : State} (history : History ref birth initial final) :
    ∀ event, event ∈ initial.occurrences → event ∈ final.occurrences := by
  induction history with
  | nil state => exact fun _ h => h
  | cons step rest ih => exact fun event h => ih event (step.retains_occurrences event h)

/-- Canonicalization is performed on every retained final clause. Pulling
back the terminal valuation along that exact map then solves the original
pre-extrusion constraints in their original row namespace. -/
theorem History.quotient_sound {ref : Nat → Nat → Prop} {birth : Nat → Nat}
    {initial final : State} (history : History ref birth initial final)
    (q : Renaming) (ρ : Valuation)
    (solution : Store.Satisfied ρ (final.obligations.map (Constraint.rename q))) :
    initial.Satisfied (fun k identity => ρ k (q k identity)) := by
  apply history.sound
  exact (Store.quotient_pullback q ρ final.obligations).mp solution

/-- If these concrete transformations discharge every obligation, every
valuation solves the input. This is not a claim that native successful
inference always empties its store or has been simulated by `History`. -/
theorem History.empty_sound {ref : Nat → Nat → Prop} {birth : Nat → Nat}
    {initial final : State} (history : History ref birth initial final)
    (empty : final.obligations = []) (ρ : Valuation) : initial.Satisfied ρ := by
  apply history.sound ρ
  change Store.Satisfied ρ final.obligations
  rw [empty]
  exact Store.satisfied_nil ρ

/-- All four original ports, including both effects, have the prescribed
copy polarity and order. This is a reduction of the executable traversal. -/
theorem positive_function_copy_order (names : CopyNames) (a ae re r : Nat) :
    extrudeCopies (fun _ _ => 1) 0 names .positive
      (.function (.var a) (.var ae) (.var re) (.var r)) =
      [⟨.value, a, names .value .negative a, .negative⟩,
       ⟨.effect, ae, names .effect .negative ae, .negative⟩,
       ⟨.effect, re, names .effect .positive re, .positive⟩,
       ⟨.value, r, names .value .positive r, .positive⟩] := rfl

theorem negative_function_copy_order (names : CopyNames) (a ae re r : Nat) :
    extrudeCopies (fun _ _ => 1) 0 names .negative
      (.function (.var a) (.var ae) (.var re) (.var r)) =
      [⟨.value, a, names .value .positive a, .positive⟩,
       ⟨.effect, ae, names .effect .positive ae, .positive⟩,
       ⟨.effect, re, names .effect .negative re, .negative⟩,
       ⟨.value, r, names .value .negative r, .negative⟩] := rfl

end YulangClosure.SimpleSub
