import Yulang.GeneralDeclarativeI65B6PairedTreeReplay400

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessConstructorModes357 (Use)
open GeneralDeclarativeWitnessSparseIntervals357 (names)
open GeneralCandidateInspection (Primitive)
open CommonDeclaredNominalInspection (Kind Parameter)
open CommonRecursiveNominalIntervals (effectiveParameter childContext)
open CommonNominalFullCarrier (Ty Row record variant nominal)

/- The typed input and its instantiated output have the same source
index, constructor tree, context and slot kinds. Only the payload of a
lexical reference changes. A primitive must be the original operation
of a source-authored Use. No primitive is encoded as nominal. -/
mutual
inductive MixedRhs401 (s : State) (leaf : Kind → Nat → Type) :
    Bool → Pattern → Type where
  | binder (n : Nat) : leaf .value n → MixedRhs401 s leaf c (.var n)
  | record (label : Nat) : MixedRhs401 s leaf c a → MixedRhs401 s leaf c b →
      MixedRhs401 s leaf c (.record label a b)
  | variant (tag : Nat) : MixedRhs401 s leaf c p → MixedRhs401 s leaf c (.variant tag p)
  | join : MixedRhs401 s leaf c a → MixedRhs401 s leaf c b → MixedRhs401 s leaf c (.join a b)
  | declaredApp (n : Nat) (use : Use s.current.environment n ps.length) :
      names use.mode ps.length = some params → s.modes[n]? = some params →
      MixedArgs401 s leaf c params ps → MixedRhs401 s leaf c (.app n ps)
  | scalar (n : Nat) (base : Inference.Base) (use : Use s.current.environment n 0) :
      use.mode = .primitive (.scalar base) → MixedRhs401 s leaf c (.app n [])
  | emptyRecord (n : Nat) (use : Use s.current.environment n 0) :
      use.mode = .primitive .emptyRecord → MixedRhs401 s leaf c (.app n [])
  | exactEmpty (n : Nat) (use : Use s.current.environment n 0) :
      use.mode = .primitive .exactEmpty → MixedRhs401 s leaf c (.app n [])
  | pair (n : Nat) (use : Use s.current.environment n 2) :
      use.mode = .primitive .pair → MixedRhs401 s leaf c a →
      MixedRhs401 s leaf c b → MixedRhs401 s leaf c (.app n [a,b])

inductive MixedArg401 (s : State) (leaf : Kind → Nat → Type) :
    Bool → Parameter → Pattern → Type where
  | valuePoint (n : Nat) : p.kind = .value →
      (effectiveParameter c p).variance ≠ .invariant → leaf .value n →
      MixedArg401 s leaf c p (.var n)
  | valueInterval (n : Nat) : p.kind = .value →
      (effectiveParameter c p).variance = .invariant → leaf .value n →
      MixedArg401 s leaf c p (.var n)
  | rowPoint (n : Nat) : p.kind = .row →
      (effectiveParameter c p).variance ≠ .invariant → leaf .row n →
      MixedArg401 s leaf c p (.var n)
  | rowInterval (n : Nat) : p.kind = .row →
      (effectiveParameter c p).variance = .invariant → leaf .row n →
      MixedArg401 s leaf c p (.var n)
  | valueTree : p.kind = .value → (∀ n, pat ≠ .var n) →
      MixedRhs401 s leaf (childContext c p) pat → MixedArg401 s leaf c p pat

inductive MixedArgs401 (s : State) (leaf : Kind → Nat → Type) :
    Bool → List Parameter → List Pattern → Type where
  | nil : MixedArgs401 s leaf c [] []
  | cons : MixedArg401 s leaf c p a → MixedArgs401 s leaf c ps as →
      MixedArgs401 s leaf c (p::ps) (a::as)
end

abbrev B6MixedRhs401 (s : State) := MixedRhs401 s (fun _ _ => Unit)

/-- Exact source kind and original capture; endpoints aren't substituted
for the actual center. All three logical names remain available. -/
structure InstantiatedSlot401 (s : State) (slots : Nat → Option Capture)
    (k : Kind) (n : Nat) where
  original : Capture
  source : slots n = some original
  kind : TypedBodyCapture392 s original k

abbrev RetainedTree401 (s : State) (slots : Nat → Option Capture) :=
  MixedRhs401 s (InstantiatedSlot401 s slots)

mutual
def substituteMixedRhs401 {s leaf mapped c p}
    (get : ∀ k n, leaf k n → Option (mapped k n)) :
    MixedRhs401 s leaf c p → Option (MixedRhs401 s mapped c p)
  | .binder n slot => (get .value n slot).map (.binder n)
  | .record label a b => do
    pure (.record label (← substituteMixedRhs401 get a) (← substituteMixedRhs401 get b))
  | .variant tag a => (substituteMixedRhs401 get a).map (.variant tag)
  | .join a b => do
    pure (.join (← substituteMixedRhs401 get a) (← substituteMixedRhs401 get b))
  | .declaredApp n use kinds exacts args =>
      (substituteMixedArgs401 get args).map (.declaredApp n use kinds exacts)
  | .scalar n base use exacts => some (.scalar n base use exacts)
  | .emptyRecord n use exacts => some (.emptyRecord n use exacts)
  | .exactEmpty n use exacts => some (.exactEmpty n use exacts)
  | .pair n use exacts a b => do
    pure (.pair n use exacts (← substituteMixedRhs401 get a) (← substituteMixedRhs401 get b))

def substituteMixedArg401 {s leaf mapped c param p}
    (get : ∀ k n, leaf k n → Option (mapped k n)) :
    MixedArg401 s leaf c param p → Option (MixedArg401 s mapped c param p)
  | .valuePoint n kind mode slot => (get .value n slot).map (.valuePoint n kind mode)
  | .valueInterval n kind mode slot => (get .value n slot).map (.valueInterval n kind mode)
  | .rowPoint n kind mode slot => (get .row n slot).map (.rowPoint n kind mode)
  | .rowInterval n kind mode slot => (get .row n slot).map (.rowInterval n kind mode)
  | .valueTree kind compound sub => (substituteMixedRhs401 get sub).map (.valueTree kind compound)

def substituteMixedArgs401 {s leaf mapped c params ps}
    (get : ∀ k n, leaf k n → Option (mapped k n)) :
    MixedArgs401 s leaf c params ps → Option (MixedArgs401 s mapped c params ps)
  | .nil => some .nil
  | .cons a b => do pure (.cons (← substituteMixedArg401 get a) (← substituteMixedArgs401 get b))
end

open GeneralNominalCenteredHeadMatExpressions (primitiveValue)
mutual
def evaluateMixedRhs401 {s leaf c p}
    (get : ∀ k n, leaf k n → Option (Ty × Row)) :
    MixedRhs401 s leaf c p → Option Ty
  | .binder n slot => (get .value n slot).map Prod.fst
  | .record label a b => do
    pure (record label (← evaluateMixedRhs401 get a) (← evaluateMixedRhs401 get b))
  | .variant tag a => (evaluateMixedRhs401 get a).map (variant tag)
  | .join a b => do pure (.union (← evaluateMixedRhs401 get a) (← evaluateMixedRhs401 get b))
  | .declaredApp n _ _ _ args => (evaluateMixedArgs401 get args).map (nominal n)
  | .scalar _ base _ _ => some (primitiveValue (.scalar base) [])
  | .emptyRecord _ _ _ => some (primitiveValue .emptyRecord [])
  | .exactEmpty _ _ _ => some (primitiveValue .exactEmpty [])
  | .pair _ _ _ a b => do
    pure (primitiveValue .pair [← evaluateMixedRhs401 get a, ← evaluateMixedRhs401 get b])

def evaluateMixedArg401 {s leaf c param p}
    (get : ∀ k n, leaf k n → Option (Ty × Row)) :
    MixedArg401 s leaf c param p → Option (Ty ⊕ Row)
  | .valuePoint n _ _ slot | .valueInterval n _ _ slot =>
    (get .value n slot).map (Sum.inl ∘ Prod.fst)
  | .rowPoint n _ _ slot | .rowInterval n _ _ slot =>
    (get .row n slot).map (Sum.inr ∘ Prod.snd)
  | .valueTree _ _ sub => (evaluateMixedRhs401 get sub).map Sum.inl

def evaluateMixedArgs401 {s leaf c params ps}
    (get : ∀ k n, leaf k n → Option (Ty × Row)) :
    MixedArgs401 s leaf c params ps → Option (List (Ty ⊕ Row))
  | .nil => some []
  | .cons a b => do
    pure ((← evaluateMixedArg401 get a) :: (← evaluateMixedArgs401 get b))
end


theorem mixed_substitution_value_fusion401 {s c p} {leaf mapped : Kind → Nat → Type}
    (sub : ∀ k n, leaf k n → Option (mapped k n))
    (value : ∀ k n, mapped k n → Option (Ty × Row))
    (tree : MixedRhs401 s leaf c p) :
    (substituteMixedRhs401 sub tree).bind (evaluateMixedRhs401 value) =
      evaluateMixedRhs401 (fun k n x => (sub k n x).bind (value k n)) tree := by
  refine MixedRhs401.rec
    (motive_1 := fun _ _ t => (substituteMixedRhs401 sub t).bind (evaluateMixedRhs401 value) =
      evaluateMixedRhs401 (fun k n x => (sub k n x).bind (value k n)) t)
    (motive_2 := fun _ _ _ t => (substituteMixedArg401 sub t).bind (evaluateMixedArg401 value) =
      evaluateMixedArg401 (fun k n x => (sub k n x).bind (value k n)) t)
    (motive_3 := fun _ _ _ t => (substituteMixedArgs401 sub t).bind (evaluateMixedArgs401 value) =
      evaluateMixedArgs401 (fun k n x => (sub k n x).bind (value k n)) t)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ tree
  · intro c n mark; cases h : sub .value n mark <;> simp [substituteMixedRhs401,evaluateMixedRhs401,h]
  · intro c p q label a b ha hb
    cases ea : substituteMixedRhs401 sub a <;> cases eb : substituteMixedRhs401 sub b <;>
      simp [substituteMixedRhs401,evaluateMixedRhs401,ea,eb,← ha,← hb]
  · intro c p tag b ih
    cases eb : substituteMixedRhs401 sub b <;>
      simp [substituteMixedRhs401,evaluateMixedRhs401,eb,← ih]
  · intro c p q a b ha hb
    cases ea : substituteMixedRhs401 sub a <;> cases eb : substituteMixedRhs401 sub b <;>
      simp [substituteMixedRhs401,evaluateMixedRhs401,ea,eb,← ha,← hb]
  · intro ps c params n use declared exacts a ih
    cases ea : substituteMixedArgs401 sub a <;>
      simp [substituteMixedRhs401,evaluateMixedRhs401,ea,← ih]
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro c p q n use prim a b ha hb
    cases ea : substituteMixedRhs401 sub a <;> cases eb : substituteMixedRhs401 sub b <;>
      simp [substituteMixedRhs401,evaluateMixedRhs401,ea,eb,← ha,← hb]
  · intro c param n kind mode mark; cases h : sub .value n mark <;> simp [substituteMixedArg401,evaluateMixedArg401,h]
  · intro c param n kind mode mark; cases h : sub .value n mark <;> simp [substituteMixedArg401,evaluateMixedArg401,h]
  · intro c param n kind mode mark; cases h : sub .row n mark <;> simp [substituteMixedArg401,evaluateMixedArg401,h]
  · intro c param n kind mode mark; cases h : sub .row n mark <;> simp [substituteMixedArg401,evaluateMixedArg401,h]
  · intro param p c kind phrase a ih
    cases ea : substituteMixedRhs401 sub a <;>
      simp [substituteMixedArg401,evaluateMixedArg401,ea,← ih]
  · intros; rfl
  · intro c ap ap' a a' first rest hf hr
    cases ef : substituteMixedArg401 sub first <;> cases er : substituteMixedArgs401 sub rest <;>
      simp [substituteMixedArgs401,evaluateMixedArgs401,ef,er,← hf,← hr]


mutual
def mixedRhsNeeds401 {s leaf c p} : MixedRhs401 s leaf c p → List (Nat × Kind)
  | .binder n _ => [(n,.value)]
  | .record _ a b | .join a b | .pair _ _ _ a b => mixedRhsNeeds401 a ++ mixedRhsNeeds401 b
  | .variant _ a => mixedRhsNeeds401 a
  | .declaredApp _ _ _ _ args => mixedArgsNeeds401 args
  | .scalar .. | .emptyRecord .. | .exactEmpty .. => []

def mixedArgNeeds401 {s leaf c k p} : MixedArg401 s leaf c k p → List (Nat × Kind)
  | .valuePoint n .. | .valueInterval n .. => [(n,.value)]
  | .rowPoint n .. | .rowInterval n .. => [(n,.row)]
  | .valueTree _ _ child => mixedRhsNeeds401 child

def mixedArgsNeeds401 {s leaf c ks ps} : MixedArgs401 s leaf c ks ps → List (Nat × Kind)
  | .nil => []
  | .cons a b => mixedArgNeeds401 a ++ mixedArgsNeeds401 b
end

/-- Every referenced role slot is witnessed at its actual kind. Missing
input is not interpreted as a mismatch or promoted to a language verdict. -/
noncomputable def instantiateMixedSlot401 {s : State} (slots : Nat → Option Capture)
    (k : Kind) (n : Nat) (_ : Unit) : Option (InstantiatedSlot401 s slots k n) := by
  classical
  exact match hit : slots n with
  | none => none
  | some cap => if fits : TypedBodyCapture392 s cap k then some ⟨cap,hit,fits⟩ else none

def sourceRead401 (m : Model) (slots : Nat → Option Capture)
    (_ : Kind) (n : Nat) (_ : Unit) : Option (Ty × Row) :=
  (slots n).map fun cap => m.assignment cap.center

def retainedRead401 (m : Model) {s slots} (k : Kind) (n : Nat)
    (read : InstantiatedSlot401 s slots k n) : Option (Ty × Row) :=
  some (m.assignment read.original.center)

theorem actual_slot_substitution_reads_original401 {s : State} {slots : Nat → Option Capture}
    {k : Kind} {n : Nat} {cap : Capture} (find : slots n = some cap)
    (fits : TypedBodyCapture392 s cap k) :
    instantiateMixedSlot401 (s := s) slots k n () = some ⟨cap,find,fits⟩ := by
  classical
  unfold instantiateMixedSlot401
  split
  next missing => rw [find] at missing; cases missing
  next captured present =>
    have same := Option.some.inj (present.symm.trans find)
    subst captured
    simp [fits]

private theorem ready_prefix401 {s slots as bs} (h : B6UsesFit398 s slots (as ++ bs)) :
    B6UsesFit398 s slots as :=
  fun x a => h x (List.mem_append.mpr (.inl a))

private theorem ready_suffix401 {s slots as bs} (h : B6UsesFit398 s slots (as ++ bs)) :
    B6UsesFit398 s slots bs :=
  fun x b => h x (List.mem_append.mpr (.inr b))

/-- Substituting the B6 tree succeeds using only the declared kinds of
the slots that appear in it. Its type index preserves the exact source
Pattern; homogeneous and heterogeneously nested nodes share the fold. -/
theorem supplied_mixed_tree_substitution_succeeds401 {s c p}
    (slots : Nat → Option Capture) (plan : B6MixedRhs401 s c p)
    (ready : B6UsesFit398 s slots (mixedRhsNeeds401 plan)) :
    ∃ tree : RetainedTree401 s slots c p,
      substituteMixedRhs401 (instantiateMixedSlot401 (s := s) slots) plan = some tree := by
  revert ready
  refine MixedRhs401.rec
    (motive_1 := fun _ _ t => B6UsesFit398 s slots (mixedRhsNeeds401 t) → ∃ tree,
      substituteMixedRhs401 (instantiateMixedSlot401 (s := s) slots) t = some tree)
    (motive_2 := fun _ _ _ t => B6UsesFit398 s slots (mixedArgNeeds401 t) → ∃ tree,
      substituteMixedArg401 (instantiateMixedSlot401 (s := s) slots) t = some tree)
    (motive_3 := fun _ _ _ t => B6UsesFit398 s slots (mixedArgsNeeds401 t) → ∃ tree,
      substituteMixedArgs401 (instantiateMixedSlot401 (s := s) slots) t = some tree)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ plan
  · intro c n tok h
    obtain ⟨cap,got,fits⟩ := h (n,.value) List.mem_cons_self
    cases tok
    exact ⟨.binder n ⟨cap,got,fits⟩, by simp only [substituteMixedRhs401,
      actual_slot_substitution_reads_original401 got fits,Option.map_some]⟩
  · intro c p q label a b ha hb h
    obtain ⟨x,hx⟩ := ha (ready_prefix401 h)
    obtain ⟨y,hy⟩ := hb (ready_suffix401 h)
    exact ⟨.record label x y, by simp [substituteMixedRhs401,hx,hy]⟩
  · intro c p tag a ha h
    obtain ⟨x,hx⟩ := ha h
    exact ⟨.variant tag x, by simp [substituteMixedRhs401,hx]⟩
  · intro c p q a b ha hb h
    obtain ⟨x,hx⟩ := ha (ready_prefix401 h)
    obtain ⟨y,hy⟩ := hb (ready_suffix401 h)
    exact ⟨.join x y, by simp [substituteMixedRhs401,hx,hy]⟩
  · intro ps c params n use kinds exacts a ha h
    obtain ⟨x,hx⟩ := ha h
    exact ⟨.declaredApp n use kinds exacts x, by simp [substituteMixedRhs401,hx]⟩
  · intros; exact ⟨_,rfl⟩
  · intros; exact ⟨_,rfl⟩
  · intros; exact ⟨_,rfl⟩
  · intro c a b n use kind x y hx hy h
    obtain ⟨vx,ex⟩ := hx (ready_prefix401 h)
    obtain ⟨vy,ey⟩ := hy (ready_suffix401 h)
    exact ⟨.pair n use kind vx vy,by simp [substituteMixedRhs401,ex,ey]⟩
  · intro c p n kind mode tok h
    obtain ⟨cap,got,fits⟩ := h (n,.value) List.mem_cons_self
    cases tok
    exact ⟨.valuePoint n kind mode ⟨cap,got,fits⟩, by simp only [substituteMixedArg401,
      actual_slot_substitution_reads_original401 got fits,Option.map_some]⟩
  · intro c p n kind mode tok h
    obtain ⟨cap,got,fits⟩ := h (n,.value) List.mem_cons_self
    cases tok
    exact ⟨.valueInterval n kind mode ⟨cap,got,fits⟩, by simp only [substituteMixedArg401,
      actual_slot_substitution_reads_original401 got fits,Option.map_some]⟩
  · intro c p n kind mode tok h
    obtain ⟨cap,got,fits⟩ := h (n,.row) List.mem_cons_self
    cases tok
    exact ⟨.rowPoint n kind mode ⟨cap,got,fits⟩, by simp only [substituteMixedArg401,
      actual_slot_substitution_reads_original401 got fits,Option.map_some]⟩
  · intro c p n kind mode tok h
    obtain ⟨cap,got,fits⟩ := h (n,.row) List.mem_cons_self
    cases tok
    exact ⟨.rowInterval n kind mode ⟨cap,got,fits⟩, by simp only [substituteMixedArg401,
      actual_slot_substitution_reads_original401 got fits,Option.map_some]⟩
  · intro p pat c kind compound a ha h
    obtain ⟨x,hx⟩ := ha h
    exact ⟨.valueTree kind compound x, by simp [substituteMixedArg401,hx]⟩
  · intros; exact ⟨.nil,rfl⟩
  · intro c ap aps p ps a b ha hb h
    obtain ⟨x,hx⟩ := ha (ready_prefix401 h)
    obtain ⟨y,hy⟩ := hb (ready_suffix401 h)
    exact ⟨.cons x y,by simp [substituteMixedArgs401,hx,hy]⟩


/-- Only the used value/row references can affect the denotation.
This applies equally to the source syntax and the retained tree. -/
theorem mixed_value_reads_exact_footprint401 {s c p} {leaf : Kind → Nat → Type}
    (left right : ∀ k n, leaf k n → Option (Ty × Row))
    (plan : MixedRhs401 s leaf c p)
    (agree : ∀ k n, (n,k) ∈ mixedRhsNeeds401 plan → ∀ x, left k n x = right k n x) :
    evaluateMixedRhs401 left plan = evaluateMixedRhs401 right plan := by
  revert agree
  refine MixedRhs401.rec
    (motive_1 := fun _ _ t => (∀ k n, (n,k) ∈ mixedRhsNeeds401 t →
      ∀ x, left k n x = right k n x) → evaluateMixedRhs401 left t = evaluateMixedRhs401 right t)
    (motive_2 := fun _ _ _ t => (∀ k n, (n,k) ∈ mixedArgNeeds401 t →
      ∀ x, left k n x = right k n x) → evaluateMixedArg401 left t = evaluateMixedArg401 right t)
    (motive_3 := fun _ _ _ t => (∀ k n, (n,k) ∈ mixedArgsNeeds401 t →
      ∀ x, left k n x = right k n x) → evaluateMixedArgs401 left t = evaluateMixedArgs401 right t)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ plan
  · intro c n mark h; simp only [evaluateMixedRhs401,h .value n List.mem_cons_self mark]
  · intro c p q label a b ha hb h
    simp only [evaluateMixedRhs401,ha (fun k n h' => h k n (List.mem_append_left _ h')),
      hb (fun k n h' => h k n (List.mem_append_right _ h'))]
  · intro c p tag a ha h; simp only [evaluateMixedRhs401,ha h]
  · intro c p q a b ha hb h
    simp only [evaluateMixedRhs401,ha (fun k n h' => h k n (List.mem_append_left _ h')),
      hb (fun k n h' => h k n (List.mem_append_right _ h'))]
  · intro ps c params n use declared exacts a ih h; simp only [evaluateMixedRhs401,ih h]
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro c p q n use prim a b ha hb h
    simp only [evaluateMixedRhs401,ha (fun k n h' => h k n (List.mem_append_left _ h')),
      hb (fun k n h' => h k n (List.mem_append_right _ h'))]
  · intro c param n kind mode mark h; simp only [evaluateMixedArg401,h .value n List.mem_cons_self mark]
  · intro c param n kind mode mark h; simp only [evaluateMixedArg401,h .value n List.mem_cons_self mark]
  · intro c param n kind mode mark h; simp only [evaluateMixedArg401,h .row n List.mem_cons_self mark]
  · intro c param n kind mode mark h; simp only [evaluateMixedArg401,h .row n List.mem_cons_self mark]
  · intro param p c kind phrase a ih h; simp only [evaluateMixedArg401,ih h]
  · intros; rfl
  · intro c ap ap' a a' first rest hf hr h
    simp only [evaluateMixedArgs401,hf (fun k n h' => h k n (List.mem_append_left _ h')),
      hr (fun k n h' => h k n (List.mem_append_right _ h'))]

/-- A well-bound retained tree is meaningful in every model. The
four primitive cases use the canonical primitive operation rather
than reading that head as a nominal constructor. -/
theorem mixed_value_total_on_bound_leaves401 {s c p} {leaf : Kind → Nat → Type}
    (get : ∀ k n, leaf k n → Option (Ty × Row))
    (full : ∀ k n x, ∃ value, get k n x = some value)
    (plan : MixedRhs401 s leaf c p) :
    ∃ value, evaluateMixedRhs401 get plan = some value := by
  refine MixedRhs401.rec
    (motive_1 := fun _ _ t => ∃ value, evaluateMixedRhs401 get t = some value)
    (motive_2 := fun _ _ _ t => ∃ value, evaluateMixedArg401 get t = some value)
    (motive_3 := fun _ _ _ t => ∃ value, evaluateMixedArgs401 get t = some value)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ plan
  · intro c n mark
    obtain ⟨x,hx⟩ := full .value n mark
    exact ⟨x.1, by simp [evaluateMixedRhs401,hx]⟩
  · intro c p q label a b ha hb
    obtain ⟨x,hx⟩ := ha
    obtain ⟨y,hy⟩ := hb
    exact ⟨record label x y,by simp [evaluateMixedRhs401,hx,hy]⟩
  · intro c p tag a ha
    obtain ⟨x,hx⟩ := ha
    exact ⟨variant tag x,by simp [evaluateMixedRhs401,hx]⟩
  · intro c p q a b ha hb
    obtain ⟨x,hx⟩ := ha
    obtain ⟨y,hy⟩ := hb
    exact ⟨.union x y,by simp [evaluateMixedRhs401,hx,hy]⟩
  · intro ps c params n use declared exacts a ih
    obtain ⟨x,hx⟩ := ih
    exact ⟨nominal n x,by simp [evaluateMixedRhs401,hx]⟩
  · intros; exact ⟨_,rfl⟩
  · intros; exact ⟨_,rfl⟩
  · intros; exact ⟨_,rfl⟩
  · intro c p q n use prim a b ha hb
    obtain ⟨x,hx⟩ := ha
    obtain ⟨y,hy⟩ := hb
    exact ⟨primitiveValue .pair [x,y],by simp [evaluateMixedRhs401,hx,hy]⟩
  · intro c p n k v mark
    obtain ⟨x,hx⟩ := full .value n mark
    exact ⟨.inl x.1,by simp [evaluateMixedArg401,hx]⟩
  · intro c p n k v mark
    obtain ⟨x,hx⟩ := full .value n mark
    exact ⟨.inl x.1,by simp [evaluateMixedArg401,hx]⟩
  · intro c p n k v mark
    obtain ⟨x,hx⟩ := full .row n mark
    exact ⟨.inr x.2,by simp [evaluateMixedArg401,hx]⟩
  · intro c p n k v mark
    obtain ⟨x,hx⟩ := full .row n mark
    exact ⟨.inr x.2,by simp [evaluateMixedArg401,hx]⟩
  · intro param p c kind phrase a ih
    obtain ⟨x,hx⟩ := ih
    exact ⟨.inl x,by simp [evaluateMixedArg401,hx]⟩
  · intros; exact ⟨[],rfl⟩
  · intro c ap ap' a a' first rest hf hr
    obtain ⟨x,hx⟩ := hf
    obtain ⟨y,hy⟩ := hr
    exact ⟨x::y,by simp [evaluateMixedArgs401,hx,hy]⟩

theorem exact_mixed_source_and_retained_values401 {s c p}
    {slots : Nat → Option Capture} {plan : B6MixedRhs401 s c p}
    {tree : RetainedTree401 s slots c p}
    (ready : B6UsesFit398 s slots (mixedRhsNeeds401 plan))
    (made : substituteMixedRhs401 (instantiateMixedSlot401 (s := s) slots) plan = some tree)
    (m : Model) :
    ∃ value, evaluateMixedRhs401 (retainedRead401 m) tree = some value ∧
      evaluateMixedRhs401 (sourceRead401 m slots) plan = some value := by
  have matched := mixed_substitution_value_fusion401 (instantiateMixedSlot401 (s := s) slots)
    (retainedRead401 m) plan
  rw [made] at matched
  change evaluateMixedRhs401 (retainedRead401 m) tree = _ at matched
  have same := mixed_value_reads_exact_footprint401
    (fun k n x => (instantiateMixedSlot401 (s := s) slots k n x).bind (retainedRead401 m k n))
    (sourceRead401 m slots) plan (by
      intro k n used x
      obtain ⟨cap,hit,fits⟩ := ready (n,k) used
      cases x
      rw [actual_slot_substitution_reads_original401 hit fits]
      simp [retainedRead401,sourceRead401,hit])
  obtain ⟨v,read⟩ := mixed_value_total_on_bound_leaves401
    (retainedRead401 m) (fun _ _ a => ⟨m.assignment a.original.center,rfl⟩) tree
  exact ⟨v,read,same.symm.trans (matched.symm.trans read)⟩


open GeneralDeclarativeWitnessConstructorModes357 (Environment Layout)
open GeneralSourceMetadataRows291 (primitives)
open GeneralSourceMetadataBundle291 (registry)

theorem mixed_primitive_has_exact_authored_mode401 {e : Environment} {n a : Nat}
    (use : Use e n a) (prim : Primitive) (isPrimitive : use.mode = .primitive prim) :
    (registry e.source).constructors n = some use.declared ∧
      primitives e.source.snapshot n = some prim ∧
      use.declared.parameters = prim.parameters ∧ prim.parameters.length = a := by
  have origin := use.sourced
  have parameters := use.kinded
  rw [isPrimitive] at origin parameters
  have exactArity := use.exactArity
  change use.declared.parameters = prim.parameters at parameters
  rw [parameters] at exactArity
  cases origin with
  | primitive found _ => exact ⟨use.actual,found,parameters,exactArity⟩

end Yulang.GeneralDeclarativeI65
