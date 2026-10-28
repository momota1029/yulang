import YulangClosure.HigherOrderSyntax

/-! Candidate immutable value-graph theory. Independent research syntax, NOT a
native heap model. `roll` below is an identity-typed transparent marker, not the
paper's iso-recursive introduction. The full paper parent remains open. -/
namespace YulangClosure.GuardedValueGraph

inductive Ty where
  | unit | bottom
  | product (left right : Ty)
  | arrow (argument result : Ty)
  | thunk (result : Ty)
  deriving DecidableEq

/-- Bodies have explicit graph references and variables. No evaluation assumption. -/
inductive Term (R V : Type) where
  | ref (reference : R)
  | var (index : V)
  | unit
  | app (function argument : Term R V)
  | force (thunk : Term R V)

def Term.subst (fr : R → Term S W) (fv : V → Term S W) : Term R V → Term S W
  | .ref r => fr r
  | .var v => fv v
  | .unit => .unit
  | .app f a => .app (f.subst fr fv) (a.subst fr fv)
  | .force t => .force (t.subst fr fv)

inductive Typed (xi : R → Ty) (gamma : V → Ty) : Term R V → Ty → Prop where
  | ref (r) : Typed xi gamma (.ref r) (xi r)
  | var (v) : Typed xi gamma (.var v) (gamma v)
  | unit : Typed xi gamma .unit .unit
  | app : Typed xi gamma f (.arrow a b) → Typed xi gamma x a →
      Typed xi gamma (.app f x) b
  | force : Typed xi gamma t (.thunk a) → Typed xi gamma (.force t) a

theorem typed_subst {xi : R → Ty} {gamma : V → Ty}
    {yi : S → Ty} {delta : W → Ty} {t : Term R V} {a : Ty}
    (h : Typed xi gamma t a) (fr : R → Term S W) (fv : V → Term S W)
    (hr : ∀ r, Typed yi delta (fr r) (xi r))
    (hv : ∀ v, Typed yi delta (fv v) (gamma v)) :
    Typed yi delta (t.subst fr fv) a := by
  induction h with
  | ref r => exact hr r
  | var v => exact hv v
  | unit => exact .unit
  | app _ _ ihf iha => exact .app ihf iha
  | force _ ih => exact .force ih

def emptyTy : Empty → Ty := Empty.elim

def argTy (a : Ty) : Option Empty → Ty
  | none => a
  | some e => Empty.elim e

inductive Node (R : Type) where
  | unit
  | pair (left right : R)
  | lam (argument result : Ty) (body : Term R (Option Empty))
  | delay (result : Ty) (body : Term R Empty)
  | alias (target : R)
  | view (metadata : Nat) (target : R)
  | roll (target : R)
  | evidence (metadata : Nat) (target : R)

/-- Exactly the transparent edge; data fields and code references are guards. -/
def Node.next : Node R → Option R
  | .alias r | .view _ r | .roll r | .evidence _ r => some r
  | _ => none

def Node.map (f : R → S) : Node R → Node S
  | .unit => .unit
  | .pair l r => .pair (f l) (f r)
  | .lam a b body => .lam a b (body.subst (fun r => .ref (f r)) .var)
  | .delay a body => .delay a (body.subst (fun r => .ref (f r)) .var)
  | .alias r => .alias (f r)
  | .view m r => .view m (f r)
  | .roll r => .roll (f r)
  | .evidence m r => .evidence m (f r)

theorem next_map (f : R → S) (n : Node R) :
    (n.map f).next = n.next.map f := by cases n <;> rfl

inductive NodeTyped (xi : R → Ty) : Node R → Ty → Prop where
  | unit : NodeTyped xi .unit .unit
  | pair (l r) : NodeTyped xi (.pair l r) (.product (xi l) (xi r))
  | lam : Typed xi (argTy a) body b → NodeTyped xi (.lam a b body) (.arrow a b)
  | delay : Typed xi emptyTy body a → NodeTyped xi (.delay a body) (.thunk a)
  | alias (r) : NodeTyped xi (.alias r) (xi r)
  | view (m r) : NodeTyped xi (.view m r) (xi r)
  | roll (r) : NodeTyped xi (.roll r) (xi r)
  | evidence (m r) : NodeTyped xi (.evidence m r) (xi r)

theorem node_map {xi : R → Ty} {yi : S → Ty} {n : Node R} {a : Ty}
    (f : R → S) (hf : ∀ r, yi (f r) = xi r) (h : NodeTyped xi n a) :
    NodeTyped yi (n.map f) a := by
  induction h with
  | unit => exact .unit
  | pair l r => simpa only [Node.map, hf] using NodeTyped.pair (xi := yi) (f l) (f r)
  | lam hb =>
      apply NodeTyped.lam
      exact typed_subst hb _ _ (fun r => by simpa only [hf] using Typed.ref (xi := yi) (gamma := argTy _) (f r)) (fun v => .var v)
  | delay hb =>
      apply NodeTyped.delay
      exact typed_subst hb _ _ (fun r => by simpa only [hf] using Typed.ref (xi := yi) (gamma := emptyTy) (f r)) (fun v => .var v)
  | alias r => simpa only [Node.map, hf] using NodeTyped.alias (xi := yi) (f r)
  | view m r => simpa only [Node.map, hf] using NodeTyped.view (xi := yi) m (f r)
  | roll r => simpa only [Node.map, hf] using NodeTyped.roll (xi := yi) (f r)
  | evidence m r => simpa only [Node.map, hf] using NodeTyped.evidence (xi := yi) m (f r)

abbrev Graph (R : Type) := R → Node R
abbrev FiniteGraph (size : Nat) := Graph (Fin size)
def WellTyped (g : Graph R) (xi : R → Ty) : Prop := ∀ r, NodeTyped xi (g r) (xi r)

/-- A finite numeric certificate for transparent edges only. `bound` enables
allocation into a larger graph without computing a maximum or using choice. -/
structure Guarded (g : Graph R) where
  rank : R → Nat
  ceiling : Nat
  bound : ∀ r, rank r < ceiling
  decrease : ∀ r s, (g r).next = some s → rank s < rank r

inductive Observes (g : Graph R) : R → Node R → Prop where
  | done (r) : (g r).next = none → Observes g r (g r)
  | step : (g r).next = some s → Observes g s n → Observes g r n

theorem finite_observation (g : Graph R) (guard : Guarded g) (r : R) :
    ∃ n, Observes g r n := by
  have aux : ∀ k r, guard.rank r < k → ∃ n, Observes g r n := by
    intro k
    induction k with
    | zero => intro r h; exact False.elim (Nat.not_lt_zero _ h)
    | succ k ih =>
        intro r h
        cases hn : (g r).next with
        | none => exact ⟨g r, .done r hn⟩
        | some s =>
            have hs : guard.rank s < k := Nat.lt_of_lt_of_le
              (guard.decrease r s hn) (Nat.le_of_lt_succ h)
            obtain ⟨n, ho⟩ := ih s hs
            exact ⟨n, .step hn ho⟩
  exact aux (guard.rank r + 1) r (Nat.lt_succ_self _)

theorem transparent_type {xi : R → Ty} {n : Node R} {a : Ty}
    (h : NodeTyped xi n a) (hn : n.next = some s) : xi s = a := by
  cases h with
  | unit => cases hn
  | pair l r => cases hn
  | lam hb => cases hn
  | delay hb => cases hn
  | alias r => cases hn; rfl
  | view m r => cases hn; rfl
  | roll r => cases hn; rfl
  | evidence m r => cases hn; rfl

theorem observation_typed {g : Graph R} {xi : R → Ty} (hg : WellTyped g xi)
    {r : R} {n : Node R} (h : Observes g r n) :
    NodeTyped xi n (xi r) ∧ n.next = none := by
  induction h with
  | done r hn => exact ⟨hg r, hn⟩
  | @step r s n hs ho ih =>
      have he := transparent_type (hg r) hs
      exact ⟨he ▸ ih.1, ih.2⟩

/-- Canonical terminal nodes, derived by inversion of concrete node typing. -/
inductive Canonical : Ty → Node R → Prop where
  | unit : Canonical .unit .unit
  | pair (l r) : Canonical (.product a b) (.pair l r)
  | lam (body) : Canonical (.arrow a b) (.lam a b body)
  | delay (body) : Canonical (.thunk a) (.delay a body)

theorem terminal_canonical {xi : R → Ty} {n : Node R} {a : Ty}
    (h : NodeTyped xi n a) (hn : n.next = none) : Canonical a n := by
  cases h with
  | unit => exact .unit
  | pair l r => exact .pair l r
  | lam hb => exact .lam _
  | delay hb => exact .delay _
  | alias r => cases hn
  | view m r => cases hn
  | roll r => cases hn
  | evidence m r => cases hn

theorem reference_canonical {g : Graph R} {xi : R → Ty}
    (hg : WellTyped g xi) (guard : Guarded g) (r : R) :
    ∃ n, Observes g r n ∧ Canonical (xi r) n := by
  obtain ⟨n, ho⟩ := finite_observation g guard r
  obtain ⟨ht, hn⟩ := observation_typed hg ho
  exact ⟨n, ho, terminal_canonical ht hn⟩

theorem no_bottom_reference {g : Graph R} {xi : R → Ty}
    (hg : WellTyped g xi) (guard : Guarded g) (r : R) : xi r ≠ .bottom := by
  intro hb
  obtain ⟨n, _, hc⟩ := reference_canonical hg guard r
  rw [hb] at hc
  cases hc

/-- Nonempty paths in the transparent subgraph, not in the whole graph. -/
inductive TransparentPath (g : Graph R) : R → R → Prop where
  | edge : (g r).next = some s → TransparentPath g r s
  | cons : (g r).next = some s → TransparentPath g s t → TransparentPath g r t

theorem transparent_path_rank {g : Graph R} (guard : Guarded g)
    {r s : R} (h : TransparentPath g r s) : guard.rank s < guard.rank r := by
  induction h with
  | edge h => exact guard.decrease _ _ h
  | cons h _ ih => exact Nat.lt_trans ih (guard.decrease _ _ h)

theorem no_transparent_cycle {g : Graph R} (guard : Guarded g) (r : R) :
    TransparentPath g r r → False := by
  intro h
  exact Nat.lt_irrefl _ (transparent_path_rank guard h)

theorem no_transparent_self {g : Graph R} (guard : Guarded g) (r : R) :
    (g r).next ≠ some r := by
  intro h
  exact Nat.lt_irrefl _ (guard.decrease r r h)

theorem no_transparent_two_cycle {g : Graph R} (guard : Guarded g) (r s : R)
    (h : (g r).next = some s) : (g s).next ≠ some r := by
  intro h'
  exact Nat.lt_irrefl _ (Nat.lt_trans (guard.decrease r s h) (guard.decrease s r h'))

/-- Simultaneous allocation uses disjoint constructors, so all new names exist
before typing their bodies and no new reference can collide with an old one. -/
def joinTy (xi : R → Ty) (nu : S → Ty) : Sum R S → Ty
  | .inl r => xi r
  | .inr s => nu s

def allocate (g : Graph R) (fresh : S → Node (Sum R S)) : Graph (Sum R S)
  | .inl r => (g r).map Sum.inl
  | .inr s => fresh s

theorem allocation_old_node (g : Graph R) (fresh : S → Node (Sum R S)) (r : R) :
    allocate g fresh (.inl r) = (g r).map Sum.inl := rfl

/-- Old observations are preserved by the injective reference renaming. -/
theorem allocation_observation {g : Graph R} (fresh : S → Node (Sum R S))
    {r : R} {n : Node R} (h : Observes g r n) :
    Observes (allocate g fresh) (.inl r) (n.map Sum.inl) := by
  induction h with
  | done r hn =>
      apply Observes.done
      simp only [allocate, next_map, hn, Option.map_none]
  | @step r s n hs _ ih =>
      apply Observes.step (s := Sum.inl s)
      · simp only [allocate, next_map, hs, Option.map_some]
      · exact ih

theorem allocation_old_type (xi : R → Ty) (nu : S → Ty) (r : R) :
    joinTy xi nu (.inl r) = xi r := rfl

theorem fresh_no_collision (r : R) (s : S) :
    (Sum.inl r : Sum R S) ≠ Sum.inr s := by intro h; cases h

theorem allocate_typed {g : Graph R} {xi : R → Ty} {nu : S → Ty}
    (hg : WellTyped g xi) (fresh : S → Node (Sum R S))
    (hf : ∀ s, NodeTyped (joinTy xi nu) (fresh s) (nu s)) :
    WellTyped (allocate g fresh) (joinTy xi nu) := by
  intro r
  cases r with
  | inl r => exact node_map Sum.inl (fun _ => rfl) (hg r)
  | inr s => exact hf s

/-- New-to-old transparent edges are harmless. Only new-to-new transparent
edges need the local rec guard check. Old nodes never acquire edges to new nodes. -/
def allocate_guard {g : Graph R} (guard : Guarded g)
    (fresh : S → Node (Sum R S)) (rank : S → Nat) (ceiling : Nat)
    (bound : ∀ s, rank s < ceiling)
    (decrease : ∀ s t, (fresh s).next = some (.inr t) → rank t < rank s) :
    Guarded (allocate g fresh) where
  rank := fun r => match r with
    | .inl r => guard.rank r
    | .inr s => guard.ceiling + rank s
  ceiling := guard.ceiling + ceiling
  bound := by
    intro r
    cases r with
    | inl r => exact Nat.lt_of_lt_of_le (guard.bound r) (Nat.le_add_right _ _)
    | inr s => exact Nat.add_lt_add_left (bound s) _
  decrease := by
    intro r t h
    cases r with
    | inl r =>
        change ((g r).map Sum.inl).next = some t at h
        rw [next_map] at h
        cases hn : (g r).next with
        | none => simp [hn] at h
        | some s =>
            simp only [hn, Option.map_some] at h
            cases h
            exact guard.decrease r s hn
    | inr s =>
        change (fresh s).next = some t at h
        cases t with
        | inl r => exact Nat.lt_of_lt_of_le (guard.bound r) (Nat.le_add_right _ _)
        | inr t => exact Nat.add_lt_add_left (decrease s t h) _

/-- The rec body is closed by simultaneous replacement of every recursive
variable by its allocated reference. Mutual dependencies do not require an order. -/
def closeBody (body : Term R S) : Term (Sum R S) Empty :=
  body.subst (fun r => .ref (.inl r)) (fun s => .ref (.inr s))

theorem closeBody_typed {xi : R → Ty} {nu : S → Ty} {body : Term R S} {a : Ty}
    (h : Typed xi nu body a) : Typed (joinTy xi nu) emptyTy (closeBody body) a :=
  typed_subst (yi := joinTy xi nu) (delta := emptyTy) h _ _
    (fun r => Typed.ref (Sum.inl r)) (fun s => Typed.ref (Sum.inr s))

theorem old_body_weakening {xi : R → Ty} (nu : S → Ty) {gamma : V → Ty}
    {body : Term R V} {a : Ty} (h : Typed xi gamma body a) :
    Typed (joinTy xi nu) gamma (body.subst (fun r => .ref (.inl r)) .var) a :=
  typed_subst (yi := joinTy xi nu) (delta := gamma) h _ _
    (fun r => Typed.ref (Sum.inl r)) (fun v => Typed.var v)

/-- The conjunction applies allocation lemmas to the parent graph-extension
obligation for this syntax; typing and the local guard are separate premises. -/
theorem rec_extension {g : Graph R} {xi : R → Ty} {nu : S → Ty}
    (hg : WellTyped g xi) (guard : Guarded g)
    (fresh : S → Node (Sum R S))
    (hf : ∀ s, NodeTyped (joinTy xi nu) (fresh s) (nu s))
    (rank : S → Nat) (ceiling : Nat) (bound : ∀ s, rank s < ceiling)
    (decrease : ∀ s t, (fresh s).next = some (.inr t) → rank t < rank s)
    {body : Term R S} {a : Ty} (hb : Typed xi nu body a) :
    WellTyped (allocate g fresh) (joinTy xi nu) ∧
    (∀ r, ∃ n, Observes (allocate g fresh) r n ∧ Canonical (joinTy xi nu r) n) ∧
    Typed (joinTy xi nu) emptyTy (closeBody body) a := by
  have ht := allocate_typed hg fresh hf
  have hg' := allocate_guard guard fresh rank ceiling bound decrease
  exact ⟨ht, reference_canonical ht hg', closeBody_typed hb⟩

/-- Genuine mutual lambda recursion: each body calls the other node. -/
def mutualLambda : Graph Bool
  | false => .lam .unit .unit (.app (.ref true) (.var none))
  | true => .lam .unit .unit (.app (.ref false) (.var none))

def mutualLambdaTy : Bool → Ty := fun _ => .arrow .unit .unit

theorem mutualLambda_typed : WellTyped mutualLambda mutualLambdaTy := by
  intro r
  cases r <;> exact NodeTyped.lam (Typed.app (Typed.ref _) (Typed.var none))

def mutualLambda_guard : Guarded mutualLambda where
  rank := fun _ => 0
  ceiling := 1
  bound := fun _ => Nat.zero_lt_succ _
  decrease := by intro r s h; cases r <;> cases h

/-- Shared child references are allowed, independently of whether their ranks
are lower: a pair node is a genuine constructor guard. -/
def sharedPair : Graph Bool
  | false => .unit
  | true => .pair false false

def sharedPairTy : Bool → Ty
  | false => .unit
  | true => .product .unit .unit

theorem sharedPair_typed : WellTyped sharedPair sharedPairTy := by
  intro r
  cases r
  · exact .unit
  · exact .pair false false

def sharedPair_guard : Guarded sharedPair where
  rank := fun _ => 0
  ceiling := 1
  bound := fun _ => Nat.zero_lt_succ _
  decrease := by intro r s h; cases r <;> cases h

/-- Typing alone permits a bogus bottom cycle. The guard certificate rejects it. -/
def transparentCycle : Graph Bool
  | false => .view 7 true
  | true => .roll false

theorem transparentCycle_typed_bottom : WellTyped transparentCycle (fun _ => .bottom) := by
  intro r
  cases r
  · exact .view 7 true
  · exact .roll false

theorem transparentCycle_unguarded : Guarded transparentCycle → False := by
  intro guard
  exact no_transparent_two_cycle guard false true rfl rfl

def emptyGraph : Graph Empty := Empty.elim

def emptyGuard : Guarded emptyGraph where
  rank := Empty.elim
  ceiling := 0
  bound := by intro r; cases r
  decrease := fun r => Empty.elim r

theorem emptyGraph_typed : WellTyped emptyGraph emptyTy := by intro r; cases r

/-- An actual allocation of both mutually recursive functions at once. -/
def mutualFresh (b : Bool) : Node (Sum Empty Bool) := (mutualLambda b).map Sum.inr

def allocatedMutual : Graph (Sum Empty Bool) := allocate emptyGraph mutualFresh

theorem mutualFresh_typed (b : Bool) :
    NodeTyped (joinTy emptyTy mutualLambdaTy) (mutualFresh b) (mutualLambdaTy b) :=
  node_map Sum.inr (fun _ => rfl) (mutualLambda_typed b)

theorem allocatedMutual_typed :
    WellTyped allocatedMutual (joinTy emptyTy mutualLambdaTy) :=
  allocate_typed emptyGraph_typed mutualFresh mutualFresh_typed

def allocatedMutual_guard : Guarded allocatedMutual :=
  allocate_guard emptyGuard mutualFresh (fun _ => 0) 1
    (fun _ => Nat.zero_lt_succ _) (by intro s t h; cases s <;> cases h)

theorem allocatedMutual_observes (b : Bool) :
    ∃ n, Observes allocatedMutual (.inr b) n ∧ Canonical (.arrow .unit .unit) n :=
  reference_canonical allocatedMutual_typed allocatedMutual_guard (.inr b)

/-- Freshness and per-node typing do not suffice: a fresh self-alias is rejected. -/
def badFresh (_ : Unit) : Node (Sum Empty Unit) := .alias (.inr ())

theorem badFresh_typed (u : Unit) :
    NodeTyped (joinTy emptyTy (fun _ : Unit => Ty.bottom)) (badFresh u) .bottom :=
  NodeTyped.alias (xi := joinTy emptyTy (fun _ : Unit => Ty.bottom)) (Sum.inr ())

theorem badAllocation_typed :
    WellTyped (allocate emptyGraph badFresh) (joinTy emptyTy (fun _ : Unit => Ty.bottom)) :=
  allocate_typed emptyGraph_typed badFresh badFresh_typed

theorem badAllocation_unguarded : Guarded (allocate emptyGraph badFresh) → False := by
  intro guard
  exact no_transparent_self guard (.inr ()) rfl

end YulangClosure.GuardedValueGraph
