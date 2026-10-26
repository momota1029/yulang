import YulangClosure.SimpleSubConstraintSoundness
import YulangClosure.SimpleSubRegularSolutions

/-! Backward constraint soundness for the guarded regular graph fragment.
Final finite acceptance supplies the same regular interpretation of every
original demand; no finite-Term valuation or solution is an input.
This graph-indexed history is not a Rust trace correspondence theorem.
Union/intersection, aliases, native row tails, ordinary coalescing and original
source generation remain outside this precisely represented fragment. -/
namespace YulangClosure.SimpleSub.Regular

def ZipRel {α : Type} (relation : α → α → Prop) : List α → List α → Prop
  | [], [] => True
  | x :: xs, y :: ys => relation x y ∧ ZipRel relation xs ys
  | _, _ => False

def HoldsExpansion (relation : Comparison → Prop) : Option (List Comparison) → Prop
  | none => False
  | some children => ∀ child, child ∈ children → relation child

@[simp] theorem holdsExpansion_some (relation : Comparison → Prop) (children : List Comparison) :
    HoldsExpansion relation (some children) ↔ ∀ c, c ∈ children → relation c := Iff.rfl

@[simp] theorem holdsExpansion_none (relation : Comparison → Prop) :
    ¬ HoldsExpansion relation none := id

theorem holdsExpansion_iff (relation : Comparison → Prop) (expanded : Option (List Comparison)) :
    HoldsExpansion relation expanded ↔
      ∃ children, expanded = some children ∧ ∀ c, c ∈ children → relation c := by
  cases expanded <;> simp [HoldsExpansion]

@[simp] theorem holdsExpansion_cons (relation : Comparison → Prop) (pair : Comparison)
    (tail : Option (List Comparison)) :
    HoldsExpansion relation (tail.map (pair :: ·)) ↔
      relation pair ∧ HoldsExpansion relation tail := by
  cases tail <;> simp [HoldsExpansion]

theorem pairLists_holds (relation : Comparison → Prop) (k : Kind) (xs ys : List Nat) :
    HoldsExpansion relation (pairLists k xs ys) ↔
      ZipRel (fun x y => relation ⟨k,x,y⟩) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [pairLists, HoldsExpansion, ZipRel]
  | cons x xs ih => cases ys <;> simp [pairLists, ih, ZipRel]

theorem recordPairs_holds (relation : Comparison → Prop) (xs ys : List Field) :
    HoldsExpansion relation (recordPairs xs ys) ↔
      ZipRel (fun x y => x.label = y.label ∧ x.optional = y.optional ∧
        relation ⟨.value,x.child,y.child⟩) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [recordPairs, HoldsExpansion, ZipRel]
  | cons x xs ih =>
      cases ys with
      | nil => simp [recordPairs, HoldsExpansion, ZipRel]
      | cons y ys =>
          by_cases h : x.label = y.label ∧ x.optional = y.optional
          · simp [recordPairs, h, ih, ZipRel]
          · simp only [recordPairs, h, ↓reduceIte, HoldsExpansion, ZipRel, false_iff]
            intro bad
            exact h ⟨bad.1.1,bad.1.2.1⟩

theorem variantPairs_holds (relation : Comparison → Prop) (xs ys : List Alternative) :
    HoldsExpansion relation (variantPairs xs ys) ↔
      ZipRel (fun x y => x.tag = y.tag ∧
        ZipRel (fun a b => relation ⟨.value,a,b⟩) x.payloads y.payloads) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [variantPairs, HoldsExpansion, ZipRel]
  | cons x xs ih =>
      cases ys with
      | nil => simp [variantPairs, HoldsExpansion, ZipRel]
      | cons y ys =>
          have hp := pairLists_holds relation .value x.payloads y.payloads
          by_cases ht : x.tag = y.tag
          · have hi := ih ys
            cases h₁ : pairLists .value x.payloads y.payloads <;>
              cases h₂ : variantPairs xs ys <;>
              simp [variantPairs, ht, h₁, h₂, HoldsExpansion, List.mem_append,
                ZipRel, forall_and, or_imp] at hp hi ⊢ <;> first | simp_all | assumption
          · simp [variantPairs, ht, HoldsExpansion, ZipRel]

def NodeRel (relation : Comparison → Prop) : {k : Kind} → Node k → Node k → Prop
  | _, .bottom, _ => True
  | _, _, .top => True
  | _, .atom x, .atom y => x = y
  | .value, .function a ae re r, .function b be se s =>
      relation ⟨.value,b,a⟩ ∧ relation ⟨.effect,be,ae⟩ ∧
      relation ⟨.effect,re,se⟩ ∧ relation ⟨.value,r,s⟩
  | .value, .record xs, .record ys =>
      ZipRel (fun x y => x.label = y.label ∧ x.optional = y.optional ∧
        relation ⟨.value,x.child,y.child⟩) xs ys
  | .value, .tuple xs, .tuple ys => ZipRel (fun x y => relation ⟨.value,x,y⟩) xs ys
  | .value, .variant xs, .variant ys =>
      ZipRel (fun x y => x.tag = y.tag ∧
        ZipRel (fun a b => relation ⟨.value,a,b⟩) x.payloads y.payloads) xs ys
  | _, _, _ => False

theorem nodeRel_iff (relation : Comparison → Prop) {k} (lower upper : Node k) :
    NodeRel relation lower upper ↔ HoldsExpansion relation (expandNodes lower upper) := by
  cases lower <;> cases upper <;>
    simp [NodeRel, expandNodes, pairLists_holds, recordPairs_holds, variantPairs_holds]
  split <;> simp_all [HoldsExpansion]

theorem forall₂_trans {α : Type} {r : α → α → Prop}
    (trans : ∀ a b c, r a b → r b c → r a c)
    {xs ys zs : List α} (hxy : ZipRel r xs ys) (hyz : ZipRel r ys zs) :
    ZipRel r xs zs := by
  induction xs generalizing ys zs with
  | nil => cases ys <;> cases zs <;> simp_all [ZipRel]
  | cons x xs ih =>
      cases ys <;> cases zs <;> simp_all only [ZipRel]
      exact ⟨trans _ _ _ hxy.1 hyz.1, ih hxy.2 hyz.2⟩

theorem NodeRel.trans {relation : Comparison → Prop}
    (trans : ∀ k a b c, relation ⟨k,a,b⟩ → relation ⟨k,b,c⟩ → relation ⟨k,a,c⟩)
    {k} {a b c : Node k} (ab : NodeRel relation a b) (bc : NodeRel relation b c) :
    NodeRel relation a c := by
  cases a <;> cases b <;> cases c <;> simp_all only [NodeRel]
  case function.function.function =>
    exact ⟨trans _ _ _ _ bc.1 ab.1, trans _ _ _ _ bc.2.1 ab.2.1,
      trans _ _ _ _ ab.2.2.1 bc.2.2.1, trans _ _ _ _ ab.2.2.2 bc.2.2.2⟩
  case record.record.record =>
    exact forall₂_trans (r := fun (x y : Field) => x.label = y.label ∧
      x.optional = y.optional ∧ relation ⟨.value,x.child,y.child⟩)
      (fun _ _ _ h₁ h₂ => ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1,
        trans _ _ _ _ h₁.2.2 h₂.2.2⟩) ab bc
  case tuple.tuple.tuple =>
    exact forall₂_trans (r := fun (x y : Nat) => relation ⟨.value,x,y⟩)
      (fun _ _ _ h₁ h₂ => trans _ _ _ _ h₁ h₂) ab bc
  case variant.variant.variant =>
    exact forall₂_trans (r := fun (x y : Alternative) => x.tag = y.tag ∧
      ZipRel (fun a b => relation ⟨.value,a,b⟩) x.payloads y.payloads)
      (fun _ _ _ h₁ h₂ => ⟨h₁.1.trans h₂.1,
        forall₂_trans (r := fun (a b : Nat) => relation ⟨.value,a,b⟩)
          (fun _ _ _ h₃ h₄ => trans _ _ _ _ h₃ h₄) h₁.2 h₂.2⟩) ab bc

theorem layer_nodeRel {graph : Graph} {relation : Comparison → Prop} {pair : Comparison} :
    Layer graph relation pair ↔ ∃ lower upper,
      graph.lookup pair.kind pair.lower = some lower ∧
      graph.lookup pair.kind pair.upper = some upper ∧ NodeRel relation lower upper := by
  cases hl : graph.lookup pair.kind pair.lower <;>
    cases hu : graph.lookup pair.kind pair.upper <;>
    simp [Layer, expand, hl, hu, nodeRel_iff, holdsExpansion_iff]

theorem Layer.trans {graph : Graph} {relation : Comparison → Prop}
    (trans : ∀ k a b c, relation ⟨k,a,b⟩ → relation ⟨k,b,c⟩ → relation ⟨k,a,c⟩)
    {k a b c} (ab : Layer graph relation ⟨k,a,b⟩) (bc : Layer graph relation ⟨k,b,c⟩) :
    Layer graph relation ⟨k,a,c⟩ := by
  rcases layer_nodeRel.mp ab with ⟨na,nb,ha,hb,hab⟩
  rcases layer_nodeRel.mp bc with ⟨nb',nc,hb',hc,hbc⟩
  have same : nb = nb' := Option.some.inj (hb.symm.trans hb')
  subst nb'
  exact layer_nodeRel.mpr ⟨na,nc,ha,hc,NodeRel.trans trans hab hbc⟩

/-- Transitivity is proved from the actual deterministic unfolding semantics.
No global validity premise is needed for already-related endpoints. -/
theorem regular_trans {graph : Graph} {k a b c}
    (ab : RegularSub graph ⟨k,a,b⟩) (bc : RegularSub graph ⟨k,b,c⟩) :
    RegularSub graph ⟨k,a,c⟩ := by
  intro depth
  have transDepth : ∀ k a b c, Approx graph depth ⟨k,a,b⟩ →
      Approx graph depth ⟨k,b,c⟩ → Approx graph depth ⟨k,a,c⟩ := by
    induction depth with
    | zero => intros; trivial
    | succ depth ih => exact fun _ _ _ _ h₁ h₂ => Layer.trans ih h₁ h₂
  exact transDepth k a b c (ab depth) (bc depth)

theorem forall₂_self {α : Type} {r : α → α → Prop} (xs : List α)
    (self : ∀ x, x ∈ xs → r x x) : ZipRel r xs xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨self x (by simp), ih (fun y hy => self y (by simp [hy]))⟩

theorem NodeRel.self {relation : Comparison → Prop} {k} (node : Node k)
    (children : ∀ ref, ref ∈ node.references → relation ⟨ref.kind,ref.identity,ref.identity⟩) :
    NodeRel relation node node := by
  cases node with
  | atom => rfl
  | bottom => trivial
  | top => trivial
  | function a ae re r =>
      exact ⟨children ⟨.value,a⟩ (by simp [Node.references]),
        children ⟨.effect,ae⟩ (by simp [Node.references]),
        children ⟨.effect,re⟩ (by simp [Node.references]),
        children ⟨.value,r⟩ (by simp [Node.references])⟩
  | record fields =>
      exact forall₂_self fields (fun f hf => ⟨rfl,rfl,
        children ⟨.value,f.child⟩ (by simp [Node.references]; exact ⟨f,hf,rfl⟩)⟩)
  | tuple elements =>
      exact forall₂_self elements (fun e he =>
        children ⟨.value,e⟩ (by simp [Node.references, he]))
  | variant alternatives =>
      apply forall₂_self alternatives
      intro a ha
      refine ⟨rfl, forall₂_self a.payloads (fun child hc => ?_)⟩
      apply children ⟨.value,child⟩
      simp only [Node.references, List.mem_flatMap]
      exact ⟨a,ha,by simp [hc]⟩

/-- A well-formed graph gives reflexivity for every existing endpoint.
Validity is supplied by the same final certificate acceptance. -/
theorem regular_refl {graph : Graph} (valid : graph.Valid) {k identity}
    (present : Reference.Exists graph ⟨k,identity⟩) : RegularSub graph ⟨k,identity,identity⟩ := by
  let relation := fun p : Comparison => p.lower = p.upper ∧
    Reference.Exists graph ⟨p.kind,p.lower⟩
  apply coinduction (relation := relation) ?_ _ ⟨rfl,present⟩
  rintro ⟨k,lower,upper⟩ ⟨same,found⟩
  change lower = upper at same
  subst upper
  rcases found with ⟨node,hn⟩
  apply layer_nodeRel.mpr
  refine ⟨node,node,hn,hn,NodeRel.self node ?_⟩
  intro ref hr
  exact ⟨rfl,(graph.valid_lookup valid hn).2 ref hr⟩


/-- Frozen Copy coordinates are reused without replacing parent/copy identity. -/
def copyLink (copy : Copy) : Comparison :=
  match copy.polarity with
  | .positive => ⟨copy.kind,copy.parent,copy.child⟩
  | .negative => ⟨copy.kind,copy.child,copy.parent⟩

def copyEqualities (copy : Copy) : List Comparison :=
  [⟨copy.kind,copy.parent,copy.child⟩,⟨copy.kind,copy.child,copy.parent⟩]

def Comparison.asConstraint (pair : Comparison) : Constraint :=
  ⟨pair.kind,.var pair.lower,.var pair.upper⟩

theorem copyLink_asConstraint (copy : Copy) :
    (copyLink copy).asConstraint = copy.link := by
  cases copy with
  | mk k parent child polarity => cases polarity <;> rfl

theorem copyEqualities_asConstraints (copy : Copy) :
    (copyEqualities copy).map Comparison.asConstraint = copy.equalities := rfl

/-- Exact interpretation of the variable-only constraints represented by graph
references. This does not identify RegularSub with finite-Term Sub. -/
def InterpretsVariable (graph : Graph) (constraint : Constraint) : Prop :=
  ∃ lower upper, constraint.lower = .var lower ∧ constraint.upper = .var upper ∧
    RegularSub graph ⟨constraint.kind,lower,upper⟩

theorem comparison_interpretation (graph : Graph) (pair : Comparison) :
    InterpretsVariable graph pair.asConstraint ↔ RegularSub graph pair := by
  cases pair
  simp [InterpretsVariable, Comparison.asConstraint]

def Holds (graph : Graph) (demands : List Comparison) : Prop :=
  ∀ pair, pair ∈ demands → RegularSub graph pair

@[simp] theorem holds_nil (graph : Graph) : Holds graph [] := by
  intro pair hp; cases hp

@[simp] theorem holds_cons (graph : Graph) (pair : Comparison) (rest : List Comparison) :
    Holds graph (pair :: rest) ↔ RegularSub graph pair ∧ Holds graph rest := by
  simp [Holds]

@[simp] theorem holds_append (graph : Graph) (left right : List Comparison) :
    Holds graph (left ++ right) ↔ Holds graph left ∧ Holds graph right := by
  simp [Holds, List.mem_append, or_imp, forall_and]

theorem holds_variable_store (graph : Graph) (demands : List Comparison) :
    Holds graph demands ↔
      ∀ constraint, constraint ∈ demands.map Comparison.asConstraint →
        InterpretsVariable graph constraint := by
  simp [Holds, comparison_interpretation]

/-- A finite structural extrusion derivation. Each structural rule checks the
actual old/new graph nodes with expand; its children retain exactly the
concatenated copy lists. Row-copy leaves are cuts, allowing the graph behind
them to be cyclic. This is not a native allocator or traversal simulation. -/
inductive Extrusion (graph : Graph) : Comparison → List Copy → Prop where
  | copy (coordinate : Copy) : Extrusion graph (copyLink coordinate) [coordinate]
  | same (k : Kind) (identity : Nat)
      (present : Reference.Exists graph ⟨k,identity⟩) :
      Extrusion graph ⟨k,identity,identity⟩ []
  | structural (pair : Comparison) (parts : List (Comparison × List Copy))
      (expanded : expand graph pair = some (parts.map Prod.fst))
      (children : ∀ part, part ∈ parts → Extrusion graph part.1 part.2) :
      Extrusion graph pair (parts.flatMap Prod.snd)

theorem Extrusion.sound {graph : Graph} (valid : graph.Valid)
    {pair : Comparison} {copies : List Copy} (trace : Extrusion graph pair copies)
    (links : Holds graph (copies.map copyLink)) : RegularSub graph pair := by
  induction trace with
  | copy coordinate => exact (holds_cons _ _ _).mp links |>.1
  | same k identity present => exact regular_refl valid present
  | structural pair parts expanded children ih =>
      apply regular_unfold.mpr
      refine ⟨parts.map Prod.fst,expanded,?_⟩
      intro child hc
      rcases List.mem_map.mp hc with ⟨part,hpart,rfl⟩
      apply ih part hpart
      intro link hlink
      rcases List.mem_map.mp hlink with ⟨copy,hcopy,rfl⟩
      apply links
      apply List.mem_map.mpr
      refine ⟨copy,?_,rfl⟩
      exact List.mem_flatMap.mpr ⟨part,hpart,hcopy⟩

structure ConstraintState where
  obligations : List Comparison
  occurrences : List Occurrence

def ConstraintState.Satisfied (graph : Graph) (state : ConstraintState) : Prop :=
  Holds graph state.obligations

/-- Graph-indexed concrete operations. Every semantic preservation conclusion
is proved below; constructors require syntax/lookup/retention facts only. -/
inductive ConstraintStep (graph : Graph) (ref : Nat → Nat → Prop) (birth : Nat → Nat) :
    ConstraintState → ConstraintState → Prop where
  | reflexive (k : Kind) (identity : Nat) (rest : List Comparison) (events : List Occurrence)
      (present : Reference.Exists graph ⟨k,identity⟩) :
      ConstraintStep graph ref birth ⟨⟨k,identity,identity⟩ :: rest,events⟩ ⟨rest,events⟩
  | decompose (pair : Comparison) (children rest : List Comparison) (events : List Occurrence)
      (expanded : expand graph pair = some children) :
      ConstraintStep graph ref birth ⟨pair :: rest,events⟩ ⟨children ++ rest,events⟩
  | insertLower (k : Kind) (lower row : Nat) (state : ConstraintState) :
      ConstraintStep graph ref birth state ⟨⟨k,lower,row⟩ :: state.obligations,state.occurrences⟩
  | insertUpper (k : Kind) (row upper : Nat) (state : ConstraintState) :
      ConstraintStep graph ref birth state ⟨⟨k,row,upper⟩ :: state.obligations,state.occurrences⟩
  | replay (k : Kind) (lower row upper : Nat) (rest : List Comparison) (events : List Occurrence)
      (lowerBound : Comparison.mk k lower row ∈ rest)
      (upperBound : Comparison.mk k row upper ∈ rest) :
      ConstraintStep graph ref birth ⟨⟨k,lower,upper⟩ :: rest,events⟩ ⟨rest,events⟩
  | extrudeUpper (k : Kind) (lower upper fresh : Nat) (copies : List Copy)
      (rest : List Comparison) (events : List Occurrence) (identity origin receiver : Nat)
      (traversal : Extrusion graph ⟨k,fresh,upper⟩ copies) :
      ConstraintStep graph ref birth ⟨⟨k,lower,upper⟩ :: rest,events⟩
        ⟨copies.map copyLink ++ ⟨k,lower,fresh⟩ :: rest,
          ⟨identity,origin,receiver,copies⟩ :: events⟩
  | extrudeLower (k : Kind) (lower fresh upper : Nat) (copies : List Copy)
      (rest : List Comparison) (events : List Occurrence) (identity origin receiver : Nat)
      (traversal : Extrusion graph ⟨k,lower,fresh⟩ copies) :
      ConstraintStep graph ref birth ⟨⟨k,lower,upper⟩ :: rest,events⟩
        ⟨copies.map copyLink ++ ⟨k,fresh,upper⟩ :: rest,
          ⟨identity,origin,receiver,copies⟩ :: events⟩
  | intrude (state : ConstraintState) (event : Occurrence) (selected : List Copy)
      (retained : event ∈ state.occurrences) (qualifies : event.Qualifies ref birth)
      (actual : ∀ copy, copy ∈ selected → copy ∈ event.copies) :
      ConstraintStep graph ref birth state
        ⟨selected.flatMap copyEqualities ++ state.obligations,state.occurrences⟩

theorem ConstraintStep.sound {graph : Graph} (valid : graph.Valid)
    {ref : Nat → Nat → Prop} {birth : Nat → Nat} {before after : ConstraintState}
    (step : ConstraintStep graph ref birth before after) (solved : after.Satisfied graph) :
    before.Satisfied graph := by
  cases step <;> simp only [ConstraintState.Satisfied, holds_cons, holds_append] at solved ⊢
  case reflexive present => exact ⟨regular_refl valid present,solved⟩
  case decompose expanded => exact ⟨regular_unfold.mpr ⟨_,expanded,solved.1⟩,solved.2⟩
  case insertLower => exact solved.2
  case insertUpper => exact solved.2
  case replay lowerBound upperBound =>
    exact ⟨regular_trans (solved _ lowerBound) (solved _ upperBound),solved⟩
  case extrudeUpper traversal =>
    exact ⟨regular_trans solved.2.1 (traversal.sound valid solved.1),solved.2.2⟩
  case extrudeLower traversal =>
    exact ⟨regular_trans (traversal.sound valid solved.1) solved.2.1,solved.2.2⟩
  case intrude => exact solved.2

theorem ConstraintStep.retains_occurrences {graph : Graph}
    {ref : Nat → Nat → Prop} {birth : Nat → Nat} {before after : ConstraintState}
    (step : ConstraintStep graph ref birth before after) :
    ∀ event, event ∈ before.occurrences → event ∈ after.occurrences := by
  cases step <;> intro event retained <;> first | exact retained | exact List.mem_cons_of_mem _ retained

theorem replay_solution_iff {graph : Graph} {k lower row upper} {rest : List Comparison}
    (lowerBound : Comparison.mk k lower row ∈ rest)
    (upperBound : Comparison.mk k row upper ∈ rest) :
    Holds graph (⟨k,lower,upper⟩ :: rest) ↔ Holds graph rest := by
  rw [holds_cons]
  exact ⟨And.right,fun h => ⟨regular_trans (h _ lowerBound) (h _ upperBound),h⟩⟩

inductive ConstraintHistory (graph : Graph) (ref : Nat → Nat → Prop) (birth : Nat → Nat) :
    ConstraintState → ConstraintState → Prop where
  | nil (state) : ConstraintHistory graph ref birth state state
  | cons {first middle last} (step : ConstraintStep graph ref birth first middle)
      (tail : ConstraintHistory graph ref birth middle last) : ConstraintHistory graph ref birth first last

theorem ConstraintHistory.sound {graph : Graph} (valid : graph.Valid)
    {ref : Nat → Nat → Prop} {birth : Nat → Nat} {first last : ConstraintState}
    (history : ConstraintHistory graph ref birth first last) (solved : last.Satisfied graph) :
    first.Satisfied graph := by
  induction history with
  | nil => exact solved
  | cons step tail ih => exact step.sound valid (ih solved)

theorem ConstraintHistory.retains_occurrences {graph : Graph}
    {ref : Nat → Nat → Prop} {birth : Nat → Nat} {first last : ConstraintState}
    (history : ConstraintHistory graph ref birth first last) :
    ∀ event, event ∈ first.occurrences → event ∈ last.occurrences := by
  induction history with
  | nil => exact fun _ h => h
  | cons step tail ih => exact fun event h => ih event (step.retains_occurrences event h)

/-- Main application: checked final finite evidence supplies a common regular
solution of ALL original pre-transform demands, with no solution premise. -/
theorem accepted_original_demands {graph : Graph}
    {ref : Nat → Nat → Prop} {birth : Nat → Nat} {first last : ConstraintState}
    {certificate : Certificate} (history : ConstraintHistory graph ref birth first last)
    (accepted : accepts graph certificate last.obligations = true) :
    graph.Valid ∧ first.Satisfied graph :=
  ⟨accepted_graph_valid accepted,
    history.sound (accepted_graph_valid accepted) (accepted_demands_sound accepted)⟩

/-- One shared postfixed relation covers original and final demands together.
It is constructed from the graph, never chosen per demand or per unfolding. -/
theorem accepted_original_joint {graph : Graph}
    {ref : Nat → Nat → Prop} {birth : Nat → Nat} {first last : ConstraintState}
    {certificate : Certificate} (history : ConstraintHistory graph ref birth first last)
    (accepted : accepts graph certificate last.obligations = true) :
    graph.Valid ∧ ∃ relation : Comparison → Prop,
      (∀ pair, relation pair → Layer graph relation pair) ∧
      (∀ pair, pair ∈ first.obligations → relation pair) ∧
      (∀ pair, pair ∈ last.obligations → relation pair) ∧
      (∀ pair, relation pair ↔ RegularSub graph pair) := by
  exact ⟨accepted_graph_valid accepted, RegularSub graph,
    fun _ h => regular_unfold.mp h, (accepted_original_demands history accepted).2,
    accepted_demands_sound accepted, fun _ => Iff.rfl⟩


/-- Renaming preserves every constructor and every metadata bit. It may
identify references; graph compatibility is a concrete lookup equation. -/
def renameNode (names : Renaming) : {k : Kind} → Node k → Node k
  | _, .atom a => .atom a
  | _, .bottom => .bottom
  | _, .top => .top
  | .value, .function a ae re r =>
      .function (names .value a) (names .effect ae) (names .effect re) (names .value r)
  | .value, .record fields =>
      .record (fields.map (fun f => ⟨f.label,f.optional,names .value f.child⟩))
  | .value, .tuple elements => .tuple (elements.map (names .value))
  | .value, .variant alternatives =>
      .variant (alternatives.map (fun a => ⟨a.tag,a.payloads.map (names .value)⟩))

def renamePair (names : Renaming) (pair : Comparison) : Comparison :=
  ⟨pair.kind,names pair.kind pair.lower,names pair.kind pair.upper⟩

def GraphRenaming (source target : Graph) (names : Renaming) : Prop :=
  ∀ k identity, target.lookup k (names k identity) =
    (source.lookup k identity).map (renameNode names)

theorem zipRel_map {α β : Type} (r : β → β → Prop) (f : α → β) (xs ys : List α) :
    ZipRel r (xs.map f) (ys.map f) ↔ ZipRel (fun x y => r (f x) (f y)) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [ZipRel]
  | cons x xs ih => cases ys <;> simp [ZipRel, ih]

theorem nodeRel_rename (names : Renaming) (relation : Comparison → Prop)
    {k} (lower upper : Node k) :
    NodeRel relation (renameNode names lower) (renameNode names upper) ↔
      NodeRel (fun pair => relation (renamePair names pair)) lower upper := by
  cases lower <;> cases upper <;> simp [NodeRel, renameNode, renamePair, zipRel_map]

/-- This is a proved semantic consequence of exact graph syntax preservation,
not an assumed subtype-preserving quotient law. Missing lookups are included. -/
theorem layer_rename {source target : Graph} {names : Renaming}
    (compatible : GraphRenaming source target names) (relation : Comparison → Prop)
    (pair : Comparison) :
    Layer target relation (renamePair names pair) ↔
      Layer source (fun p => relation (renamePair names p)) pair := by
  rw [layer_nodeRel, layer_nodeRel]
  simp only [renamePair]
  rw [compatible pair.kind pair.lower, compatible pair.kind pair.upper]
  cases hl : source.lookup pair.kind pair.lower <;>
    cases hu : source.lookup pair.kind pair.upper <;> simp [nodeRel_rename, renamePair]

theorem regular_rename {source target : Graph} {names : Renaming}
    (compatible : GraphRenaming source target names) (pair : Comparison) :
    RegularSub target (renamePair names pair) ↔ RegularSub source pair := by
  have depths : ∀ depth pair, Approx target depth (renamePair names pair) ↔
      Approx source depth pair := by
    intro depth
    induction depth with
    | zero => intro pair; rfl
    | succ depth ih =>
        intro pair
        change Layer target (Approx target depth) (renamePair names pair) ↔
          Layer source (Approx source depth) pair
        rw [layer_rename compatible]
        exact ⟨Layer.mono (fun p h => (ih p).mp h), Layer.mono (fun p h => (ih p).mpr h)⟩
  exact ⟨fun h depth => (depths depth pair).mp (h depth),
    fun h depth => (depths depth pair).mpr (h depth)⟩

/-- A checked target certificate can be pulled back across a concrete,
possibly non-injective graph renaming, then through the source history.
The source's independent finite validity check is explicit. -/
theorem accepted_renamed_original {source target : Graph} {names : Renaming}
    {ref : Nat → Nat → Prop} {birth : Nat → Nat} {first last : ConstraintState}
    {certificate : Certificate} (sourceChecked : checkGraph source = true)
    (compatible : GraphRenaming source target names)
    (history : ConstraintHistory source ref birth first last)
    (accepted : accepts target certificate (last.obligations.map (renamePair names)) = true) :
    source.Valid ∧ first.Satisfied source := by
  have valid := (checkGraph_iff source).mp sourceChecked
  refine ⟨valid,history.sound valid ?_⟩
  intro pair hp
  apply (regular_rename compatible pair).mp
  exact accepted_demands_sound accepted _ (List.mem_map.mpr ⟨pair,hp,rfl⟩)

/-- Every equality inserted for actual retained copies is reflected together
with the rest of the original store, even after subsequent transformations. -/
theorem accepted_retained_equalities {graph : Graph}
    {ref : Nat → Nat → Prop} {birth : Nat → Nat} {selected : List Copy}
    {rest : List Comparison} {events : List Occurrence} {last : ConstraintState}
    {certificate : Certificate}
    (history : ConstraintHistory graph ref birth
      ⟨selected.flatMap copyEqualities ++ rest,events⟩ last)
    (accepted : accepts graph certificate last.obligations = true) :
    Holds graph rest ∧ ∀ copy, copy ∈ selected →
      RegularSub graph ⟨copy.kind,copy.parent,copy.child⟩ ∧
      RegularSub graph ⟨copy.kind,copy.child,copy.parent⟩ := by
  have all := (accepted_original_demands history accepted).2
  have both := (holds_append graph _ _).mp all
  refine ⟨both.2,?_⟩
  intro copy hc
  constructor
  · apply both.1
    exact List.mem_flatMap.mpr ⟨copy,hc,by simp [copyEqualities]⟩
  · apply both.1
    exact List.mem_flatMap.mpr ⟨copy,hc,by simp [copyEqualities]⟩

/-! A concrete cyclic history using four-port structural extrusion and actual
retained equality insertion. The two recursive components are isomorphic;
all finite metadata and both effect ports are present in the certificate. -/
def equalityCyclicGraph : Graph
  | .value =>
      [.function 2 0 1 4, .function 3 1 0 5, .atom 9, .atom 9,
       .record [⟨10,false,6⟩,⟨11,true,4⟩],
       .record [⟨10,false,7⟩,⟨11,true,5⟩],
       .tuple [8], .tuple [9], .variant [⟨12,[0]⟩], .variant [⟨12,[1]⟩]]
  | .effect => [.atom 17,.atom 17]

def equalityCyclicCertificate : Certificate :=
  [⟨.value,0,1⟩,⟨.value,1,0⟩,⟨.value,2,3⟩,⟨.value,3,2⟩,
   ⟨.effect,0,1⟩,⟨.effect,1,0⟩,⟨.value,4,5⟩,⟨.value,5,4⟩,
   ⟨.value,6,7⟩,⟨.value,7,6⟩,⟨.value,8,9⟩,⟨.value,9,8⟩,
   ⟨.value,1,1⟩,⟨.value,3,3⟩,⟨.effect,1,1⟩,⟨.effect,0,0⟩,
   ⟨.value,5,5⟩,⟨.value,7,7⟩,⟨.value,9,9⟩]

def cyclicCopies : List Copy :=
  [⟨.value,2,3,.negative⟩,⟨.effect,0,1,.negative⟩,
   ⟨.effect,1,0,.positive⟩,⟨.value,4,5,.positive⟩]

def cyclicParts : List (Comparison × List Copy) :=
  cyclicCopies.map (fun copy => (copyLink copy,[copy]))

theorem cyclic_structural_extrusion :
    Extrusion equalityCyclicGraph ⟨.value,0,1⟩ cyclicCopies := by
  have trace := Extrusion.structural (graph := equalityCyclicGraph)
    ⟨.value,0,1⟩ cyclicParts (by rfl) (by
      intro part hp
      rcases List.mem_map.mp hp with ⟨copy,_,rfl⟩
      exact .copy copy)
  exact trace

def cyclicEvent : Occurrence := ⟨41,0,0,cyclicCopies⟩
def cyclicInitial : ConstraintState := ⟨[⟨.value,0,1⟩],[]⟩
def cyclicExtruded : ConstraintState :=
  ⟨cyclicCopies.map copyLink ++ [⟨.value,1,1⟩],[cyclicEvent]⟩
def cyclicIntruded : ConstraintState :=
  ⟨cyclicCopies.flatMap copyEqualities ++ cyclicExtruded.obligations,[cyclicEvent]⟩

theorem cyclic_history : ConstraintHistory equalityCyclicGraph
    (fun _ _ => False) (fun _ => 0) cyclicInitial cyclicIntruded := by
  apply ConstraintHistory.cons (middle := cyclicExtruded)
  · exact .extrudeLower .value 0 1 1 cyclicCopies [] [] 41 0 0 cyclic_structural_extrusion
  · apply ConstraintHistory.cons
    · apply ConstraintStep.intrude cyclicExtruded cyclicEvent cyclicCopies
      · exact List.mem_cons_self
      · exact ⟨0,.refl rfl,.refl rfl⟩
      · exact fun _ h => h
    · exact .nil _

theorem cyclic_final_accepted :
    accepts equalityCyclicGraph equalityCyclicCertificate cyclicIntruded.obligations = true := rfl

theorem cyclic_original_solved :
    equalityCyclicGraph.Valid ∧ cyclicInitial.Satisfied equalityCyclicGraph :=
  accepted_original_demands cyclic_history cyclic_final_accepted

/-- Removing either effect direction prevents this equality-bearing cyclic
history from obtaining an accepted final certificate. -/
theorem cyclic_missing_effect_rejected :
    accepts equalityCyclicGraph
      (equalityCyclicCertificate.filter (fun p => decide (p ≠ ⟨.effect,0,1⟩)))
      cyclicIntruded.obligations = false := rfl

/-- Actual top-level function decomposition also feeds the earlier cyclic
certificate: its original root need not be an accepted final demand. -/
def cyclicDecomposed : ConstraintState :=
  ⟨[⟨.value,3,2⟩,⟨.effect,1,0⟩,⟨.effect,1,0⟩,⟨.value,4,5⟩],[]⟩

theorem mixed_decomposition_history : ConstraintHistory mixedCyclicGraph
    (fun _ _ => False) (fun _ => 0) cyclicInitial cyclicDecomposed :=
  .cons (.decompose ⟨.value,0,1⟩ cyclicDecomposed.obligations [] [] rfl) (.nil _)

theorem mixed_decomposition_accepted :
    accepts mixedCyclicGraph mixedCyclicCertificate cyclicDecomposed.obligations = true := rfl

theorem mixed_original_reconstructed :
    mixedCyclicGraph.Valid ∧ cyclicInitial.Satisfied mixedCyclicGraph :=
  accepted_original_demands mixed_decomposition_history mixed_decomposition_accepted


/-- This checked structural quotient really identifies two source references. -/
def duplicateGraph : Graph
  | .value => [.atom 7,.atom 7]
  | .effect => []
def quotientGraph : Graph
  | .value => [.atom 7]
  | .effect => []
def quotientNames : Renaming
  | .value, 0 => 0
  | .value, 1 => 0
  | .value, n + 2 => n + 1
  | .effect, n => n

theorem quotient_compatible : GraphRenaming duplicateGraph quotientGraph quotientNames := by
  intro k identity
  cases k with
  | effect => rfl
  | value =>
      cases identity with
      | zero => rfl
      | succ n => cases n <;> rfl

theorem quotient_identifies_distinct :
    (0 : Nat) ≠ 1 ∧ quotientNames .value 0 = quotientNames .value 1 := by decide

theorem quotient_original_solved :
    duplicateGraph.Valid ∧
      (ConstraintState.mk [⟨.value,0,1⟩] []).Satisfied duplicateGraph := by
  apply accepted_renamed_original (target := quotientGraph) (names := quotientNames)
    (certificate := [⟨.value,0,0⟩]) (ref := fun _ _ => False) (birth := fun _ => 0)
  · rfl
  · exact quotient_compatible
  · exact .nil _
  · rfl

/-- Acyclic reconstruction with the original function pair absent from the
entire terminal certificate; it contains only the four-port child obligations. -/
def acyclicGraph : Graph
  | .value => [.function 2 0 0 2,.function 2 0 0 2,.atom 5]
  | .effect => [.atom 6]
def acyclicCertificate : Certificate := [⟨.value,2,2⟩,⟨.effect,0,0⟩]
def acyclicTerminal : ConstraintState :=
  ⟨[⟨.value,2,2⟩,⟨.effect,0,0⟩,⟨.effect,0,0⟩,⟨.value,2,2⟩],[]⟩

theorem acyclic_original_absent : Comparison.mk .value 0 1 ∉ acyclicCertificate := by decide

theorem acyclic_original_reconstructed :
    acyclicGraph.Valid ∧ cyclicInitial.Satisfied acyclicGraph := by
  apply accepted_original_demands (last := acyclicTerminal) (certificate := acyclicCertificate)
    (ref := fun _ _ => False) (birth := fun _ => 0)
  · exact .cons (.decompose ⟨.value,0,1⟩ acyclicTerminal.obligations [] [] rfl) (.nil _)
  · rfl

end YulangClosure.SimpleSub.Regular
