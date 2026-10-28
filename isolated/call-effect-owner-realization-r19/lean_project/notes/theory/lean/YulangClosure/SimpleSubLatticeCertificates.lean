import YulangClosure.SimpleSubRegularConstraintSoundness

/-!
Finite lattice derivations inside guarded regular structural graphs.

This extends the independent all-depth interpretation of RegularSolutions.
The structural nodes, metadata, and four Function ports are reused verbatim.
Only a structural rule can appeal to the shared recursive comparison table;
join, meet, and transitivity premises are finite derivations at the same depth.
Graph validation separately rules out cycles consisting solely of lattice edges.

The lattice rules are the rules of SimpleSubConstraintSyntax.Sub. This is a
proof-side certificate language, not a production inference algorithm or a
new source typing judgment. Native extraction, ordinary coalescing, complete
Call/effects, and the graph decoder/history/publication bridges remain open.
-/
namespace YulangClosure.SimpleSub.Lattice
open Regular

inductive Node : Kind → Type where
  | structural {k} (node : Regular.Node k) : Node k
  | union {k} (left right : Nat) : Node k
  | intersection {k} (left right : Nat) : Node k
  deriving Repr

abbrev Graph := (k : Kind) → List (Node k)

def Graph.lookup (graph : Graph) (k : Kind) (i : Nat) : Option (Node k) :=
  lookupList (graph k) i

def Exists (graph : Graph) (k : Kind) (i : Nat) : Prop :=
  ∃ node, graph.lookup k i = some node

def existsAt (graph : Graph) (k : Kind) (i : Nat) : Bool :=
  (graph.lookup k i).isSome

theorem existsAt_iff (graph : Graph) (k : Kind) (i : Nat) :
    existsAt graph k i = true ↔ Exists graph k i := by
  cases h : graph.lookup k i <;> simp [existsAt, Exists, h]

def Node.references {k} : Node k → List Reference
  | .structural node => node.references
  | .union a b | .intersection a b => [⟨k,a⟩,⟨k,b⟩]

def Node.uniqueLabels {k} : Node k → Prop
  | .structural node => node.uniqueLabels
  | _ => True

instance {k} (node : Node k) : Decidable node.uniqueLabels := by
  cases node <;> simp only [Node.uniqueLabels] <;> infer_instance

def Graph.Valid (graph : Graph) : Prop :=
  ∀ k node, node ∈ graph k → node.uniqueLabels ∧
    ∀ ref, ref ∈ node.references → Exists graph ref.kind ref.identity

def checkGraph (graph : Graph) : Bool :=
  let check := fun {k} (node : Node k) => decide node.uniqueLabels &&
    node.references.all (fun ref => existsAt graph ref.kind ref.identity)
  (graph .value).all check && (graph .effect).all check

theorem checkGraph_iff (graph : Graph) : checkGraph graph = true ↔ graph.Valid := by
  simp only [checkGraph, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    existsAt_iff]
  constructor
  · rintro ⟨hv,he⟩ k
    cases k
    · exact hv
    · exact he
  · intro h
    exact ⟨h .value,h .effect⟩

/-- Finite lattice paths stop at actual structural constructors. -/
inductive FiniteLattice (graph : Graph) : (k : Kind) → Nat → Prop where
  | structural {k i node} (found : graph.lookup k i = some (.structural node)) :
      FiniteLattice graph k i
  | union {k i a b} (found : graph.lookup k i = some (.union a b))
      (left : FiniteLattice graph k a) (right : FiniteLattice graph k b) :
      FiniteLattice graph k i
  | intersection {k i a b} (found : graph.lookup k i = some (.intersection a b))
      (left : FiniteLattice graph k a) (right : FiniteLattice graph k b) :
      FiniteLattice graph k i

def checkFinite (graph : Graph) : Nat → (k : Kind) → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, k, i =>
      match graph.lookup k i with
      | some (.structural _) => true
      | some (.union a b) | some (.intersection a b) =>
          checkFinite graph fuel k a && checkFinite graph fuel k b
      | none => false

theorem checkFinite_sound {graph : Graph} {fuel k i}
    (checked : checkFinite graph fuel k i = true) : FiniteLattice graph k i := by
  induction fuel generalizing k i with
  | zero => cases checked
  | succ fuel ih =>
      cases found : graph.lookup k i with
      | none => simp [checkFinite,found] at checked
      | some node =>
          cases node with
          | structural node => exact .structural found
          | union a b =>
              have h := Bool.and_eq_true_iff.mp (show
                (checkFinite graph fuel k a && checkFinite graph fuel k b) = true from
                by simpa only [checkFinite,found] using checked)
              exact .union found (ih h.1) (ih h.2)
          | intersection a b =>
              have h := Bool.and_eq_true_iff.mp (show
                (checkFinite graph fuel k a && checkFinite graph fuel k b) = true from
                by simpa only [checkFinite,found] using checked)
              exact .intersection found (ih h.1) (ih h.2)

def Graph.Guarded (graph : Graph) : Prop :=
  ∀ k i, i < (graph k).length → FiniteLattice graph k i

def checkGuarded (graph : Graph) : Bool :=
  let fuel := (graph .value).length + (graph .effect).length + 1
  (List.range (graph .value).length).all (checkFinite graph fuel .value) &&
    (List.range (graph .effect).length).all (checkFinite graph fuel .effect)

theorem checkGuarded_sound {graph : Graph} (checked : checkGuarded graph = true) :
    graph.Guarded := by
  have h := Bool.and_eq_true_iff.mp checked
  intro k i hi
  cases k with
  | value => exact checkFinite_sound ((List.all_eq_true.mp h.1) i (List.mem_range.mpr hi))
  | effect => exact checkFinite_sound ((List.all_eq_true.mp h.2) i (List.mem_range.mpr hi))

def unionAt (graph : Graph) (k : Kind) (i : Nat) : Option (Nat × Nat) :=
  match graph.lookup k i with
  | some (.union a b) => some (a,b)
  | _ => none

def intersectionAt (graph : Graph) (k : Kind) (i : Nat) : Option (Nat × Nat) :=
  match graph.lookup k i with
  | some (.intersection a b) => some (a,b)
  | _ => none

def bottomAt (graph : Graph) (k : Kind) (i : Nat) : Bool :=
  match graph.lookup k i with
  | some (.structural .bottom) => true
  | _ => false

def topAt (graph : Graph) (k : Kind) (i : Nat) : Bool :=
  match graph.lookup k i with
  | some (.structural .top) => true
  | _ => false

def structuralExpand (graph : Graph) (pair : Comparison) : Option (List Comparison) :=
  match graph.lookup pair.kind pair.lower, graph.lookup pair.kind pair.upper with
  | some (.structural lower), some (.structural upper) => expandNodes lower upper
  | _, _ => none

/-- Independent finitary derivation for one structural depth. There is no
constructor that admits an arbitrary recursive table comparison directly. -/
inductive Layer (graph : Graph) (relation : Comparison → Prop) : Comparison → Prop where
  | structural {pair children} (expanded : structuralExpand graph pair = some children)
      (closed : ∀ child, child ∈ children → relation child) : Layer graph relation pair
  | refl {k i} (present : Exists graph k i) : Layer graph relation ⟨k,i,i⟩
  | trans {k a b c} : Layer graph relation ⟨k,a,b⟩ →
      Layer graph relation ⟨k,b,c⟩ → Layer graph relation ⟨k,a,c⟩
  | bottom {k a b} (found : bottomAt graph k a = true) (present : Exists graph k b) :
      Layer graph relation ⟨k,a,b⟩
  | top {k a b} (found : topAt graph k b = true) (present : Exists graph k a) :
      Layer graph relation ⟨k,a,b⟩
  | unionLeft {k u a b} (found : unionAt graph k u = some (a,b)) :
      Layer graph relation ⟨k,a,u⟩
  | unionRight {k u a b} (found : unionAt graph k u = some (a,b)) :
      Layer graph relation ⟨k,b,u⟩
  | unionElim {k u a b c} (found : unionAt graph k u = some (a,b)) :
      Layer graph relation ⟨k,a,c⟩ → Layer graph relation ⟨k,b,c⟩ →
      Layer graph relation ⟨k,u,c⟩
  | intersectionLeft {k u a b} (found : intersectionAt graph k u = some (a,b)) :
      Layer graph relation ⟨k,u,a⟩
  | intersectionRight {k u a b} (found : intersectionAt graph k u = some (a,b)) :
      Layer graph relation ⟨k,u,b⟩
  | intersectionIntro {k u a b c} (found : intersectionAt graph k u = some (a,b)) :
      Layer graph relation ⟨k,c,a⟩ → Layer graph relation ⟨k,c,b⟩ →
      Layer graph relation ⟨k,c,u⟩
  | unionMono {k u v a b c d}
      (left : unionAt graph k u = some (a,b)) (right : unionAt graph k v = some (c,d)) :
      Layer graph relation ⟨k,a,c⟩ → Layer graph relation ⟨k,b,d⟩ →
      Layer graph relation ⟨k,u,v⟩
  | intersectionMono {k u v a b c d}
      (left : intersectionAt graph k u = some (a,b))
      (right : intersectionAt graph k v = some (c,d)) :
      Layer graph relation ⟨k,a,c⟩ → Layer graph relation ⟨k,b,d⟩ →
      Layer graph relation ⟨k,u,v⟩

theorem Layer.mono {graph : Graph} {left right : Comparison → Prop}
    (included : ∀ p, left p → right p) {pair} (h : Layer graph left pair) :
    Layer graph right pair := by
  induction h with
  | structural expanded closed => exact .structural expanded (fun c hc => included c (closed c hc))
  | refl present => exact .refl present
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | bottom found present => exact .bottom found present
  | top found present => exact .top found present
  | unionLeft found => exact .unionLeft found
  | unionRight found => exact .unionRight found
  | unionElim found _ _ ih₁ ih₂ => exact .unionElim found ih₁ ih₂
  | intersectionLeft found => exact .intersectionLeft found
  | intersectionRight found => exact .intersectionRight found
  | intersectionIntro found _ _ ih₁ ih₂ => exact .intersectionIntro found ih₁ ih₂
  | unionMono left right _ _ ih₁ ih₂ => exact .unionMono left right ih₁ ih₂
  | intersectionMono left right _ _ ih₁ ih₂ => exact .intersectionMono left right ih₁ ih₂

def Approx (graph : Graph) : Nat → Comparison → Prop
  | 0, _ => True
  | depth + 1, pair => Layer graph (Approx graph depth) pair

def RegularSub (graph : Graph) (pair : Comparison) : Prop :=
  ∀ depth, Approx graph depth pair

theorem coinduction {graph : Graph} {relation : Comparison → Prop}
    (postfixed : ∀ pair, relation pair → Layer graph relation pair) :
    ∀ pair, relation pair → RegularSub graph pair := by
  intro pair hp depth
  induction depth generalizing pair with
  | zero => trivial
  | succ depth ih => exact Layer.mono (fun child hc => ih child hc) (postfixed pair hp)

/-- This direction needs no selection of a common derivation from infinitely
many depth-specific witnesses. The reverse unfolding implication is not claimed. -/
theorem regular_fold {graph : Graph} {pair}
    (h : Layer graph (RegularSub graph) pair) : RegularSub graph pair := by
  intro depth
  cases depth with
  | zero => trivial
  | succ depth => exact Layer.mono (fun child hc => hc depth) h

theorem regular_refl {graph : Graph} {k i} (present : Exists graph k i) :
    RegularSub graph ⟨k,i,i⟩ := regular_fold (.refl present)

theorem regular_trans {graph : Graph} {k a b c}
    (left : RegularSub graph ⟨k,a,b⟩) (right : RegularSub graph ⟨k,b,c⟩) :
    RegularSub graph ⟨k,a,c⟩ := by
  intro depth
  cases depth with
  | zero => trivial
  | succ depth => exact .trans (left (depth + 1)) (right (depth + 1))

theorem regular_structural {graph : Graph} {pair children}
    (expanded : structuralExpand graph pair = some children)
    (closed : ∀ child, child ∈ children → RegularSub graph child) :
    RegularSub graph pair := regular_fold (.structural expanded closed)

/-- Finite rule witnesses. Recursive table use occurs only in `structural`. -/
inductive Derivation where
  | structural | refl | bottom | top | unionLeft | unionRight
  | intersectionLeft | intersectionRight
  | trans (middle : Nat) (first second : Derivation)
  | unionElim (left right : Derivation)
  | intersectionIntro (left right : Derivation)
  | unionMono (left right : Derivation)
  | intersectionMono (left right : Derivation)
  deriving Repr

def checkDerivation (graph : Graph) (table : List Comparison) : Derivation → Comparison → Bool
  | .structural, pair =>
      match structuralExpand graph pair with
      | some children => children.all (fun child => decide (child ∈ table))
      | none => false
  | .refl, ⟨k,a,b⟩ => decide (a = b) && existsAt graph k a
  | .bottom, ⟨k,a,b⟩ => bottomAt graph k a && existsAt graph k b
  | .top, ⟨k,a,b⟩ => topAt graph k b && existsAt graph k a
  | .trans b first second, ⟨k,a,c⟩ =>
      checkDerivation graph table first ⟨k,a,b⟩ && checkDerivation graph table second ⟨k,b,c⟩
  | .unionLeft, ⟨k,a,u⟩ =>
      match unionAt graph k u with
      | some (l,_) => decide (a = l)
      | none => false
  | .unionRight, ⟨k,b,u⟩ =>
      match unionAt graph k u with
      | some (_,r) => decide (b = r)
      | none => false
  | .unionElim left right, ⟨k,u,c⟩ =>
      match unionAt graph k u with
      | some (a,b) => checkDerivation graph table left ⟨k,a,c⟩ &&
          checkDerivation graph table right ⟨k,b,c⟩
      | none => false
  | .intersectionLeft, ⟨k,u,a⟩ =>
      match intersectionAt graph k u with
      | some (l,_) => decide (a = l)
      | none => false
  | .intersectionRight, ⟨k,u,b⟩ =>
      match intersectionAt graph k u with
      | some (_,r) => decide (b = r)
      | none => false
  | .intersectionIntro left right, ⟨k,c,u⟩ =>
      match intersectionAt graph k u with
      | some (a,b) => checkDerivation graph table left ⟨k,c,a⟩ &&
          checkDerivation graph table right ⟨k,c,b⟩
      | none => false
  | .unionMono left right, ⟨k,u,v⟩ =>
      match unionAt graph k u, unionAt graph k v with
      | some (a,b), some (c,d) => checkDerivation graph table left ⟨k,a,c⟩ &&
          checkDerivation graph table right ⟨k,b,d⟩
      | _, _ => false
  | .intersectionMono left right, ⟨k,u,v⟩ =>
      match intersectionAt graph k u, intersectionAt graph k v with
      | some (a,b), some (c,d) => checkDerivation graph table left ⟨k,a,c⟩ &&
          checkDerivation graph table right ⟨k,b,d⟩
      | _, _ => false

theorem checkDerivation_sound {graph : Graph} {table : List Comparison} (proof : Derivation)
    {k a b} (checked : checkDerivation graph table proof ⟨k,a,b⟩ = true) :
    Layer graph (fun child => child ∈ table) ⟨k,a,b⟩ := by
  induction proof generalizing k a b with
  | structural =>
      cases found : structuralExpand graph ⟨k,a,b⟩ with
      | none => simp [checkDerivation,found] at checked
      | some children =>
          exact .structural found (by simpa [checkDerivation,found,List.all_eq_true] using checked)
  | refl =>
      have h : a = b ∧ Exists graph k a := by simpa [checkDerivation,existsAt_iff] using checked
      rcases h with ⟨rfl,present⟩
      exact .refl present
  | bottom =>
      have h := Bool.and_eq_true_iff.mp checked
      exact .bottom h.1 ((existsAt_iff _ _ _).mp h.2)
  | top =>
      have h := Bool.and_eq_true_iff.mp checked
      exact .top h.1 ((existsAt_iff _ _ _).mp h.2)
  | trans middle first second ih₁ ih₂ =>
      have h := Bool.and_eq_true_iff.mp checked
      exact .trans (ih₁ h.1) (ih₂ h.2)
  | unionLeft =>
      cases found : unionAt graph k b with
      | none => simp [checkDerivation,found] at checked
      | some pair =>
          rcases pair with ⟨l,r⟩
          have h : a = l := by simpa [checkDerivation,found] using checked
          subst a
          exact .unionLeft found
  | unionRight =>
      cases found : unionAt graph k b with
      | none => simp [checkDerivation,found] at checked
      | some pair =>
          rcases pair with ⟨l,r⟩
          have h : a = r := by simpa [checkDerivation,found] using checked
          subst a
          exact .unionRight found
  | intersectionLeft =>
      cases found : intersectionAt graph k a with
      | none => simp [checkDerivation,found] at checked
      | some pair =>
          rcases pair with ⟨l,r⟩
          have h : b = l := by simpa [checkDerivation,found] using checked
          subst b
          exact .intersectionLeft found
  | intersectionRight =>
      cases found : intersectionAt graph k a with
      | none => simp [checkDerivation,found] at checked
      | some pair =>
          rcases pair with ⟨l,r⟩
          have h : b = r := by simpa [checkDerivation,found] using checked
          subst b
          exact .intersectionRight found
  | unionElim left right ih₁ ih₂ =>
      cases found : unionAt graph k a with
      | none => simp [checkDerivation,found] at checked
      | some pair =>
          rcases pair with ⟨l,r⟩
          have h : checkDerivation graph table left ⟨k,l,b⟩ = true ∧
              checkDerivation graph table right ⟨k,r,b⟩ = true := by
            simpa [checkDerivation,found] using checked
          exact .unionElim found (ih₁ h.1) (ih₂ h.2)
  | intersectionIntro left right ih₁ ih₂ =>
      cases found : intersectionAt graph k b with
      | none => simp [checkDerivation,found] at checked
      | some pair =>
          rcases pair with ⟨l,r⟩
          have h : checkDerivation graph table left ⟨k,a,l⟩ = true ∧
              checkDerivation graph table right ⟨k,a,r⟩ = true := by
            simpa [checkDerivation,found] using checked
          exact .intersectionIntro found (ih₁ h.1) (ih₂ h.2)
  | unionMono left right ih₁ ih₂ =>
      cases hl : unionAt graph k a with
      | none => simp [checkDerivation,hl] at checked
      | some p =>
          cases hr : unionAt graph k b with
          | none => simp [checkDerivation,hl,hr] at checked
          | some q =>
              rcases p with ⟨l,r⟩
              rcases q with ⟨s,t⟩
              have h : checkDerivation graph table left ⟨k,l,s⟩ = true ∧
                  checkDerivation graph table right ⟨k,r,t⟩ = true := by
                simpa [checkDerivation,hl,hr] using checked
              exact .unionMono hl hr (ih₁ h.1) (ih₂ h.2)
  | intersectionMono left right ih₁ ih₂ =>
      cases hl : intersectionAt graph k a with
      | none => simp [checkDerivation,hl] at checked
      | some p =>
          cases hr : intersectionAt graph k b with
          | none => simp [checkDerivation,hl,hr] at checked
          | some q =>
              rcases p with ⟨l,r⟩
              rcases q with ⟨s,t⟩
              have h : checkDerivation graph table left ⟨k,l,s⟩ = true ∧
                  checkDerivation graph table right ⟨k,r,t⟩ = true := by
                simpa [checkDerivation,hl,hr] using checked
              exact .intersectionMono hl hr (ih₁ h.1) (ih₂ h.2)

/-- Every finite derivation of the independent layer has finite executable
evidence. This constructs a witness from a derivation; it is not proof search. -/
theorem checkDerivation_complete {graph : Graph} {table : List Comparison} {pair}
    (h : Layer graph (fun child => child ∈ table) pair) :
    ∃ proof, checkDerivation graph table proof pair = true := by
  induction h with
  | structural expanded closed =>
      exact ⟨.structural,by simpa [checkDerivation,expanded,List.all_eq_true] using closed⟩
  | refl present => exact ⟨.refl,by simp [checkDerivation,existsAt_iff,present]⟩
  | @trans k a b c first second ih₁ ih₂ =>
      rcases ih₁ with ⟨p,hp⟩
      rcases ih₂ with ⟨q,hq⟩
      exact ⟨.trans b p q,by simp [checkDerivation,hp,hq]⟩
  | bottom found present => exact ⟨.bottom,by simp [checkDerivation,found,existsAt_iff,present]⟩
  | top found present => exact ⟨.top,by simp [checkDerivation,found,existsAt_iff,present]⟩
  | unionLeft found => exact ⟨.unionLeft,by simp [checkDerivation,found]⟩
  | unionRight found => exact ⟨.unionRight,by simp [checkDerivation,found]⟩
  | intersectionLeft found => exact ⟨.intersectionLeft,by simp [checkDerivation,found]⟩
  | intersectionRight found => exact ⟨.intersectionRight,by simp [checkDerivation,found]⟩
  | unionElim found _ _ ih₁ ih₂ =>
      rcases ih₁ with ⟨p,hp⟩
      rcases ih₂ with ⟨q,hq⟩
      exact ⟨.unionElim p q,by simp [checkDerivation,found,hp,hq]⟩
  | intersectionIntro found _ _ ih₁ ih₂ =>
      rcases ih₁ with ⟨p,hp⟩
      rcases ih₂ with ⟨q,hq⟩
      exact ⟨.intersectionIntro p q,by simp [checkDerivation,found,hp,hq]⟩
  | unionMono left right _ _ ih₁ ih₂ =>
      rcases ih₁ with ⟨p,hp⟩
      rcases ih₂ with ⟨q,hq⟩
      exact ⟨.unionMono p q,by simp [checkDerivation,left,right,hp,hq]⟩
  | intersectionMono left right _ _ ih₁ ih₂ =>
      rcases ih₁ with ⟨p,hp⟩
      rcases ih₂ with ⟨q,hq⟩
      exact ⟨.intersectionMono p q,by simp [checkDerivation,left,right,hp,hq]⟩

theorem checkDerivation_iff (graph : Graph) (table : List Comparison) (pair : Comparison) :
    (∃ proof, checkDerivation graph table proof pair = true) ↔
      Layer graph (fun child => child ∈ table) pair := by
  constructor
  · rintro ⟨proof,checked⟩
    rcases pair with ⟨k,a,b⟩
    exact checkDerivation_sound proof checked
  · exact checkDerivation_complete

abbrev Certificate := List (Comparison × Derivation)

def table (certificate : Certificate) : List Comparison := certificate.map Prod.fst

def checkCertificate (graph : Graph) (certificate : Certificate) : Bool :=
  certificate.all (fun entry => checkDerivation graph (table certificate) entry.2 entry.1)

theorem checkCertificate_postfixed {graph : Graph} {certificate : Certificate}
    (checked : checkCertificate graph certificate = true) :
    ∀ pair, pair ∈ table certificate → Layer graph (fun c => c ∈ table certificate) pair := by
  intro pair hp
  rcases List.mem_map.mp hp with ⟨⟨p,proof⟩,member,same⟩
  dsimp at same
  subst pair
  rcases p with ⟨k,a,b⟩
  exact checkDerivation_sound proof ((List.all_eq_true.mp checked) _ member)

theorem certificate_sound {graph : Graph} {certificate : Certificate}
    (checked : checkCertificate graph certificate = true) :
    ∀ pair, pair ∈ table certificate → RegularSub graph pair :=
  coinduction (checkCertificate_postfixed checked)

def accepts (graph : Graph) (certificate : Certificate) (demands : List Comparison) : Bool :=
  checkGraph graph && checkGuarded graph && checkCertificate graph certificate &&
    demands.all (fun pair => decide (pair ∈ table certificate))

theorem accepts_sound {graph : Graph} {certificate : Certificate} {demands : List Comparison}
    (accepted : accepts graph certificate demands = true) :
    graph.Valid ∧ graph.Guarded ∧ ∀ pair, pair ∈ demands → RegularSub graph pair := by
  have h : checkGraph graph = true ∧ checkGuarded graph = true ∧
      checkCertificate graph certificate = true ∧
      ∀ pair, pair ∈ demands → pair ∈ table certificate := by
    simpa [accepts,List.all_eq_true,and_assoc] using accepted
  exact ⟨(checkGraph_iff graph).mp h.1,checkGuarded_sound h.2.1,
    fun pair hp => certificate_sound h.2.2.1 pair (h.2.2.2 pair hp)⟩

theorem accepted_joint_relation {graph : Graph} {certificate : Certificate}
    {demands : List Comparison} (accepted : accepts graph certificate demands = true) :
    graph.Valid ∧ graph.Guarded ∧ ∃ relation : Comparison → Prop,
      (∀ pair, relation pair → Layer graph relation pair) ∧
      (∀ pair, pair ∈ demands → relation pair) ∧
      (∀ pair, relation pair → RegularSub graph pair) := by
  have h : checkGraph graph = true ∧ checkGuarded graph = true ∧
      checkCertificate graph certificate = true ∧
      ∀ pair, pair ∈ demands → pair ∈ table certificate := by
    simpa [accepts,List.all_eq_true,and_assoc] using accepted
  exact ⟨(accepts_sound accepted).1,(accepts_sound accepted).2.1,
    (fun pair => pair ∈ table certificate),checkCertificate_postfixed h.2.2.1,
    h.2.2.2,certificate_sound h.2.2.1⟩

/-- Preserve all old identities while including the old structural graph. -/
def ofRegular (graph : Regular.Graph) : Graph :=
  fun k => (graph k).map Node.structural

theorem lookupList_map {α β : Type} (f : α → β) (xs : List α) (i : Nat) :
    lookupList (xs.map f) i = (lookupList xs i).map f := by
  induction xs generalizing i with
  | nil => rfl
  | cons head tail ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem ofRegular_lookup (graph : Regular.Graph) (k : Kind) (i : Nat) :
    (ofRegular graph).lookup k i = (graph.lookup k i).map Node.structural :=
  lookupList_map _ _ _

theorem ofRegular_expansion (graph : Regular.Graph) (pair : Comparison) :
    structuralExpand (ofRegular graph) pair = Regular.expand graph pair := by
  cases hl : graph.lookup pair.kind pair.lower <;>
    cases hr : graph.lookup pair.kind pair.upper <;>
    simp [structuralExpand,ofRegular_lookup,Regular.expand,hl,hr]

theorem ofRegular_layer {graph : Regular.Graph} {relation pair}
    (h : Regular.Layer graph relation pair) : Layer (ofRegular graph) relation pair := by
  rcases h with ⟨children,expanded,closed⟩
  exact .structural (by simpa only [ofRegular_expansion] using expanded) closed

/-- Every old regular comparison is preserved; no old node is reinterpreted. -/
theorem ofRegular_sub {graph : Regular.Graph} {pair}
    (h : Regular.RegularSub graph pair) : RegularSub (ofRegular graph) pair := by
  intro depth
  induction depth generalizing pair with
  | zero => trivial
  | succ depth ih =>
      exact Layer.mono (fun child hc => ih (pair := child) hc)
        (ofRegular_layer (Regular.regular_unfold.mp h))

theorem ofRegular_valid {graph : Regular.Graph} (valid : graph.Valid) :
    (ofRegular graph).Valid := by
  intro k node member
  change node ∈ (graph k).map Node.structural at member
  rcases List.mem_map.mp member with ⟨old,oldMember,same⟩
  subst node
  have h := valid k old oldMember
  refine ⟨h.1,?_⟩
  intro ref hr
  rcases h.2 ref hr with ⟨child,found⟩
  exact ⟨.structural child,by simp [ofRegular_lookup,found]⟩

theorem lookupList_present {α : Type} (xs : List α) (i : Nat) (bound : i < xs.length) :
    ∃ x, lookupList xs i = some x := by
  induction xs generalizing i with
  | nil => simp at bound
  | cons head tail ih =>
      cases i with
      | zero => exact ⟨head,rfl⟩
      | succ i => exact ih i (Nat.lt_of_succ_lt_succ bound)

theorem ofRegular_guarded (graph : Regular.Graph) : (ofRegular graph).Guarded := by
  intro k i bound
  have oldBound : i < (graph k).length := by simpa [ofRegular] using bound
  rcases lookupList_present (graph k) i oldBound with ⟨node,found⟩
  have h : graph.lookup k i = some node := found
  exact .structural (node := node) (by simp [ofRegular_lookup,h])

/-! The recursive result crosses a union and an intersection before returning
through the Function root. The argument and both effects retain their separate
contravariant/contravariant/covariant/covariant demands. -/
def recursiveLatticeGraph : Graph
  | .value =>
      [.structural (.function 2 0 1 4), .structural (.function 3 1 0 5),
       .structural .top, .structural .bottom, .union 0 6, .intersection 7 8,
       .structural (.atom 10), .union 1 6, .structural .top]
  | .effect => [.structural .top, .structural .bottom]

def recursiveLatticeCertificate : Certificate :=
  [(⟨.value,0,1⟩,.structural), (⟨.value,3,2⟩,.bottom),
   (⟨.effect,1,0⟩,.bottom),
   (⟨.value,4,5⟩,.intersectionIntro (.unionMono .structural .refl) .top)]

theorem recursiveLattice_accepted :
    accepts recursiveLatticeGraph recursiveLatticeCertificate [⟨.value,0,1⟩] = true := rfl

theorem recursiveLattice_regular : RegularSub recursiveLatticeGraph ⟨.value,0,1⟩ :=
  (accepts_sound recursiveLattice_accepted).2.2 _ (by simp)

theorem recursiveLattice_guarded : recursiveLatticeGraph.Guarded :=
  (accepts_sound recursiveLattice_accepted).2.1

theorem recursiveLattice_all_depths (depth : Nat) :
    Approx recursiveLatticeGraph depth ⟨.value,0,1⟩ := recursiveLattice_regular depth

theorem recursiveLattice_missing_effect_rejected :
    accepts recursiveLatticeGraph
      [(⟨.value,0,1⟩,.structural), (⟨.value,3,2⟩,.bottom),
       (⟨.value,4,5⟩,.intersectionIntro (.unionMono .structural .refl) .top)]
      [⟨.value,0,1⟩] = false := rfl

/-- Merely naming a pair in the table cannot discharge a union premise. -/
def unguardedGraph : Graph
  | .value => [.union 0 1,.structural (.atom 10)]
  | .effect => []

theorem unguarded_table_assumption_rejected :
    checkDerivation unguardedGraph [⟨.value,0,1⟩]
      (.unionElim .structural .refl) ⟨.value,0,1⟩ = false := rfl

theorem unguarded_graph_rejected (certificate : Certificate) (demands : List Comparison) :
    accepts unguardedGraph certificate demands = false := by
  have h : checkGuarded unguardedGraph = false := rfl
  simp [accepts,h]

/-! Finite rule correspondence. The readback premise below consists solely
of exact constructor equations. It is used only for this finite-Term bridge,
not for certificate soundness or the cyclic example. No such finite readback
is asserted to exist for a recursive graph. -/
abbrev Readback := (k : Kind) → Nat → Term k

def tupleTerm (read : Readback) : List Nat → Term .value
  | [] => .tupleNil
  | head :: tail => .tupleCons (read .value head) (tupleTerm read tail)

def recordTerm (read : Readback) : List Field → Term .value
  | [] => .recordNil
  | field :: tail => .recordCons field.label field.optional (read .value field.child)
      (recordTerm read tail)

def variantTerm (read : Readback) : List Alternative → Term .value
  | [] => .variantNil
  | alt :: tail => .variantCons alt.tag (tupleTerm read alt.payloads) (variantTerm read tail)

def structuralTerm (read : Readback) : {k : Kind} → Regular.Node k → Term k
  | _, .atom i => .atom i
  | _, .bottom => .bottom
  | _, .top => .top
  | .value, .function a ae re r =>
      .function (read .value a) (read .effect ae) (read .effect re) (read .value r)
  | .value, .record fields => recordTerm read fields
  | .value, .tuple elements => tupleTerm read elements
  | .value, .variant alternatives => variantTerm read alternatives

def nodeTerm (read : Readback) {k} : Node k → Term k
  | .structural node => structuralTerm read node
  | .union a b => .union (read k a) (read k b)
  | .intersection a b => .intersection (read k a) (read k b)

def ReadbackAgrees (graph : Graph) (read : Readback) : Prop :=
  ∀ k i node, graph.lookup k i = some node → read k i = nodeTerm read node

def ReadSub (read : Readback) (pair : Comparison) : Prop :=
  Sub (read pair.kind pair.lower) (read pair.kind pair.upper)

theorem tupleTerm_sub (read : Readback) {xs ys}
    (h : ZipRel (fun a b => Sub (read .value a) (read .value b)) xs ys) :
    Sub (tupleTerm read xs) (tupleTerm read ys) := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => exact .refl _
    | cons _ _ => cases h
  | cons x xs ih => cases ys with
    | nil => cases h
    | cons y ys => exact .tupleCons h.1 (ih h.2)

theorem recordTerm_sub (read : Readback) {xs ys}
    (h : ZipRel (fun a b => a.label = b.label ∧ a.optional = b.optional ∧
      Sub (read .value a.child) (read .value b.child)) xs ys) :
    Sub (recordTerm read xs) (recordTerm read ys) := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => exact .refl _
    | cons _ _ => cases h
  | cons x xs ih => cases ys with
    | nil => cases h
    | cons y ys =>
        rcases x with ⟨label,optional,child⟩
        rcases y with ⟨label',optional',child'⟩
        rcases h with ⟨⟨hl,ho,hc⟩,ht⟩
        dsimp at hl ho hc
        subst label'
        subst optional'
        exact .recordCons label optional hc (ih ht)

theorem variantTerm_sub (read : Readback) {xs ys}
    (h : ZipRel (fun a b => a.tag = b.tag ∧
      ZipRel (fun x y => Sub (read .value x) (read .value y)) a.payloads b.payloads) xs ys) :
    Sub (variantTerm read xs) (variantTerm read ys) := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => exact .refl _
    | cons _ _ => cases h
  | cons x xs ih => cases ys with
    | nil => cases h
    | cons y ys =>
        rcases x with ⟨tag,payloads⟩
        rcases y with ⟨tag',payloads'⟩
        rcases h with ⟨⟨ht,hp⟩,hs⟩
        dsimp at ht hp
        subst tag'
        exact .variantCons tag (tupleTerm_sub read hp) (ih hs)

/-- Exact original finite Sub rules for all reused structural constructors. -/
theorem structuralTerm_sub (read : Readback) {k} {lower upper : Regular.Node k}
    {children : List Comparison} (expanded : expandNodes lower upper = some children)
    (related : ∀ child, child ∈ children → ReadSub read child) :
    Sub (structuralTerm read lower) (structuralTerm read upper) := by
  have h : NodeRel (ReadSub read) lower upper :=
    (nodeRel_iff _ _ _).mpr ((holdsExpansion_iff _ _).mpr ⟨children,expanded,related⟩)
  cases lower <;> cases upper <;> simp only [NodeRel,ReadSub] at h <;>
    first
    | exact False.elim h
    | exact Sub.bottom _
    | exact Sub.top _
    | exact tupleTerm_sub read h
    | exact recordTerm_sub read h
    | exact variantTerm_sub read h
    | exact Sub.function h.1 h.2.1 h.2.2.1 h.2.2.2
    | cases h; exact Sub.refl _

theorem readback_union {graph : Graph} {read : Readback} (agrees : ReadbackAgrees graph read)
    {k i a b} (found : unionAt graph k i = some (a,b)) :
    read k i = .union (read k a) (read k b) := by
  cases lookup : graph.lookup k i with
  | none => simp [unionAt,lookup] at found
  | some node => cases node with
    | structural node => simp [unionAt,lookup] at found
    | intersection l r => simp [unionAt,lookup] at found
    | union l r =>
        have h : l = a ∧ r = b := by simpa [unionAt,lookup] using found
        rcases h with ⟨rfl,rfl⟩
        exact agrees k i _ lookup

theorem readback_intersection {graph : Graph} {read : Readback}
    (agrees : ReadbackAgrees graph read) {k i a b}
    (found : intersectionAt graph k i = some (a,b)) :
    read k i = .intersection (read k a) (read k b) := by
  cases lookup : graph.lookup k i with
  | none => simp [intersectionAt,lookup] at found
  | some node => cases node with
    | structural node => simp [intersectionAt,lookup] at found
    | union l r => simp [intersectionAt,lookup] at found
    | intersection l r =>
        have h : l = a ∧ r = b := by simpa [intersectionAt,lookup] using found
        rcases h with ⟨rfl,rfl⟩
        exact agrees k i _ lookup

theorem readback_bottom {graph : Graph} {read : Readback}
    (agrees : ReadbackAgrees graph read) {k i} (found : bottomAt graph k i = true) :
    read k i = .bottom := by
  cases lookup : graph.lookup k i with
  | none => simp [bottomAt,lookup] at found
  | some node => cases node with
    | union l r => simp [bottomAt,lookup] at found
    | intersection l r => simp [bottomAt,lookup] at found
    | structural node => cases node <;> simp [bottomAt,lookup] at found
                         exact agrees _ _ _ lookup

theorem readback_top {graph : Graph} {read : Readback}
    (agrees : ReadbackAgrees graph read) {k i} (found : topAt graph k i = true) :
    read k i = .top := by
  cases lookup : graph.lookup k i with
  | none => simp [topAt,lookup] at found
  | some node => cases node with
    | union l r => simp [topAt,lookup] at found
    | intersection l r => simp [topAt,lookup] at found
    | structural node => cases node <;> simp [topAt,lookup] at found
                         exact agrees _ _ _ lookup

theorem sub_transport {k} {a b c d : Term k} (left : a = c) (right : b = d)
    (h : Sub c d) : Sub a b := by
  cases left
  cases right
  exact h

theorem structuralExpand_sub {graph : Graph} {read : Readback}
    (agrees : ReadbackAgrees graph read) {k a b children}
    (expanded : structuralExpand graph ⟨k,a,b⟩ = some children)
    (related : ∀ child, child ∈ children → ReadSub read child) :
    Sub (read k a) (read k b) := by
  cases hl : graph.lookup k a with
  | none => simp [structuralExpand,hl] at expanded
  | some lower =>
      cases hr : graph.lookup k b with
      | none => simp [structuralExpand,hr] at expanded
      | some upper =>
          cases lower <;> cases upper <;> simp [structuralExpand,hl,hr] at expanded
          exact sub_transport (agrees _ _ _ hl) (agrees _ _ _ hr)
            (structuralTerm_sub read expanded related)

/-- Every represented layer rule is an actual original Sub derivation under
exact finite readback equations and the structural-port Sub premises. -/
theorem Layer.toSub {graph : Graph} {relation : Comparison → Prop} {read : Readback}
    (agrees : ReadbackAgrees graph read)
    (recursive : ∀ pair, relation pair → ReadSub read pair)
    {pair : Comparison} (h : Layer graph relation pair) : ReadSub read pair := by
  induction h with
  | structural expanded closed =>
      exact structuralExpand_sub agrees expanded (fun c hc => recursive c (closed c hc))
  | refl present => exact .refl _
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | bottom found present =>
      exact sub_transport (readback_bottom agrees found) rfl (.bottom _)
  | top found present =>
      exact sub_transport rfl (readback_top agrees found) (.top _)
  | unionLeft found =>
      exact sub_transport rfl (readback_union agrees found) (.unionLeft _ _)
  | unionRight found =>
      exact sub_transport rfl (readback_union agrees found) (.unionRight _ _)
  | unionElim found _ _ ih₁ ih₂ =>
      exact sub_transport (readback_union agrees found) rfl (.unionElim ih₁ ih₂)
  | intersectionLeft found =>
      exact sub_transport (readback_intersection agrees found) rfl (.intersectionLeft _ _)
  | intersectionRight found =>
      exact sub_transport (readback_intersection agrees found) rfl (.intersectionRight _ _)
  | intersectionIntro found _ _ ih₁ ih₂ =>
      exact sub_transport rfl (readback_intersection agrees found) (.intersectionIntro ih₁ ih₂)
  | unionMono hl hr _ _ ih₁ ih₂ =>
      exact sub_transport (readback_union agrees hl) (readback_union agrees hr) (.unionMono ih₁ ih₂)
  | intersectionMono hl hr _ _ ih₁ ih₂ =>
      exact sub_transport (readback_intersection agrees hl) (readback_intersection agrees hr)
        (.intersectionMono ih₁ ih₂)

end YulangClosure.SimpleSub.Lattice
