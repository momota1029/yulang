import YulangClosure.SimpleSubLatticeCertificates

/-!
Bounded construction of finite lattice certificates on an already fixed graph.

The inner rounds retain explicit finite derivations and try every declared
lattice rule, including every in-range transitivity middle. The outer rounds
only delete comparisons. A strict deletion shortens the finite table, so its
initial length is sufficient to reach a table for which every retained pair
has an actual checked derivation. No model, derivation table, or all-depth
subtyping premise is an input to construction or accepted-output soundness.

Both finite stabilization arguments are proved. For valid graphs the generated
table is exactly the independent all-depth relation. This is a proof-side
reference construction, not a second production inference or coalescing
algorithm. Graph/native construction, history, all original source constructors,
shared scopes and witnesses, full Call and effects remain separate obligations.
-/
namespace YulangClosure.SimpleSub.LatticeDecision
open Regular Lattice

def kindPairs (kind : Kind) (size : Nat) : List Comparison :=
  (List.range size).flatMap (fun lower =>
    (List.range size).map (fun upper => ⟨kind,lower,upper⟩))

def allPairs (graph : Lattice.Graph) : List Comparison :=
  kindPairs .value (graph .value).length ++ kindPairs .effect (graph .effect).length

theorem mem_kindPairs (kind : Kind) (size : Nat) (pair : Comparison) :
    pair ∈ kindPairs kind size ↔
      pair.kind = kind ∧ pair.lower < size ∧ pair.upper < size := by
  constructor
  · intro member
    rcases List.mem_flatMap.mp member with ⟨lower,hlower,member⟩
    rcases List.mem_map.mp member with ⟨upper,hupper,same⟩
    subst pair
    exact ⟨rfl,List.mem_range.mp hlower,List.mem_range.mp hupper⟩
  · rcases pair with ⟨pairKind,lower,upper⟩
    rintro ⟨same,hlower,hupper⟩
    cases same
    exact List.mem_flatMap.mpr ⟨lower,List.mem_range.mpr hlower,
      List.mem_map.mpr ⟨upper,List.mem_range.mpr hupper,rfl⟩⟩

theorem mem_allPairs (graph : Lattice.Graph) (pair : Comparison) :
    pair ∈ allPairs graph ↔
      pair.lower < (graph pair.kind).length ∧ pair.upper < (graph pair.kind).length := by
  rcases pair with ⟨kind,lower,upper⟩
  cases kind <;> simp [allPairs,mem_kindPairs]

/-- Look up an actual finite witness, without introducing a recursive hypothesis. -/
def proofAt : Lattice.Certificate → Comparison → Option Derivation
  | [], _ => none
  | (pair,proof) :: rest, target =>
      if pair = target then some proof else proofAt rest target

theorem proofAt_member {certificate : Lattice.Certificate} {pair proof}
    (found : proofAt certificate pair = some proof) : (pair,proof) ∈ certificate := by
  induction certificate with
  | nil => cases found
  | cons entry rest ih =>
      rcases entry with ⟨p,d⟩
      simp only [proofAt] at found
      split at found
      · rename_i same
        subst p
        cases found
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih found)

def combine (certificate : Lattice.Certificate) (rule : Derivation → Derivation → Derivation)
    (left right : Comparison) : Option Derivation := do
  let first ← proofAt certificate left
  let second ← proofAt certificate right
  pure (rule first second)

/-- All one-rule extensions of the existing witnesses for a fixed pair. -/
def candidates (graph : Lattice.Graph) (prior : Lattice.Certificate)
    (pair : Comparison) : List Derivation :=
  let ⟨k,a,b⟩ := pair
  let unionElim := match unionAt graph k a with
    | some (l,r) => combine prior .unionElim ⟨k,l,b⟩ ⟨k,r,b⟩
    | none => none
  let intersectionIntro := match intersectionAt graph k b with
    | some (l,r) => combine prior .intersectionIntro ⟨k,a,l⟩ ⟨k,a,r⟩
    | none => none
  let unionMono := match unionAt graph k a, unionAt graph k b with
    | some (l,r), some (s,t) => combine prior .unionMono ⟨k,l,s⟩ ⟨k,r,t⟩
    | _, _ => none
  let intersectionMono := match intersectionAt graph k a, intersectionAt graph k b with
    | some (l,r), some (s,t) => combine prior .intersectionMono ⟨k,l,s⟩ ⟨k,r,t⟩
    | _, _ => none
  [.structural,.refl,.bottom,.top,.unionLeft,.unionRight,
    .intersectionLeft,.intersectionRight] ++
    (proofAt prior pair).toList ++ unionElim.toList ++ intersectionIntro.toList ++
    unionMono.toList ++ intersectionMono.toList ++
    (List.range (graph k).length).filterMap (fun middle =>
      combine prior (.trans middle) ⟨k,a,middle⟩ ⟨k,middle,b⟩)

def derive (graph : Lattice.Graph) (recursive : List Comparison)
    (prior : Lattice.Certificate) (pair : Comparison) : Option Derivation :=
  (candidates graph prior pair).find? (fun proof => checkDerivation graph recursive proof pair)

theorem derive_checked {graph recursive prior pair proof}
    (found : derive graph recursive prior pair = some proof) :
    checkDerivation graph recursive proof pair = true := by
  change (candidates graph prior pair).find? (fun d => checkDerivation graph recursive d pair) = some proof at found
  have h := List.find?_some found
  exact h

/-- Each round stores actual witnesses only for the given pending pairs. -/
def layerRound (graph : Lattice.Graph) (recursive : List Comparison)
    (prior : Lattice.Certificate) (pending : List Comparison) : Lattice.Certificate :=
  pending.filterMap (fun pair =>
    (derive graph recursive prior pair).map (fun proof => (pair,proof)))

def Witnesses (graph : Lattice.Graph) (recursive : List Comparison)
    (certificate : Lattice.Certificate) : Prop :=
  ∀ entry, entry ∈ certificate → checkDerivation graph recursive entry.2 entry.1 = true

theorem layerRound_checked (graph : Lattice.Graph) (recursive : List Comparison)
    (prior : Lattice.Certificate) (pending : List Comparison) :
    Witnesses graph recursive (layerRound graph recursive prior pending) := by
  intro entry member
  rcases List.mem_filterMap.mp member with ⟨pair,_,found⟩
  cases h : derive graph recursive prior pair with
  | none => simp [h] at found
  | some proof =>
      simp only [h,Option.map_some,Option.some.injEq] at found
      subst entry
      exact derive_checked h

def remaining (graph : Lattice.Graph) (recursive : List Comparison)
    (prior : Lattice.Certificate) (pending : List Comparison) : List Comparison :=
  pending.filter (fun pair => !(derive graph recursive prior pair).isSome)

def Saturated (graph : Lattice.Graph) (recursive : List Comparison)
    (certificate : Lattice.Certificate) : Prop :=
  ∀ pair, pair ∈ allPairs graph → (derive graph recursive certificate pair).isSome = true →
    pair ∈ table certificate

/-- Every nonstable round strictly shrinks the remaining list. -/
def close (graph : Lattice.Graph) (recursive : List Comparison) :
    Nat → List Comparison → Lattice.Certificate → Lattice.Certificate
  | 0, _, prior => prior
  | fuel + 1, pending, prior =>
      let next := remaining graph recursive prior pending
      if next = pending then prior else
        close graph recursive fuel next (prior ++ layerRound graph recursive prior pending)

theorem remaining_strict {graph recursive prior pending}
    (changed : remaining graph recursive prior pending ≠ pending) :
    (remaining graph recursive prior pending).length < pending.length := by
  have le := List.length_filter_le (fun pair => !(derive graph recursive prior pair).isSome) pending
  have ne : (remaining graph recursive prior pending).length ≠ pending.length := by
    intro same
    apply changed
    exact List.filter_eq_self.mpr (List.length_filter_eq_length_iff.mp same)
  change (remaining graph recursive prior pending).length ≤ pending.length at le
  omega

theorem close_correct (graph : Lattice.Graph) (recursive : List Comparison) (fuel : Nat)
    (pending : List Comparison) (prior : Lattice.Certificate)
    (enough : pending.length ≤ fuel)
    (checked : Witnesses graph recursive prior)
    (covered : ∀ pair, pair ∈ allPairs graph → pair ∈ pending ∨ pair ∈ table prior) :
    Witnesses graph recursive (close graph recursive fuel pending prior) ∧
      Saturated graph recursive (close graph recursive fuel pending prior) := by
  induction fuel generalizing pending prior with
  | zero =>
      have empty : pending = [] := List.length_eq_zero_iff.mp (by omega)
      subst pending
      refine ⟨checked,?_⟩
      intro pair hp _
      exact (covered pair hp).resolve_left (by simp)
  | succ fuel ih =>
      simp only [close]
      split
      · rename_i fixed
        refine ⟨checked,?_⟩
        intro pair hp derived
        rcases covered pair hp with member | member
        · have failed := List.filter_eq_self.mp fixed pair member
          simp [derived] at failed
        · exact member
      · rename_i changed
        apply ih
        · have strict := remaining_strict changed
          omega
        · intro entry member
          rcases List.mem_append.mp member with old | new
          · exact checked entry old
          · exact layerRound_checked _ _ _ _ entry new
        · intro pair hp
          rcases covered pair hp with old | old
          · cases found : derive graph recursive prior pair with
            | none => exact Or.inl (List.mem_filter.mpr ⟨old,by simp [found]⟩)
            | some proof =>
                apply Or.inr
                apply List.mem_map.mpr
                refine ⟨(pair,proof),List.mem_append_right _ ?_,rfl⟩
                exact List.mem_filterMap.mpr ⟨pair,old,by simp [found]⟩
          · apply Or.inr
            simpa [table,List.map_append] using List.mem_append_left
              (table (layerRound graph recursive prior pending)) old

def layerCertificate (graph : Lattice.Graph) (recursive : List Comparison) : Lattice.Certificate :=
  close graph recursive (allPairs graph).length (allPairs graph) []

theorem layerCertificate_correct (graph : Lattice.Graph) (recursive : List Comparison) :
    Witnesses graph recursive (layerCertificate graph recursive) ∧
      Saturated graph recursive (layerCertificate graph recursive) :=
  close_correct _ _ _ _ _ (Nat.le_refl _) (by simp [Witnesses])
    (fun _ hp => Or.inl hp)

theorem layerCertificate_checked (graph : Lattice.Graph) (recursive : List Comparison) :
    Witnesses graph recursive (layerCertificate graph recursive) :=
  (layerCertificate_correct graph recursive).1

def supported (graph : Lattice.Graph) (recursive : List Comparison) (pair : Comparison) : Bool :=
  (proofAt (layerCertificate graph recursive) pair).isSome

def pruneStep (graph : Lattice.Graph) (recursive : List Comparison) : List Comparison :=
  let available := layerCertificate graph recursive
  recursive.filter (fun pair => (proofAt available pair).isSome)

def prune (graph : Lattice.Graph) : Nat → List Comparison → List Comparison
  | 0, recursive => recursive
  | fuel + 1, recursive =>
      let next := pruneStep graph recursive
      if next = recursive then recursive else prune graph fuel next

theorem pruneStep_strict {graph : Lattice.Graph} {recursive : List Comparison}
    (changed : pruneStep graph recursive ≠ recursive) :
    (pruneStep graph recursive).length < recursive.length := by
  have le := List.length_filter_le (supported graph recursive) recursive
  have ne : (pruneStep graph recursive).length ≠ recursive.length := by
    intro same
    apply changed
    exact List.filter_eq_self.mpr (List.length_filter_eq_length_iff.mp same)
  change (pruneStep graph recursive).length ≤ recursive.length at le
  omega

theorem prune_supported (graph : Lattice.Graph) (fuel : Nat) (recursive : List Comparison)
    (enough : recursive.length ≤ fuel) :
    ∀ pair, pair ∈ prune graph fuel recursive →
      supported graph (prune graph fuel recursive) pair = true := by
  induction fuel generalizing recursive with
  | zero =>
      have empty : recursive = [] := List.length_eq_zero_iff.mp (by omega)
      subst recursive
      simp [prune]
  | succ fuel ih =>
      simp only [prune]
      split
      · rename_i fixed
        exact List.filter_eq_self.mp fixed
      · apply ih
        have strict := pruneStep_strict ‹_›
        omega

/-- Retain precisely the requested recursive table, with actual located witnesses. -/
def extract (available : Lattice.Certificate) (recursive : List Comparison) : Lattice.Certificate :=
  recursive.filterMap (fun pair => (proofAt available pair).map (fun proof => (pair,proof)))

theorem extract_table (available : Lattice.Certificate) (recursive : List Comparison)
    (complete : ∀ pair, pair ∈ recursive → (proofAt available pair).isSome = true) :
    table (extract available recursive) = recursive := by
  induction recursive with
  | nil => rfl
  | cons pair rest ih =>
      have h := complete pair (by simp)
      cases found : proofAt available pair with
      | none => simp [found] at h
      | some proof =>
          have tail := ih (fun p hp => complete p (List.mem_cons_of_mem _ hp))
          simpa [extract,table,found] using congrArg (List.cons pair) tail

theorem extract_checked {graph : Lattice.Graph} {available : Lattice.Certificate}
    {recursive : List Comparison}
    (checked : Witnesses graph recursive available)
    (complete : ∀ pair, pair ∈ recursive → (proofAt available pair).isSome = true) :
    checkCertificate graph (extract available recursive) = true := by
  have same := extract_table available recursive complete
  apply List.all_eq_true.mpr
  intro entry member
  rcases List.mem_filterMap.mp member with ⟨pair,_,found⟩
  cases hp : proofAt available pair with
  | none => simp [hp] at found
  | some proof =>
      simp only [hp,Option.map_some,Option.some.injEq] at found
      subst entry
      rw [same]
      exact checked _ (proofAt_member hp)

def finalTable (graph : Lattice.Graph) : List Comparison :=
  prune graph (allPairs graph).length (allPairs graph)

/-- The graph is the sole input; no externally supplied finite table remains. -/
def constructCertificate (graph : Lattice.Graph) : Lattice.Certificate :=
  let recursive := finalTable graph
  extract (layerCertificate graph recursive) recursive

theorem constructed_table (graph : Lattice.Graph) :
    table (constructCertificate graph) = finalTable graph :=
  extract_table _ _ (prune_supported graph _ _ (Nat.le_refl _))

theorem constructed_checked (graph : Lattice.Graph) :
    checkCertificate graph (constructCertificate graph) = true :=
  extract_checked (layerCertificate_checked _ _) (prune_supported graph _ _ (Nat.le_refl _))

theorem constructed_sound (graph : Lattice.Graph) :
    ∀ pair, pair ∈ table (constructCertificate graph) → Lattice.RegularSub graph pair :=
  Lattice.certificate_sound (constructed_checked graph)

def decideDemands (graph : Lattice.Graph) (demands : List Comparison) : Bool :=
  Lattice.accepts graph (constructCertificate graph) demands

theorem decideDemands_sound {graph : Lattice.Graph} {demands : List Comparison}
    (accepted : decideDemands graph demands = true) :
    graph.Valid ∧ graph.Guarded ∧
      ∀ pair, pair ∈ demands → Lattice.RegularSub graph pair :=
  Lattice.accepts_sound accepted

theorem decided_joint_relation {graph : Lattice.Graph} {demands : List Comparison}
    (accepted : decideDemands graph demands = true) :
    graph.Valid ∧ graph.Guarded ∧ ∃ relation : Comparison → Prop,
      (∀ pair, relation pair → Lattice.Layer graph relation pair) ∧
      (∀ pair, pair ∈ demands → relation pair) ∧
      (∀ pair, relation pair → Lattice.RegularSub graph pair) :=
  Lattice.accepted_joint_relation accepted


theorem proofAt_exists {certificate : Lattice.Certificate} {pair}
    (member : pair ∈ table certificate) : ∃ proof, proofAt certificate pair = some proof := by
  induction certificate with
  | nil => cases member
  | cons entry rest ih =>
      rcases entry with ⟨p,d⟩
      simp only [table,List.map_cons,List.mem_cons] at member
      simp only [proofAt]
      split
      · exact ⟨d,rfl⟩
      · rename_i different
        exact ih (member.resolve_left (Ne.symm different))

theorem find_isSome_of_mem {α : Type} (test : α → Bool) {items : List α} {item : α}
    (member : item ∈ items) (passes : test item = true) :
    (items.find? test).isSome = true := by
  induction items with
  | nil => cases member
  | cons head tail ih =>
      simp only [List.find?]
      split
      · rfl
      · rename_i failed
        rcases List.mem_cons.mp member with same | member
        · subst head
          simp [passes] at failed
        · exact ih member

theorem saturated_rule {graph recursive certificate pair proof}
    (saturated : Saturated graph recursive certificate)
    (bounded : pair ∈ allPairs graph)
    (candidate : proof ∈ candidates graph certificate pair)
    (checked : checkDerivation graph recursive proof pair = true) :
    pair ∈ table certificate :=
  saturated pair bounded (find_isSome_of_mem _ candidate checked)

theorem lookupList_index_lt {α : Type} {items : List α} {index : Nat} {item : α}
    (found : lookupList items index = some item) : index < items.length := by
  induction items generalizing index with
  | nil => cases found
  | cons head tail ih =>
      cases index with
      | zero => simp
      | succ index => exact Nat.succ_lt_succ (ih found)

theorem exists_index {graph : Lattice.Graph} {k i} (present : Lattice.Exists graph k i) :
    i < (graph k).length := by
  rcases present with ⟨node,found⟩
  exact lookupList_index_lt found

theorem union_exists {graph : Lattice.Graph} (valid : graph.Valid) {k u a b}
    (found : unionAt graph k u = some (a,b)) :
    Lattice.Exists graph k u ∧ Lattice.Exists graph k a ∧ Lattice.Exists graph k b := by
  cases lookup : graph.lookup k u with
  | none => simp [unionAt,lookup] at found
  | some node => cases node with
    | structural node => simp [unionAt,lookup] at found
    | intersection l r => simp [unionAt,lookup] at found
    | union l r =>
        have same : l = a ∧ r = b := by simpa [unionAt,lookup] using found
        rcases same with ⟨rfl,rfl⟩
        have h := (valid k _ (lookupList_mem lookup)).2
        exact ⟨⟨_,lookup⟩,h ⟨k,l⟩ (by simp [Lattice.Node.references]),
          h ⟨k,r⟩ (by simp [Lattice.Node.references])⟩

theorem intersection_exists {graph : Lattice.Graph} (valid : graph.Valid) {k u a b}
    (found : intersectionAt graph k u = some (a,b)) :
    Lattice.Exists graph k u ∧ Lattice.Exists graph k a ∧ Lattice.Exists graph k b := by
  cases lookup : graph.lookup k u with
  | none => simp [intersectionAt,lookup] at found
  | some node => cases node with
    | structural node => simp [intersectionAt,lookup] at found
    | union l r => simp [intersectionAt,lookup] at found
    | intersection l r =>
        have same : l = a ∧ r = b := by simpa [intersectionAt,lookup] using found
        rcases same with ⟨rfl,rfl⟩
        have h := (valid k _ (lookupList_mem lookup)).2
        exact ⟨⟨_,lookup⟩,h ⟨k,l⟩ (by simp [Lattice.Node.references]),
          h ⟨k,r⟩ (by simp [Lattice.Node.references])⟩

theorem bottom_exists {graph : Lattice.Graph} {k i} (found : bottomAt graph k i = true) :
    Lattice.Exists graph k i := by
  cases lookup : graph.lookup k i with
  | none => simp [bottomAt,lookup] at found
  | some node => exact ⟨node,lookup⟩

theorem top_exists {graph : Lattice.Graph} {k i} (found : topAt graph k i = true) :
    Lattice.Exists graph k i := by
  cases lookup : graph.lookup k i with
  | none => simp [topAt,lookup] at found
  | some node => exact ⟨node,lookup⟩

theorem structural_exists {graph : Lattice.Graph} {pair children}
    (found : structuralExpand graph pair = some children) :
    Lattice.Exists graph pair.kind pair.lower ∧ Lattice.Exists graph pair.kind pair.upper := by
  cases left : graph.lookup pair.kind pair.lower with
  | none => simp [structuralExpand,left] at found
  | some lower =>
      cases right : graph.lookup pair.kind pair.upper with
      | none => cases lower <;> simp [structuralExpand,left,right] at found
      | some upper => exact ⟨⟨lower,left⟩,⟨upper,right⟩⟩

/-- In a valid graph, transitivity cannot use an out-of-range middle. -/
theorem layer_endpoints {graph : Lattice.Graph} (valid : graph.Valid) {relation pair}
    (h : Lattice.Layer graph relation pair) :
    Lattice.Exists graph pair.kind pair.lower ∧ Lattice.Exists graph pair.kind pair.upper := by
  induction h with
  | structural found _ => exact structural_exists found
  | refl present => exact ⟨present,present⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1,ih₂.2⟩
  | bottom found present => exact ⟨bottom_exists found,present⟩
  | top found present => exact ⟨present,top_exists found⟩
  | unionLeft found =>
      have e := union_exists valid found
      exact ⟨e.2.1,e.1⟩
  | unionRight found =>
      have e := union_exists valid found
      exact ⟨e.2.2,e.1⟩
  | unionElim found _ _ _ ih₂ => exact ⟨(union_exists valid found).1,ih₂.2⟩
  | intersectionLeft found =>
      have e := intersection_exists valid found
      exact ⟨e.1,e.2.1⟩
  | intersectionRight found =>
      have e := intersection_exists valid found
      exact ⟨e.1,e.2.2⟩
  | intersectionIntro found _ _ ih₁ _ => exact ⟨ih₁.1,(intersection_exists valid found).1⟩
  | unionMono left right _ _ _ _ =>
      exact ⟨(union_exists valid left).1,(union_exists valid right).1⟩
  | intersectionMono left right _ _ _ _ =>
      exact ⟨(intersection_exists valid left).1,(intersection_exists valid right).1⟩

theorem layer_bounded {graph : Lattice.Graph} (valid : graph.Valid) {relation pair}
    (h : Lattice.Layer graph relation pair) : pair ∈ allPairs graph := by
  have e := layer_endpoints valid h
  exact (mem_allPairs graph pair).mpr ⟨exists_index e.1,exists_index e.2⟩


/-- A stable finite rule closure contains every independent finite Layer
derivation. This is where the full rule inventory and valid middle bounds
are used; no common infinite-depth derivation is selected. -/
theorem saturated_complete {graph : Lattice.Graph} (valid : graph.Valid)
    {recursive : List Comparison} {certificate : Lattice.Certificate}
    (checked : Witnesses graph recursive certificate)
    (saturated : Saturated graph recursive certificate) {pair}
    (h : Lattice.Layer graph (fun p => p ∈ recursive) pair) : pair ∈ table certificate := by
  suffices pair ∈ allPairs graph → pair ∈ table certificate from this (layer_bounded valid h)
  induction h with
  | structural expanded closed =>
      intro bounded
      apply saturated_rule saturated bounded (proof := .structural)
      · simp [candidates]
      · simpa [checkDerivation,expanded,List.all_eq_true] using closed
  | refl present =>
      intro bounded
      apply saturated_rule saturated bounded (proof := .refl)
      · simp [candidates]
      · simp [checkDerivation,existsAt_iff,present]
  | bottom found present =>
      intro bounded
      apply saturated_rule saturated bounded (proof := .bottom)
      · simp [candidates]
      · simp [checkDerivation,found,existsAt_iff,present]
  | top found present =>
      intro bounded
      apply saturated_rule saturated bounded (proof := .top)
      · simp [candidates]
      · simp [checkDerivation,found,existsAt_iff,present]
  | unionLeft found =>
      intro bounded
      apply saturated_rule saturated bounded (proof := .unionLeft)
      · simp [candidates]
      · simp [checkDerivation,found]
  | unionRight found =>
      intro bounded
      apply saturated_rule saturated bounded (proof := .unionRight)
      · simp [candidates]
      · simp [checkDerivation,found]
  | intersectionLeft found =>
      intro bounded
      apply saturated_rule saturated bounded (proof := .intersectionLeft)
      · simp [candidates]
      · simp [checkDerivation,found]
  | intersectionRight found =>
      intro bounded
      apply saturated_rule saturated bounded (proof := .intersectionRight)
      · simp [candidates]
      · simp [checkDerivation,found]
  | @trans k a b c first second ih₁ ih₂ =>
      intro bounded
      rcases proofAt_exists (ih₁ (layer_bounded valid first)) with ⟨p,hp⟩
      rcases proofAt_exists (ih₂ (layer_bounded valid second)) with ⟨q,hq⟩
      have cp := checked _ (proofAt_member hp)
      have cq := checked _ (proofAt_member hq)
      apply saturated_rule saturated bounded (proof := .trans b p q)
      · change (Derivation.trans b p q) ∈ _ ++ (List.range (graph k).length).filterMap _
        apply List.mem_append_right
        exact List.mem_filterMap.mpr ⟨b,List.mem_range.mpr
          (exists_index (layer_endpoints valid first).2),by simp [combine,hp,hq]⟩
      · simpa only [checkDerivation,Bool.and_eq_true] using And.intro cp cq
  | unionElim found first second ih₁ ih₂ =>
      intro bounded
      rcases proofAt_exists (ih₁ (layer_bounded valid first)) with ⟨p,hp⟩
      rcases proofAt_exists (ih₂ (layer_bounded valid second)) with ⟨q,hq⟩
      have cp := checked _ (proofAt_member hp)
      have cq := checked _ (proofAt_member hq)
      apply saturated_rule saturated bounded (proof := .unionElim p q)
      · simp [candidates,found,combine,hp,hq]
      · simpa only [checkDerivation,found,Bool.and_eq_true] using And.intro cp cq
  | intersectionIntro found first second ih₁ ih₂ =>
      intro bounded
      rcases proofAt_exists (ih₁ (layer_bounded valid first)) with ⟨p,hp⟩
      rcases proofAt_exists (ih₂ (layer_bounded valid second)) with ⟨q,hq⟩
      have cp := checked _ (proofAt_member hp)
      have cq := checked _ (proofAt_member hq)
      apply saturated_rule saturated bounded (proof := .intersectionIntro p q)
      · simp [candidates,found,combine,hp,hq]
      · simpa only [checkDerivation,found,Bool.and_eq_true] using And.intro cp cq
  | unionMono left right first second ih₁ ih₂ =>
      intro bounded
      rcases proofAt_exists (ih₁ (layer_bounded valid first)) with ⟨p,hp⟩
      rcases proofAt_exists (ih₂ (layer_bounded valid second)) with ⟨q,hq⟩
      have cp := checked _ (proofAt_member hp)
      have cq := checked _ (proofAt_member hq)
      apply saturated_rule saturated bounded (proof := .unionMono p q)
      · simp [candidates,left,right,combine,hp,hq]
      · simpa only [checkDerivation,left,right,Bool.and_eq_true] using And.intro cp cq
  | intersectionMono left right first second ih₁ ih₂ =>
      intro bounded
      rcases proofAt_exists (ih₁ (layer_bounded valid first)) with ⟨p,hp⟩
      rcases proofAt_exists (ih₂ (layer_bounded valid second)) with ⟨q,hq⟩
      have cp := checked _ (proofAt_member hp)
      have cq := checked _ (proofAt_member hq)
      apply saturated_rule saturated bounded (proof := .intersectionMono p q)
      · simp [candidates,left,right,combine,hp,hq]
      · simpa only [checkDerivation,left,right,Bool.and_eq_true] using And.intro cp cq

theorem layerCertificate_exact {graph : Lattice.Graph} (valid : graph.Valid)
    (recursive : List Comparison) (pair : Comparison) :
    pair ∈ table (layerCertificate graph recursive) ↔
      Lattice.Layer graph (fun p => p ∈ recursive) pair := by
  constructor
  · intro member
    rcases proofAt_exists member with ⟨proof,found⟩
    rcases pair with ⟨k,a,b⟩
    exact Lattice.checkDerivation_sound proof
      (layerCertificate_checked graph recursive _ (proofAt_member found))
  · exact saturated_complete valid (layerCertificate_correct graph recursive).1
      (layerCertificate_correct graph recursive).2

theorem supported_iff {graph : Lattice.Graph} (valid : graph.Valid)
    (recursive : List Comparison) (pair : Comparison) :
    supported graph recursive pair = true ↔
      Lattice.Layer graph (fun p => p ∈ recursive) pair := by
  rw [← layerCertificate_exact valid recursive pair]
  constructor
  · intro h
    cases found : proofAt (layerCertificate graph recursive) pair with
    | none => simp [supported,found] at h
    | some proof => exact List.mem_map.mpr ⟨(pair,proof),proofAt_member found,rfl⟩
  · intro member
    rcases proofAt_exists member with ⟨proof,found⟩
    simp [supported,found]


theorem approx_down (graph : Lattice.Graph) (depth : Nat) (pair : Comparison)
    (h : Lattice.Approx graph (depth + 1) pair) : Lattice.Approx graph depth pair := by
  induction depth generalizing pair with
  | zero => trivial
  | succ depth ih => exact Lattice.Layer.mono (fun p hp => ih p hp) h

/-- A finite depth at which the current table covers the independent
approximant. This invariant is constructed, never supplied by a caller. -/
def FiniteCover (graph : Lattice.Graph) (recursive : List Comparison) : Prop :=
  ∃ depth, ∀ pair, Lattice.Approx graph (depth + 1) pair → pair ∈ recursive

theorem pruneStep_cover {graph : Lattice.Graph} (valid : graph.Valid)
    {recursive : List Comparison} (cover : FiniteCover graph recursive) :
    FiniteCover graph (pruneStep graph recursive) := by
  rcases cover with ⟨depth,cover⟩
  refine ⟨depth + 1,?_⟩
  intro pair h
  apply List.mem_filter.mpr
  refine ⟨cover pair (approx_down graph (depth + 1) pair h),?_⟩
  exact (supported_iff valid recursive pair).mpr (Lattice.Layer.mono cover h)

theorem prune_cover {graph : Lattice.Graph} (valid : graph.Valid) (fuel : Nat)
    (recursive : List Comparison) (cover : FiniteCover graph recursive) :
    FiniteCover graph (prune graph fuel recursive) := by
  induction fuel generalizing recursive with
  | zero => exact cover
  | succ fuel ih =>
      simp only [prune]
      split
      · exact cover
      · exact ih _ (pruneStep_cover valid cover)

theorem universe_cover {graph : Lattice.Graph} (valid : graph.Valid) :
    FiniteCover graph (allPairs graph) :=
  ⟨0,fun _ h => layer_bounded valid h⟩

/-- Exactness follows from two finite stabilization proofs. The reverse
all-depth unfolding law is a consequence, not a premise. -/
theorem constructed_exact {graph : Lattice.Graph} (valid : graph.Valid) (pair : Comparison) :
    pair ∈ table (constructCertificate graph) ↔ Lattice.RegularSub graph pair := by
  constructor
  · exact constructed_sound graph pair
  · intro regular
    rw [constructed_table]
    rcases prune_cover valid (allPairs graph).length (allPairs graph) (universe_cover valid) with
      ⟨depth,covered⟩
    exact covered pair (regular (depth + 1))

/-- On this finite valid graph, one common finite layer can now be obtained
from all depth witnesses by membership in the constructed certificate. -/
theorem regular_unfold {graph : Lattice.Graph} (valid : graph.Valid) (pair : Comparison) :
    Lattice.RegularSub graph pair ↔ Lattice.Layer graph (Lattice.RegularSub graph) pair := by
  constructor
  · intro regular
    exact Lattice.Layer.mono (constructed_sound graph)
      (Lattice.checkCertificate_postfixed (constructed_checked graph) pair
        ((constructed_exact valid pair).mpr regular))
  · exact Lattice.regular_fold

/-- Guard checking remains the accepted graph-fragment condition. This does
not assert that every original source graph is guarded or that the guard
checker is complete for a different source-language judgment. -/
theorem decideDemands_exact (graph : Lattice.Graph) (demands : List Comparison) :
    decideDemands graph demands = true ↔
      graph.Valid ∧ Lattice.checkGuarded graph = true ∧
        ∀ pair, pair ∈ demands → Lattice.RegularSub graph pair := by
  constructor
  · intro accepted
    have h : Lattice.checkGraph graph = true ∧ Lattice.checkGuarded graph = true ∧
        Lattice.checkCertificate graph (constructCertificate graph) = true ∧
        ∀ pair, pair ∈ demands → pair ∈ table (constructCertificate graph) := by
      simpa [decideDemands,Lattice.accepts,List.all_eq_true,and_assoc] using accepted
    exact ⟨(Lattice.checkGraph_iff graph).mp h.1,h.2.1,
      fun pair hp => constructed_sound graph pair (h.2.2.2 pair hp)⟩
  · rintro ⟨valid,guarded,related⟩
    have members : ∀ pair, pair ∈ demands → pair ∈ table (constructCertificate graph) :=
      fun pair hp => (constructed_exact valid pair).mpr (related pair hp)
    simpa [decideDemands,Lattice.accepts,List.all_eq_true,and_assoc,
      constructed_checked,(Lattice.checkGraph_iff graph).mpr valid,guarded] using members

theorem decideDemands_rejects_iff (graph : Lattice.Graph) (demands : List Comparison) :
    decideDemands graph demands = false ↔
      ¬ (graph.Valid ∧ Lattice.checkGuarded graph = true ∧
        ∀ pair, pair ∈ demands → Lattice.RegularSub graph pair) := by
  rw [← decideDemands_exact]
  cases decideDemands graph demands <;> simp

/-- The recursive Function/lattice example now needs no external witness table. -/
theorem recursiveLattice_decided :
    decideDemands recursiveLatticeGraph [⟨.value,0,1⟩] = true := by
  apply (decideDemands_exact _ _).mpr
  refine ⟨(Lattice.accepts_sound recursiveLattice_accepted).1,?_,?_⟩
  · rfl
  · intro pair member
    simp only [List.mem_singleton] at member
    subst pair
    exact recursiveLattice_regular

theorem unguarded_decision_rejected (demands : List Comparison) :
    decideDemands unguardedGraph demands = false :=
  Lattice.unguarded_graph_rejected _ _


/-- Direct kernel computation of lattice injection and genuine failed union elimination. -/
def finiteLatticeGraph : Lattice.Graph
  | .value => [.structural (.atom 0),.structural (.atom 1),.union 0 1]
  | .effect => []

theorem finite_injection_computed :
    decideDemands finiteLatticeGraph [⟨.value,0,2⟩] = true := by decide

theorem finite_union_elimination_rejected :
    decideDemands finiteLatticeGraph [⟨.value,2,0⟩] = false := by decide

end YulangClosure.SimpleSub.LatticeDecision
