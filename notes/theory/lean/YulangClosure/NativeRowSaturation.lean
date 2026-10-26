import YulangClosure.NativeRowModel

/-!
Executable finite closure of structural row clauses. Every nonstable round
strictly removes pending bounded comparisons; the initial universe size is a
proved sufficient iteration bound. The returned graph and interpretation are
then constructed by NativeRowModel, for the ORIGINAL input clauses.

This is a proof-side reference procedure, not an added native checking pass.
Exact structural metadata and all four signed Function ports are inherited
from Regular.expandNodes. Original optional/width adaptation, contextual
effects and actual native/output correspondence remain separate obligations.
-/
namespace YulangClosure.SimpleSub.NativeRowSaturation
open Regular (Comparison Reference lookupList expandNodes renamePair NodeRel)
open NativeRowModel

def Bounded (s : System) (p : Comparison) : Prop :=
  p.lower < s.rows p.kind + (s.heads p.kind).length ∧
  p.upper < s.rows p.kind + (s.heads p.kind).length

instance (s : System) (p : Comparison) : Decidable (Bounded s p) :=
  inferInstanceAs (Decidable (_ ∧ _))

def pairUniverse (s : System) : List Comparison :=
  LatticeDecision.kindPairs .value (s.rows .value + (s.heads .value).length) ++
  LatticeDecision.kindPairs .effect (s.rows .effect + (s.heads .effect).length)

@[simp] theorem mem_pairUniverse (s : System) (p : Comparison) :
    p ∈ pairUniverse s ↔ Bounded s p := by
  rcases p with ⟨k,x,y⟩
  cases k <;> simp [pairUniverse,LatticeDecision.mem_kindPairs,Bounded]

def withClauses (s : System) (clauses : List Comparison) : System :=
  {s with clauses := clauses}

def headExpansion (s : System) (p : Comparison) : Option (List Comparison) := do
  let a ← lookupList (s.heads p.kind) (p.lower - s.rows p.kind)
  let b ← lookupList (s.heads p.kind) (p.upper - s.rows p.kind)
  expandNodes a b

/-- A row→target clause propagates every retained head lower bound. A
head→head clause emits the exact signed constructor children. Head→row is
already a lower bound. No transitive semantic comparison is used here. -/
def consequences (s : System) (prior : List Comparison) (p : Comparison) : List Comparison :=
  if p.lower < s.rows p.kind then
    ((withClauses s prior).lower p.kind p.lower).map
      (fun h => ⟨p.kind,s.head p.kind h,p.upper⟩)
  else if p.upper < s.rows p.kind then []
  else (headExpansion s p).getD []

def demands (s : System) (prior : List Comparison) : List Comparison :=
  prior.flatMap (consequences s prior)

def remaining (s : System) (prior pending : List Comparison) : List Comparison :=
  pending.filter (fun p => p ∉ demands s prior)

def additions (s : System) (prior pending : List Comparison) : List Comparison :=
  pending.filter (fun p => p ∈ demands s prior)

def Separate (prior pending : List Comparison) : Prop :=
  ∀ p, p ∈ pending → p ∉ prior

theorem additions_new {s : System} {prior pending : List Comparison}
    (separate : Separate prior pending) :
    ∀ p, p ∈ additions s prior pending → p ∉ prior :=
  fun p hp => separate p (List.mem_filter.mp hp).1

theorem remaining_separate {s : System} {prior pending : List Comparison}
    (separate : Separate prior pending) :
    Separate (prior ++ additions s prior pending) (remaining s prior pending) := by
  intro p hp old
  obtain ⟨pendingMem,notNeeded⟩ := List.mem_filter.mp hp
  rcases List.mem_append.mp old with old | added
  · exact separate p pendingMem old
  · have needed := of_decide_eq_true (List.mem_filter.mp added).2
    exact of_decide_eq_true notNeeded needed

/-- This fuel is not an unproved cutoff: close_correct proves that every
initial pending list has reached closure by its own length. -/
def close (s : System) : Nat → List Comparison → List Comparison → List Comparison
  | 0, _, prior => prior
  | fuel + 1, pending, prior =>
      let next := remaining s prior pending
      if next = pending then prior
      else close s fuel next (prior ++ additions s prior pending)

def Closed (s : System) (prior : List Comparison) : Prop :=
  ∀ p, Bounded s p → p ∈ demands s prior → p ∈ prior

theorem remaining_strict {s prior pending}
    (changed : remaining s prior pending ≠ pending) :
    (remaining s prior pending).length < pending.length := by
  have le := List.length_filter_le (fun p => decide (p ∉ demands s prior)) pending
  have ne : (remaining s prior pending).length ≠ pending.length := by
    intro same
    apply changed
    exact List.filter_eq_self.mpr (List.length_filter_eq_length_iff.mp same)
  change (remaining s prior pending).length ≤ pending.length at le
  omega

theorem close_retains (s : System) (fuel : Nat) (pending prior : List Comparison) :
    ∀ p, p ∈ prior → p ∈ close s fuel pending prior := by
  induction fuel generalizing pending prior with
  | zero => exact fun _ hp => hp
  | succ fuel ih =>
      simp only [close]
      split
      · exact fun _ hp => hp
      · exact fun p hp => ih _ _ p (List.mem_append_left _ hp)

theorem close_prefix (s : System) (fuel : Nat) (pending prior : List Comparison) :
    ∃ extra, close s fuel pending prior = prior ++ extra := by
  induction fuel generalizing pending prior with
  | zero => exact ⟨[],(List.append_nil prior).symm⟩
  | succ fuel ih =>
      simp only [close]
      split
      · exact ⟨[],(List.append_nil prior).symm⟩
      · obtain ⟨extra,eq⟩ := ih (remaining s prior pending) (prior ++ additions s prior pending)
        exact ⟨additions s prior pending ++ extra,eq.trans (List.append_assoc _ _ _)⟩

theorem close_correct (s : System) (fuel : Nat) (pending prior : List Comparison)
    (enough : pending.length ≤ fuel)
    (priorBounded : ∀ p, p ∈ prior → Bounded s p)
    (pendingBounded : ∀ p, p ∈ pending → Bounded s p)
    (covered : ∀ p, Bounded s p → p ∈ pending ∨ p ∈ prior) :
    (∀ p, p ∈ close s fuel pending prior → Bounded s p) ∧
      Closed s (close s fuel pending prior) := by
  induction fuel generalizing pending prior with
  | zero =>
      have empty : pending = [] := List.length_eq_zero_iff.mp (by omega)
      subst pending
      exact ⟨priorBounded,fun p hp _ => (covered p hp).resolve_left (by simp)⟩
  | succ fuel ih =>
      simp only [close]
      split
      · rename_i fixed
        refine ⟨priorBounded,?_⟩
        intro p hp needed
        rcases covered p hp with member | member
        · have failed := List.filter_eq_self.mp fixed p member
          simp [needed] at failed
        · exact member
      · rename_i changed
        apply ih
        · have strict := remaining_strict changed
          omega
        · intro p hp
          rcases List.mem_append.mp hp with old | added
          · exact priorBounded p old
          · exact pendingBounded p (List.mem_filter.mp added).1
        · intro p hp
          exact pendingBounded p (List.mem_filter.mp hp).1
        · intro p hp
          rcases covered p hp with old | old
          · by_cases needed : p ∈ demands s prior
            · exact Or.inr (List.mem_append_right _ (List.mem_filter.mpr ⟨old,by simpa using needed⟩))
            · exact Or.inl (List.mem_filter.mpr ⟨old,by simpa using needed⟩)
          · exact Or.inr (List.mem_append_left _ old)

def initialPending (s : System) : List Comparison :=
  (pairUniverse s).filter (fun p => p ∉ s.clauses)

theorem initial_separate (s : System) : Separate s.clauses (initialPending s) :=
  fun _ hp => of_decide_eq_true (List.mem_filter.mp hp).2

def clauses (s : System) : List Comparison :=
  close s (initialPending s).length (initialPending s) s.clauses

def completed (s : System) : System := withClauses s (clauses s)

theorem clauses_retains (s : System) : ∀ p, p ∈ s.clauses → p ∈ clauses s :=
  close_retains _ _ _ _

theorem clauses_prefix (s : System) : ∃ extra, (completed s).clauses = s.clauses ++ extra :=
  close_prefix _ _ _ _

theorem clauses_correct {s : System}
    (bounded : ∀ p, p ∈ s.clauses → Bounded s p) :
    (∀ p, p ∈ clauses s → Bounded s p) ∧ Closed s (clauses s) := by
  apply close_correct _ _ _ _ (Nat.le_refl _) bounded
  · intro p hp
    exact (mem_pairUniverse s p).mp (List.mem_filter.mp hp).1
  · intro p hp
    by_cases member : p ∈ s.clauses
    · exact Or.inr member
    · exact Or.inl (List.mem_filter.mpr ⟨(mem_pairUniverse s p).mpr hp,by simpa using member⟩)

def checkBounds (s : System) (ps : List Comparison) : Bool :=
  ps.all (fun p => decide (Bounded s p))

@[simp] theorem checkBounds_iff (s : System) (ps : List Comparison) :
    checkBounds s ps = true ↔ ∀ p, p ∈ ps → Bounded s p := by
  simp [checkBounds,List.all_eq_true]

def checkNode (s : System) {k} (node : Regular.Node k) : Bool :=
  decide node.uniqueLabels && node.references.all
    (fun r => decide (r.identity < s.rows r.kind + (s.heads r.kind).length))

def checkFormation (s : System) : Bool :=
  (s.heads .value).all (checkNode s) && (s.heads .effect).all (checkNode s)

theorem checkFormation_iff (s : System) : checkFormation s = true ↔
    ∀ k node, node ∈ s.heads k → node.uniqueLabels ∧
      ∀ r, r ∈ node.references → r.identity < s.rows r.kind + (s.heads r.kind).length := by
  simp only [checkFormation,Bool.and_eq_true,List.all_eq_true,checkNode,decide_eq_true_eq]
  constructor
  · rintro ⟨hv,he⟩ k
    cases k
    · exact hv
    · exact he
  · intro h
    exact ⟨h .value,h .effect⟩

def compatible (s : System) (p : Comparison) : Bool :=
  if p.lower < s.rows p.kind ∨ p.upper < s.rows p.kind then true
  else (headExpansion s p).isSome

def checkCompatible (s : System) (ps : List Comparison) : Bool := ps.all (compatible s)

theorem headExpansion_at (s : System) {k h u a b}
    (ha : lookupList (s.heads k) h = some a)
    (hb : lookupList (s.heads k) u = some b) :
    headExpansion s ⟨k,s.head k h,s.head k u⟩ = expandNodes a b := by
  simp [headExpansion,System.head,ha,hb]

theorem row_consequence {s : System} {prior : List Comparison} {k x y h}
    (row : x < s.rows k) (pair : ⟨k,x,y⟩ ∈ prior)
    (lower : h ∈ (withClauses s prior).lower k x) :
    ⟨k,s.head k h,y⟩ ∈ demands s prior := by
  apply List.mem_flatMap.mpr
  refine ⟨⟨k,x,y⟩,pair,?_⟩
  simp only [consequences,row,↓reduceIte]
  exact List.mem_map.mpr ⟨h,lower,rfl⟩

theorem head_consequence {s : System} {prior : List Comparison} {k h u children}
    (pair : ⟨k,s.head k h,s.head k u⟩ ∈ prior)
    (expanded : headExpansion s ⟨k,s.head k h,s.head k u⟩ = some children) :
    ∀ p, p ∈ children → p ∈ demands s prior := by
  intro p hp
  apply List.mem_flatMap.mpr
  refine ⟨⟨k,s.head k h,s.head k u⟩,pair,?_⟩
  have lh : ¬ s.head k h < s.rows k := by simp [System.head]
  have uh : ¬ s.head k u < s.rows k := by simp [System.head]
  simpa [consequences,lh,uh,expanded] using hp

/-- The closure proof supplies all propagation fields. The remaining checks
are local shape/bounds/constructor compatibility checks, not Saturated. -/
theorem completed_saturated {s : System}
    (bounded : checkBounds s s.clauses = true)
    (formed : checkFormation s = true)
    (shapes : checkCompatible s (clauses s) = true)
    (children : checkBounds s (demands s (clauses s)) = true) :
    Saturated (completed s) := by
  have good := clauses_correct ((checkBounds_iff _ _).mp bounded)
  have emitted := (checkBounds_iff _ _).mp children
  constructor
  · exact good.1
  · exact (checkFormation_iff s).mp formed
  · intro k x y xr yr pair h lower
    apply lower_mem.mpr
    refine ⟨(lower_mem.mp lower).1,?_⟩
    have needed := row_consequence xr pair lower
    exact good.2 _ (emitted _ needed) needed
  · intro k x u xr pair h lower
    have needed := row_consequence xr pair lower
    exact good.2 _ (emitted _ needed) needed
  · intro k h u a b ha hb pair
    have passes := List.all_eq_true.mp shapes _ pair
    have lh : ¬ s.head k h < s.rows k := by simp [System.head]
    have uh : ¬ s.head k u < s.rows k := by simp [System.head]
    change compatible s ⟨k,s.head k h,s.head k u⟩ = true at passes
    simp only [compatible,lh,uh,or_self,↓reduceIte] at passes
    cases expanded : headExpansion s ⟨k,s.head k h,s.head k u⟩ with
    | none => simp [expanded] at passes
    | some cs =>
        apply (Regular.nodeRel_iff _ _ _).mpr
        apply (Regular.holdsExpansion_iff _ _).mpr
        refine ⟨cs,(headExpansion_at s ha hb).symm.trans expanded,?_⟩
        intro p hp
        have needed := head_consequence pair expanded p hp
        exact good.2 _ (emitted _ needed) needed

inductive Diagnostic where
  | malformedBounds (pairs : List Comparison)
  | malformedHeads (heads : List Reference)
  | incompatibleHeads (pairs : List Comparison)
  | malformedChildren (pairs : List Comparison)
  deriving Repr

def badBounds (s : System) (ps : List Comparison) : List Comparison :=
  ps.filter (fun p => ¬ Bounded s p)

def badHeads (s : System) : List Reference :=
  [Kind.value,Kind.effect].flatMap (fun k =>
    ((List.range (s.heads k).length).filter (fun h =>
      match lookupList (s.heads k) h with
      | some node => !(checkNode s node)
      | none => true)).map (fun h => ⟨k,h⟩))

/-- All failures carry finite offending inputs. No model, certificate or
successful lattice decision is an argument or acceptance test. -/
def solve (s : System) : Except Diagnostic System :=
  if checkBounds s s.clauses then
    if checkFormation s then
      let out := clauses s
      if checkCompatible s out then
        if checkBounds s (demands s out) then .ok (completed s)
        else .error (.malformedChildren (badBounds s (demands s out)))
      else .error (.incompatibleHeads (out.filter (fun p => !(compatible s p))))
    else .error (.malformedHeads (badHeads s))
  else .error (.malformedBounds (badBounds s s.clauses))

theorem solve_success {s out : System} (success : solve s = .ok out) :
    out = completed s ∧ out.rows = s.rows ∧ out.heads = s.heads ∧
      (∀ p, p ∈ s.clauses → p ∈ out.clauses) ∧ Saturated out := by
  unfold solve at success
  split at success
  · rename_i bounded
    split at success
    · rename_i formed
      dsimp only at success
      split at success
      · rename_i shapes
        split at success
        · rename_i children
          cases success
          exact ⟨rfl,rfl,rfl,clauses_retains s,
            completed_saturated bounded formed shapes children⟩
        · cases success
      · cases success
    · cases success
  · cases success

/-- Direct construction for the ORIGINAL clauses, not just added obligations.
The same computed graph and one names map interpret every original endpoint. -/
theorem solve_original_model {s out : System} (success : solve s = .ok out) :
    out.graph.Valid ∧ out.graph.Guarded ∧
      (∀ p, p ∈ s.clauses → Lattice.RegularSub out.graph (renamePair out.names p)) ∧
      LatticeDecision.decideDemands out.graph (s.clauses.map (renamePair out.names)) = true := by
  have result := solve_success success
  have bounds := fun p hp => canonical_bounds result.2.2.2.2 p (result.2.2.2.1 p hp)
  refine ⟨canonical_valid result.2.2.2.2,canonical_guarded out,bounds,?_⟩
  apply (LatticeDecision.decideDemands_exact _ _).mpr
  refine ⟨canonical_valid result.2.2.2.2,canonical_guard_checked out,?_⟩
  intro p hp
  rcases List.mem_map.mp hp with ⟨old,member,rfl⟩
  exact bounds old member

open LatticeInference

theorem solve_original_store {s out : System} (success : solve s = .ok out)
    {store : Store}
    (decoded : decodeStore out.graph out.names store =
      some (s.clauses.map (renamePair out.names))) :
    StoreSatisfied out.graph out.names store := by
  apply decoded_store_satisfied decoded
  intro p hp
  rcases List.mem_map.mp hp with ⟨old,member,rfl⟩
  exact (solve_original_model success).2.2.1 old member

theorem solve_original_history {s out : System} (success : solve s = .ok out)
    {ref birth first events}
    (history : ConstraintHistory out.graph ref birth first
      ⟨s.clauses.map (renamePair out.names),events⟩) :
    out.graph.Valid ∧ out.graph.Guarded ∧ Holds out.graph first.obligations :=
  accepted_original_demands history (solve_original_model success).2.2.2

/-- Every generated comparison is mandatory in every syntactically saturated
extension with the same tables. This is syntactic minimality, not completeness
for an enlarged record-adaptation or lattice satisfiability semantics. -/
theorem demands_in_extension {s : System} {prior target : List Comparison}
    (sat : Saturated (withClauses s target))
    (included : ∀ p, p ∈ prior → p ∈ target) :
    ∀ p, p ∈ demands s prior → p ∈ target := by
  intro p hp
  rcases List.mem_flatMap.mp hp with ⟨⟨k,x,y⟩,pair,hp⟩
  have retained := included _ pair
  simp only [consequences] at hp
  split at hp
  · rename_i xr
    rcases List.mem_map.mp hp with ⟨h,lower,rfl⟩
    have old : h ∈ (withClauses s target).lower k x := by
      obtain ⟨bound,member⟩ := lower_mem.mp lower
      exact lower_mem.mpr ⟨bound,included _ member⟩
    by_cases yr : y < s.rows k
    · exact (lower_mem.mp (sat.rowRow k x y xr yr retained h old)).2
    · have hy : y = s.head k (y - s.rows k) := by simp [System.head]; omega
      rw [hy]
      exact sat.rowHead k x _ xr (hy ▸ retained) h old
  · rename_i xr
    split at hp
    · cases hp
    · rename_i yr
      have hx : x = s.head k (x - s.rows k) := by simp [System.head]; omega
      have hy : y = s.head k (y - s.rows k) := by simp [System.head]; omega
      cases ha : lookupList (s.heads k) (x - s.rows k) with
      | none => simp [headExpansion,ha] at hp
      | some a =>
          cases hb : lookupList (s.heads k) (y - s.rows k) with
          | none => simp [headExpansion,ha,hb] at hp
          | some b =>
              have rel := sat.headHead k (x - s.rows k) (y - s.rows k) a b ha hb
                (hx ▸ hy ▸ retained)
              rcases (Regular.holdsExpansion_iff _ _).mp
                ((Regular.nodeRel_iff _ _ _).mp rel) with ⟨cs,exp,closed⟩
              apply closed p
              simpa [headExpansion,ha,hb,exp] using hp

theorem close_least {s : System} {target : List Comparison}
    (sat : Saturated (withClauses s target)) (fuel : Nat)
    (pending prior : List Comparison)
    (included : ∀ p, p ∈ prior → p ∈ target) :
    ∀ p, p ∈ close s fuel pending prior → p ∈ target := by
  induction fuel generalizing pending prior with
  | zero => exact included
  | succ fuel ih =>
      simp only [close]
      split
      · exact included
      · apply ih
        intro p hp
        rcases List.mem_append.mp hp with old | added
        · exact included p old
        · exact demands_in_extension sat included p
            (of_decide_eq_true (List.mem_filter.mp added).2)

theorem clauses_least {s : System} {target : List Comparison}
    (sat : Saturated (withClauses s target))
    (included : ∀ p, p ∈ s.clauses → p ∈ target) :
    ∀ p, p ∈ clauses s → p ∈ target := close_least sat _ _ _ included

theorem compatible_of_saturated {s : System} {target : List Comparison}
    (sat : Saturated (withClauses s target)) {p : Comparison} (member : p ∈ target) :
    compatible s p = true := by
  rcases p with ⟨k,x,y⟩
  by_cases row : x < s.rows k ∨ y < s.rows k
  · simp [compatible,row]
  · have bounds := sat.bounded ⟨k,x,y⟩ member
    change x < s.rows k + (s.heads k).length ∧
      y < s.rows k + (s.heads k).length at bounds
    have hx : x = s.head k (x - s.rows k) := by simp [System.head]; omega
    have hy : y = s.head k (y - s.rows k) := by simp [System.head]; omega
    rcases Lattice.lookupList_present (s.heads k) (x - s.rows k) (by omega) with ⟨a,ha⟩
    rcases Lattice.lookupList_present (s.heads k) (y - s.rows k) (by omega) with ⟨b,hb⟩
    have rel := sat.headHead k (x - s.rows k) (y - s.rows k) a b ha hb
      (hx ▸ hy ▸ member)
    rcases (Regular.holdsExpansion_iff _ _).mp
      ((Regular.nodeRel_iff _ _ _).mp rel) with ⟨cs,expanded,_⟩
    simp [compatible,row,headExpansion,ha,hb,expanded]

/-- Completeness for the exact finite syntactic closure problem. Existence of
an extension is used only in this converse theorem, never by solve or its
soundness proof. It is not completeness for arbitrary semantic models. -/
theorem solve_complete {s : System} {target : List Comparison}
    (sat : Saturated (withClauses s target))
    (included : ∀ p, p ∈ s.clauses → p ∈ target) :
    solve s = .ok (completed s) := by
  have all := clauses_least sat included
  have bounded : checkBounds s s.clauses = true :=
    (checkBounds_iff _ _).mpr (fun p hp => sat.bounded p (included p hp))
  have formed : checkFormation s = true := (checkFormation_iff _).mpr sat.formed
  have shapes : checkCompatible s (clauses s) = true :=
    List.all_eq_true.mpr (fun p hp => compatible_of_saturated sat (all p hp))
  have childBounds : checkBounds s (demands s (clauses s)) = true :=
    (checkBounds_iff _ _).mpr (fun p hp =>
      sat.bounded p (demands_in_extension sat all p hp))
  simp [solve,bounded,formed,shapes,childBounds]

theorem solve_exists_iff (s : System) :
    (∃ out, solve s = .ok out) ↔ ∃ target : List Comparison,
      (∀ p, p ∈ s.clauses → p ∈ target) ∧ Saturated (withClauses s target) := by
  constructor
  · rintro ⟨out,success⟩
    rcases solve_success success with ⟨rfl,_,_,keep,sat⟩
    exact ⟨clauses s,keep,sat⟩
  · rintro ⟨target,included,sat⟩
    exact ⟨completed s,solve_complete sat included⟩

def recursiveInput : System := withClauses recursiveSystem
  [⟨.value,1,0⟩,⟨.value,0,1⟩,⟨.effect,1,0⟩,⟨.effect,0,1⟩]

def recursiveInputStore : Store :=
  [⟨.value,recursiveFunction,.var 0⟩,⟨.value,.var 0,recursiveFunction⟩,
   ⟨.effect,.atom 7,.var 0⟩,⟨.effect,.var 0,.atom 7⟩]

theorem recursive_solved : solve recursiveInput = .ok (completed recursiveInput) := rfl

theorem recursive_input_decoded :
    decodeStore (completed recursiveInput).graph (completed recursiveInput).names
      recursiveInputStore = some
        (recursiveInput.clauses.map (renamePair (completed recursiveInput).names)) := rfl

theorem recursive_original_store_constructed :
    (completed recursiveInput).graph.Valid ∧ (completed recursiveInput).graph.Guarded ∧
      StoreSatisfied (completed recursiveInput).graph (completed recursiveInput).names
        recursiveInputStore :=
  ⟨(solve_original_model recursive_solved).1,
    (solve_original_model recursive_solved).2.1,
    solve_original_store recursive_solved recursive_input_decoded⟩

theorem recursive_original_decided :
    LatticeDecision.decideDemands (completed recursiveInput).graph
      (recursiveInput.clauses.map (renamePair (completed recursiveInput).names)) = true :=
  (solve_original_model recursive_solved).2.2.2

theorem alias_solved : solve aliasSystem = .ok (completed aliasSystem) := rfl

theorem alias_cycle_computed :
    (completed aliasSystem).graph.lookup .value ((completed aliasSystem).names .value 0) =
      some (.structural .bottom) ∧
    (completed aliasSystem).graph.lookup .value ((completed aliasSystem).names .value 1) =
      some (.structural .bottom) ∧
    LatticeDecision.decideDemands (completed aliasSystem).graph
      (aliasSystem.clauses.map (renamePair (completed aliasSystem).names)) = true :=
  ⟨rfl,rfl,(solve_original_model alias_solved).2.2.2⟩

def incompatibleInput : System where
  rows := fun _ => 0
  heads := fun k => match k with
    | .value => [.atom 0,.atom 1]
    | .effect => []
  clauses := [⟨.value,0,1⟩]

theorem incompatible_atoms_rejected :
    solve incompatibleInput = .error (.incompatibleHeads [⟨.value,0,1⟩]) := rfl

def malformedInput : System := withClauses aliasSystem [⟨.value,0,2⟩]

theorem malformed_bound_rejected :
    solve malformedInput = .error (.malformedBounds [⟨.value,0,2⟩]) := rfl

def duplicateLabelsInput : System where
  rows := fun _ => 0
  heads := fun k => match k with
    | .value => [.record [⟨4,false,0⟩,⟨4,true,0⟩]]
    | .effect => []
  clauses := []

theorem duplicate_labels_rejected :
    solve duplicateLabelsInput = .error (.malformedHeads [⟨.value,0⟩]) := rfl

theorem function_signed_children (a ae re r b be se t : Nat) :
    expandNodes (.function a ae re r) (.function b be se t) =
      some [⟨.value,b,a⟩,⟨.effect,be,ae⟩,⟨.effect,re,se⟩,⟨.value,r,t⟩] := rfl

theorem optional_metadata_not_erased :
    expandNodes (.record [⟨4,false,0⟩]) (.record [⟨4,true,0⟩]) = none := rfl

theorem tuple_arity_not_erased :
    expandNodes (.tuple [0,1]) (.tuple [0]) = none := rfl

theorem variant_payload_arity_not_erased :
    expandNodes (.variant [⟨4,[0,1]⟩]) (.variant [⟨4,[0]⟩]) = none := rfl

end YulangClosure.SimpleSub.NativeRowSaturation
