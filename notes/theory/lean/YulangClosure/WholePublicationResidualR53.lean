import YulangClosure.PerCallResidualPublicationR52

/-!
R53 whole-publication construction on the retained canonical terminal domain.
The recursive assembler consumes exactly one record per Forward and none per
Suppress. Primitive owner/source reads remain explicit; no Rust extraction,
source soundness, A/B or production authority is asserted.
-/
namespace YulangClosure.WholePublicationResidualR53

open CurrentEmissionOwnershipR47 (Endpoint currentBound)
open NativeResidualPublicationR51
open PerCallResidualPublicationR52 (Captured Store Installed CallSource DrainSource ModeSource project Window)

variable {Artifact Id Term Fact : Type}

instance [DecidableEq Id] [DecidableEq Fact] (q : Query Artifact Id Term Fact)
    (index : Nat) (endpoint : Endpoint Id) (r : Captured Id Fact) :
    Decidable (CallSource q index endpoint r) := by unfold CallSource; infer_instance

def suppressedItem (index : Nat) (endpoint : Endpoint Id) : Item Id Fact :=
  ⟨index, endpoint, .suppress, .suppressed⟩
def forwardItem (index : Nat) (endpoint : Endpoint Id) (r : Captured Id Fact) : Item Id Fact :=
  ⟨index, endpoint, .forward, .forwarded r.probe⟩

/-- This executable constructor rejects missing, extra, reordered, foreign
publication/index/endpoint/fact/occurrence/cause/upper call records. -/
def assemble [DecidableEq Id] [DecidableEq Fact] (q : Query Artifact Id Term Fact) :
    Nat → List (Endpoint Id × AuthenticatedResidualConsumerR49.Decision) →
      List (Captured Id Fact) → Option (List (Item Id Fact))
  | _, [], [] => some []
  | _, [], _ :: _ => none
  | index, (endpoint, .suppress) :: rest, calls =>
      (assemble q (index + 1) rest calls).map (suppressedItem index endpoint :: ·)
  | _, (_, .forward) :: _, [] => none
  | index, (endpoint, .forward) :: rest, r :: calls =>
      if CallSource q index endpoint r then
        (assemble q (index + 1) rest calls).map (forwardItem index endpoint r :: ·)
      else none

/-- Derived from successful construction, never an assumed correspondence. -/
inductive Aligned (q : Query Artifact Id Term Fact) : Nat →
    List (Endpoint Id × AuthenticatedResidualConsumerR49.Decision) →
      List (Captured Id Fact) → List (Item Id Fact) → Prop
  | nil (index) : Aligned q index [] [] []
  | suppress (index endpoint rest calls items)
      (tail : Aligned q (index + 1) rest calls items) :
      Aligned q index ((endpoint, .suppress) :: rest) calls (suppressedItem index endpoint :: items)
  | forward (index endpoint rest r calls items) (source : CallSource q index endpoint r)
      (tail : Aligned q (index + 1) rest calls items) :
      Aligned q index ((endpoint, .forward) :: rest) (r :: calls) (forwardItem index endpoint r :: items)

theorem assemble_sound [DecidableEq Id] [DecidableEq Fact]
    (q : Query Artifact Id Term Fact) (index : Nat) (plan : List (Endpoint Id × AuthenticatedResidualConsumerR49.Decision))
    (calls : List (Captured Id Fact)) (items : List (Item Id Fact))
    (built : assemble q index plan calls = some items) : Aligned q index plan calls items := by
  induction plan generalizing index calls items with
  | nil =>
    cases calls with
    | nil => simp [assemble] at built; subst items; exact .nil index
    | cons r calls => simp [assemble] at built
  | cons entry rest ih =>
    rcases entry with ⟨endpoint, decision⟩
    cases decision with
    | suppress =>
      cases h : assemble q (index + 1) rest calls with
      | none => simp [assemble, h] at built
      | some tail =>
        simp only [assemble, h, Option.map_some, Option.some.injEq] at built
        subst items
        exact .suppress index endpoint rest calls tail (ih _ _ _ h)
    | forward =>
      cases calls with
      | nil => simp [assemble] at built
      | cons r calls =>
        by_cases source : CallSource q index endpoint r
        · cases h : assemble q (index + 1) rest calls with
          | none => simp [assemble, source, h] at built
          | some tail =>
            simp [assemble, source, h] at built
            subst items
            exact .forward index endpoint rest r calls tail source (ih _ _ _ h)
        · simp [assemble, source] at built

def rowPart (r : Captured Id Fact) : Option Id :=
  match r.probe.mode, r.probe.bound.item with
  | .newlyEmitted, .effectRow row => some row
  | _, _ => none

def atomPart (r : Captured Id Fact) : Option Id :=
  match r.probe.mode, r.probe.bound.item with
  | .newlyEmitted, .effectAtom atom => some atom
  | _, _ => none

def callKeys (calls : List (Captured Id Fact)) : List (Nat × Nat) :=
  calls.map (fun r => (r.probe.call.publication, r.probe.call.planIndex))
def itemCallKeys (items : List (Item Id Fact)) : List (Nat × Nat) :=
  items.filterMap fun item => match item.decision, item.probe with
  | .forward, .forwarded p => some (p.call.publication, p.call.planIndex)
  | _, _ => none

theorem aligned_projections (q : Query Artifact Id Term Fact) (index : Nat) (plan calls items)
    (aligned : Aligned q index plan calls items) :
    itemPlan items = plan ∧ items.map Item.index = List.range' index plan.length ∧
    itemCallKeys items = callKeys calls ∧
    plannedRows items = calls.filterMap rowPart ∧ plannedAtoms items = calls.filterMap atomPart := by
  induction aligned with
  | nil index => simp [itemPlan, itemCallKeys, callKeys, plannedRows, plannedAtoms]
  | suppress index endpoint rest calls items tail ih =>
    rcases ih with ⟨plan, indices, keys, rows, atoms⟩
    exact ⟨by simpa [itemPlan, suppressedItem] using congrArg (List.cons (endpoint, AuthenticatedResidualConsumerR49.Decision.suppress)) plan,
      by simpa [suppressedItem, List.range'_succ] using congrArg (List.cons index) indices,
      by simpa [itemCallKeys, suppressedItem] using keys,
      by simpa [plannedRows, suppressedItem] using rows,
      by simpa [plannedAtoms, suppressedItem] using atoms⟩
  | forward index endpoint rest r calls items source tail ih =>
    rcases ih with ⟨plan, indices, keys, rows, atoms⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [itemPlan, forwardItem] using congrArg (List.cons (endpoint, AuthenticatedResidualConsumerR49.Decision.forward)) plan
    · simpa [forwardItem, List.range'_succ] using congrArg (List.cons index) indices
    · simpa [itemCallKeys, callKeys, forwardItem] using congrArg (List.cons (r.probe.call.publication, r.probe.call.planIndex)) keys
    · change (match rowPart r with | none => plannedRows items | some row => row :: plannedRows items) =
        (match rowPart r with | none => calls.filterMap rowPart | some row => row :: calls.filterMap rowPart)
      rw [rows]
    · change (match atomPart r with | none => plannedAtoms items | some atom => atom :: plannedAtoms items) =
        (match atomPart r with | none => calls.filterMap atomPart | some atom => atom :: calls.filterMap atomPart)
      rw [atoms]

theorem aligned_lower (q : Query Artifact Id Term Fact) (index : Nat) (plan calls items)
    (aligned : Aligned q index plan calls items) :
    (∀ r ∈ calls, index ≤ r.probe.call.planIndex) ∧ (∀ item ∈ items, index ≤ item.index) := by
  induction aligned with
  | nil index =>
    constructor
    · intro r member; cases member
    · intro item member; cases member
  | suppress index endpoint rest calls items tail ih =>
    refine ⟨fun r member => Nat.le_trans (Nat.le_succ index) (ih.1 r member), ?_⟩
    intro item member
    rcases List.mem_cons.mp member with rfl | later
    · exact Nat.le_refl _
    · exact Nat.le_trans (Nat.le_succ index) (ih.2 item later)
  | forward index endpoint rest r calls items source tail ih =>
    constructor
    · intro candidate member
      rcases List.mem_cons.mp member with rfl | later
      · rw [source.2.1]; exact Nat.le_refl _
      · exact Nat.le_trans (Nat.le_succ index) (ih.1 candidate later)
    · intro item member
      rcases List.mem_cons.mp member with rfl | later
      · exact Nat.le_refl _
      · exact Nat.le_trans (Nat.le_succ index) (ih.2 item later)

theorem suppress_has_no_call (q : Query Artifact Id Term Fact) (index : Nat) (plan calls items)
    (aligned : Aligned q index plan calls items) (item : Item Id Fact) (member : item ∈ items)
    (suppressed : item.decision = .suppress) : ∀ r ∈ calls, r.probe.call.planIndex ≠ item.index := by
  induction aligned generalizing item with
  | nil index => cases member
  | suppress index endpoint rest calls items tail ih =>
    rcases List.mem_cons.mp member with rfl | later
    · intro r rMember
      exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self index) ((aligned_lower q _ _ _ _ tail).1 r rMember))
    · exact ih item later suppressed
  | forward index endpoint rest head calls items source tail ih =>
    rcases List.mem_cons.mp member with rfl | later
    · cases suppressed
    · intro r rMember
      rcases List.mem_cons.mp rMember with rfl | tailMember
      · rw [source.2.1]
        exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self index) ((aligned_lower q _ _ _ _ tail).2 item later))
      · exact ih item later suppressed r tailMember

theorem forward_has_original_call (q : Query Artifact Id Term Fact) (index : Nat) (plan calls items)
    (aligned : Aligned q index plan calls items) (item : Item Id Fact) (member : item ∈ items)
    (forwarded : item.decision = .forward) :
    ∃ r ∈ calls, item.probe = .forwarded r.probe ∧ CallSource q item.index item.endpoint r := by
  induction aligned generalizing item with
  | nil index => cases member
  | suppress index endpoint rest calls items tail ih =>
    rcases List.mem_cons.mp member with rfl | later
    · cases forwarded
    · exact ih item later forwarded
  | forward index endpoint rest r calls items call tail ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨r, List.mem_cons_self, rfl, call⟩
    · obtain ⟨record, recordMember, probe, source⟩ := ih item later forwarded
      exact ⟨record, List.mem_cons_of_mem _ recordMember, probe, source⟩

/-- Conversely every retained Forward record is consumed at its original
plan position. Together with ordered keys and contiguous item indices this
is the finite Forward/call bijection, including suppressed plan positions. -/
theorem call_has_original_forward (q : Query Artifact Id Term Fact) (index : Nat) (plan calls items)
    (aligned : Aligned q index plan calls items) (r : Captured Id Fact) (member : r ∈ calls) :
    ∃ item ∈ items, item.decision = .forward ∧ item.probe = .forwarded r.probe ∧
      CallSource q item.index item.endpoint r := by
  induction aligned with
  | nil index => cases member
  | suppress index endpoint rest calls items tail ih =>
    obtain ⟨item, itemMember, decision, probe, source⟩ := ih member
    exact ⟨item, List.mem_cons_of_mem _ itemMember, decision, probe, source⟩
  | forward index endpoint rest head calls items call tail ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨forwardItem index endpoint r, List.mem_cons_self, rfl, rfl, call⟩
    · obtain ⟨item, itemMember, decision, probe, source⟩ := ih later
      exact ⟨item, List.mem_cons_of_mem _ itemMember, decision, probe, source⟩

/-- A raw retained-owner projection, not an assumed ItemReads result. -/
def keyLookup (publication index : Nat) : List (Captured Id Fact) → Option (Captured Id Fact)
  | [] => none
  | r :: rest => if r.probe.call.publication = publication ∧ r.probe.call.planIndex = index then some r
      else keyLookup publication index rest

theorem keyLookup_absent (publication index : Nat) (calls : List (Captured Id Fact))
    (absent : ∀ r ∈ calls, r.probe.call.planIndex ≠ index) : keyLookup publication index calls = none := by
  induction calls with
  | nil => rfl
  | cons r rest ih =>
    have different := absent r (List.mem_cons_self)
    have tail := ih (fun r member => absent r (List.mem_cons_of_mem _ member))
    simp [keyLookup, different, tail]

def NativeSource [DecidableEq Id] (base : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact)
    (r : Captured Id Fact) : Prop :=
  base.boundCandidates q.frame.row r.probe.call.endpoint = [r.probe.slot] ∧
  currentBound base.after.current r.probe.slot = some r.probe.bound ∧
  r.probe.bound.owner = .effect q.frame.row ∧ r.probe.slot.owner = .effect q.frame.row ∧
  r.probe.bound.item = r.probe.call.endpoint ∧ r.probe.bound.polarity = .positive ∧
  (r.probe.slot.lane = .effectLowerRow ∨ r.probe.slot.lane = .effectLowerAtom)

def withItems (q : Query Artifact Id Term Fact) (items : List (Item Id Fact)) : Query Artifact Id Term Fact :=
  { q with
    items := items
    frame := { q.frame with rowsSuffix := plannedRows items, atomsSuffix := plannedAtoms items } }

theorem aligned_item_reads [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Fact]
    (base : Inputs Artifact Id Fact) (s : Store Id Fact) (q : Query Artifact Id Term Fact)
    (allItems : List (Item Id Fact)) (index : Nat) (plan calls items)
    (aligned : Aligned q index plan calls items)
    (sources : ∀ r ∈ calls, Installed s r ∧ DrainSource base r ∧ ModeSource base q r ∧ NativeSource base q r)
    (absent : ∀ item ∈ items, item.decision = .suppress → s.keyed q.publication item.index = none) :
    ∀ item ∈ items, ItemReads (project base s) (withItems q allItems) item := by
  induction aligned with
  | nil index => intro item member; cases member
  | suppress index endpoint rest calls items tail ih =>
    intro item member
    rcases List.mem_cons.mp member with rfl | later
    · simp only [ItemReads, suppressedItem]
      have missing : s.keyed q.publication index = none := absent _ (List.mem_cons_self) rfl
      simp [project, withItems, missing]
    · exact ih sources (fun item member => absent item (List.mem_cons_of_mem _ member)) item later
  | forward index endpoint rest r calls items call tail ih =>
    intro item member
    rcases List.mem_cons.mp member with rfl | later
    · obtain ⟨installed, drain, mode, native⟩ := sources r (List.mem_cons_self)
      have native' : NativeSource base q r := native
      unfold NativeSource at native'
      rw [call.2.2.1] at native'
      have checked := PerCallResidualPublicationR52.captured_forward_native base s (withItems q allItems)
        index endpoint r installed call drain mode native'
      exact checked.1
    · exact ih (fun r member => sources r (List.mem_cons_of_mem _ member))
        (fun item member => absent item (List.mem_cons_of_mem _ member)) item later

/-- Explicit native owner projections and finite take/drop comparisons. The
frame equality is derived using take_append_drop, not assumed as a result. -/
def OwnerReads [DecidableEq Id] (base : Inputs Artifact Id Fact) (q : Query Artifact Id Term Fact)
    (calls : List (Captured Id Fact)) : Prop :=
  base.resultOwner q.originalFact.upper = some q.frame.row ∧
  base.initialRows q.frame.row = some q.frame.before ∧
  base.after.current.effectRows q.frame.row = some q.frame.after ∧
  q.frame.after.lowerRows.take q.frame.before.lowerRows.length = q.frame.before.lowerRows ∧
  q.frame.after.lowerAtoms.take q.frame.before.lowerAtoms.length = q.frame.before.lowerAtoms ∧
  q.frame.after.lowerRows.drop q.frame.before.lowerRows.length = calls.filterMap rowPart ∧
  q.frame.after.lowerAtoms.drop q.frame.before.lowerAtoms.length = calls.filterMap atomPart

theorem owner_frame [DecidableEq Id] (base : Inputs Artifact Id Fact) (s : Store Id Fact)
    (q : Query Artifact Id Term Fact) (index : Nat) (plan calls items)
    (aligned : Aligned q index plan calls items) (owner : OwnerReads base q calls) :
    FrameReads (project base s) (withItems q items) := by
  rcases owner with ⟨result, initial, final, rowPrefix, atomPrefix, rowSuffix, atomSuffix⟩
  have projections := aligned_projections q index plan calls items aligned
  have rows := (List.take_append_drop q.frame.before.lowerRows.length q.frame.after.lowerRows).symm
  have atoms := (List.take_append_drop q.frame.before.lowerAtoms.length q.frame.after.lowerAtoms).symm
  rw [rowPrefix, rowSuffix, ← projections.2.2.2.1] at rows
  rw [atomPrefix, atomSuffix, ← projections.2.2.2.2] at atoms
  exact ⟨result, initial, final, rows, atoms, rfl, rfl⟩

/-- Complete R50 plan + actual assembly + primitive owner/per-call reads
construct R51 observe for the SAME context, identity, source fact and records. -/
theorem whole_publication_observed [DecidableEq Artifact] [DecidableEq Id]
    [DecidableEq Term] [DecidableEq Fact]
    (base : Inputs Artifact Id Fact) (s : Store Id Fact) (q : Query Artifact Id Term Fact)
    (plan : List (Endpoint Id × AuthenticatedResidualConsumerR49.Decision))
    (calls : List (Captured Id Fact)) (items : List (Item Id Fact))
    (acceptedPlan : AuthenticatedResidualConsumerR49.plan q.context q.original = some plan)
    (built : assemble q 0 plan calls = some items)
    (inventory : ∀ index, s.keyed q.publication index = keyLookup q.publication index calls)
    (sources : ∀ r ∈ calls, Installed s r ∧ DrainSource base r ∧ ModeSource base q r ∧ NativeSource base q r)
    (artifact : base.after.current.artifact = q.context.inputs.arrival.current.artifact)
    (fact : FactReads base q) (owner : OwnerReads base q calls) :
    observe (project base s) (withItems q items) = true := by
  have aligned := assemble_sound q 0 plan calls items built
  have projections := aligned_projections q 0 plan calls items aligned
  have lengths : items.length = plan.length := by
    have h := congrArg List.length projections.1
    simpa only [itemPlan, List.length_map] using h
  have absent : ∀ item ∈ items, item.decision = .suppress → s.keyed q.publication item.index = none := by
    intro item member suppressed
    rw [inventory]
    exact keyLookup_absent _ _ _ (suppress_has_no_call q 0 plan calls items aligned item member suppressed)
  have checked := aligned_item_reads base s q items 0 plan calls items aligned sources absent
  change decide (Reads (project base s) (withItems q items)) = true
  apply decide_eq_true
  refine ⟨?_, ?_, artifact, fact, owner_frame base s q 0 plan calls items aligned owner, ?_⟩
  · simpa only [withItems, projections.1] using acceptedPlan
  · change items.map Item.index = List.range items.length
    rw [projections.2.1, lengths, List.range_eq_range']
  · apply List.all_eq_true.mpr
    intro item member
    exact decide_eq_true (checked item member)

/-- Cuts are all reads of the same base state's append-only owner vectors. -/
def CutShape (r : Captured Id Fact) : Prop :=
  r.probe.call.originCut ≤ r.originEnd ∧ r.completionCut ≤ r.completionEnd ∧
  r.probe.call.emissionCut ≤ r.emissionEnd

def CutOrder (a b : Captured Id Fact) : Prop :=
  a.originEnd ≤ b.probe.call.originCut ∧ a.completionEnd ≤ b.completionCut ∧
  a.emissionEnd ≤ b.probe.call.emissionCut

def Chronological (calls : List (Captured Id Fact)) : Prop :=
  calls.Pairwise CutOrder ∧ ∀ r ∈ calls, CutShape r

instance (r : Captured Id Fact) : Decidable (CutShape r) := by unfold CutShape; infer_instance
instance (a b : Captured Id Fact) : Decidable (CutOrder a b) := by unfold CutOrder; infer_instance
instance (calls : List (Captured Id Fact)) : Decidable (Chronological calls) := by
  unfold Chronological; infer_instance

theorem cut_order_trans (a b c : Captured Id Fact) (ab : CutOrder a b) (shape : CutShape b)
    (bc : CutOrder b c) : CutOrder a c :=
  ⟨Nat.le_trans ab.1 (Nat.le_trans shape.1 bc.1),
    Nat.le_trans ab.2.1 (Nat.le_trans shape.2.1 bc.2.1),
    Nat.le_trans ab.2.2 (Nat.le_trans shape.2.2 bc.2.2)⟩

def CutChain : List (Captured Id Fact) → Prop
  | [] => True
  | [r] => CutShape r
  | a :: b :: rest => CutShape a ∧ CutOrder a b ∧ CutChain (b :: rest)

theorem adjacent_cuts_compose : ∀ calls : List (Captured Id Fact), CutChain calls → Chronological calls
  | [], _ => ⟨.nil, fun _ member => by cases member⟩
  | [r], shape => ⟨.cons (fun _ member => by cases member) .nil,
      fun candidate member => by rcases List.mem_singleton.mp member with rfl; exact shape⟩
  | a :: b :: rest, chain => by
      obtain ⟨shape, ab, tail⟩ := chain
      have ih := adjacent_cuts_compose (b :: rest) tail
      constructor
      · apply List.Pairwise.cons
        · intro c member
          rcases List.mem_cons.mp member with rfl | later
          · exact ab
          · exact cut_order_trans a b c ab (ih.2 b (List.mem_cons_self))
              ((List.pairwise_cons.mp ih.1).1 c later)
        · exact ih.1
      · intro r member
        rcases List.mem_cons.mp member with rfl | later
        · exact shape
        · exact ih.2 r later

theorem same_state_receipts_separate (base : Inputs Artifact Id Fact) (a b : Captured Id Fact)
    (aSource : DrainSource base a) (bSource : DrainSource base b) (ordered : CutOrder a b) :
    a.probe.receipt.originIndex ≠ b.probe.receipt.originIndex ∧ a.completionIndex ≠ b.completionIndex :=
  ⟨PerCallResidualPublicationR52.origin_separation base a b aSource bSource ordered.1,
    PerCallResidualPublicationR52.completion_separation base a b aSource bSource ordered.2.1⟩

/-- Additional whole observer check: numeric cut order plus the derived R51
view. Observation absence is still a Bool, not an inference failure. -/
def wholeObserve [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Term] [DecidableEq Fact]
    (base : Inputs Artifact Id Fact) (s : Store Id Fact) (q : Query Artifact Id Term Fact)
    (plan : List (Endpoint Id × AuthenticatedResidualConsumerR49.Decision))
    (calls : List (Captured Id Fact)) : Bool :=
  match assemble q 0 plan calls with
  | none => false
  | some items => decide (Chronological calls) && observe (project base s) (withItems q items)

theorem whole_observer_components [DecidableEq Artifact] [DecidableEq Id]
    [DecidableEq Term] [DecidableEq Fact]
    (base : Inputs Artifact Id Fact) (s : Store Id Fact) (q : Query Artifact Id Term Fact)
    (plan : List (Endpoint Id × AuthenticatedResidualConsumerR49.Decision)) (calls : List (Captured Id Fact))
    (accepted : wholeObserve base s q plan calls = true) :
    ∃ items, assemble q 0 plan calls = some items ∧ Chronological calls ∧
      observe (project base s) (withItems q items) = true := by
  cases built : assemble q 0 plan calls with
  | none => simp [wholeObserve, built] at accepted
  | some items =>
    have both : decide (Chronological calls) = true ∧ observe (project base s) (withItems q items) = true := by
      simpa only [wholeObserve, built, Bool.and_eq_true] using accepted
    exact ⟨items, rfl, of_decide_eq_true both.1, both.2⟩

theorem source_whole_observed [DecidableEq Artifact] [DecidableEq Id]
    [DecidableEq Term] [DecidableEq Fact]
    (base : Inputs Artifact Id Fact) (s : Store Id Fact) (q : Query Artifact Id Term Fact)
    (plan : List (Endpoint Id × AuthenticatedResidualConsumerR49.Decision))
    (calls : List (Captured Id Fact)) (items : List (Item Id Fact))
    (acceptedPlan : AuthenticatedResidualConsumerR49.plan q.context q.original = some plan)
    (built : assemble q 0 plan calls = some items)
    (inventory : ∀ index, s.keyed q.publication index = keyLookup q.publication index calls)
    (sources : ∀ r ∈ calls, Installed s r ∧ DrainSource base r ∧ ModeSource base q r ∧ NativeSource base q r)
    (artifact : base.after.current.artifact = q.context.inputs.arrival.current.artifact)
    (fact : FactReads base q) (owner : OwnerReads base q calls) (chain : CutChain calls) :
    wholeObserve base s q plan calls = true := by
  have observed := whole_publication_observed base s q plan calls items acceptedPlan built inventory sources artifact fact owner
  have chrono := adjacent_cuts_compose calls chain
  simp only [wholeObserve, built, observed, decide_eq_true chrono, Bool.true_and]

/-- Applying the whole construction back to R51 gives the exact native frame
in ORIGINAL Forward-call order; AlreadyPresent contributes no suffix item. -/
theorem whole_exact_native_frame [DecidableEq Artifact] [DecidableEq Id]
    [DecidableEq Term] [DecidableEq Fact]
    (base : Inputs Artifact Id Fact) (s : Store Id Fact) (q : Query Artifact Id Term Fact)
    (plan : List (Endpoint Id × AuthenticatedResidualConsumerR49.Decision)) (calls : List (Captured Id Fact))
    (accepted : wholeObserve base s q plan calls = true) :
    base.initialRows q.frame.row = some q.frame.before ∧
    base.after.current.effectRows q.frame.row = some q.frame.after ∧
    q.frame.after.lowerRows = q.frame.before.lowerRows ++ calls.filterMap rowPart ∧
    q.frame.after.lowerAtoms = q.frame.before.lowerAtoms ++ calls.filterMap atomPart := by
  obtain ⟨items, built, _, observed⟩ := whole_observer_components base s q plan calls accepted
  have projections := aligned_projections q 0 plan calls items (assemble_sound q 0 plan calls items built)
  have frame := accepted_exact_native_frame (project base s) (withItems q items) observed
  simpa only [project, withItems, projections.2.2.2.1, projections.2.2.2.2] using frame

/-- Exact old-prefix membership follows without deleting a pre-existing target
or same-family sibling merely because its plan decision was Suppress. -/
theorem whole_preserves_existing_atom [DecidableEq Artifact] [DecidableEq Id]
    [DecidableEq Term] [DecidableEq Fact]
    (base : Inputs Artifact Id Fact) (s : Store Id Fact) (q : Query Artifact Id Term Fact)
    (plan : List (Endpoint Id × AuthenticatedResidualConsumerR49.Decision)) (calls : List (Captured Id Fact))
    (accepted : wholeObserve base s q plan calls = true) (atom : Id)
    (old : atom ∈ q.frame.before.lowerAtoms) : atom ∈ q.frame.after.lowerAtoms := by
  rw [(whole_exact_native_frame base s q plan calls accepted).2.2.2]
  exact List.mem_append_left _ old

def witnessCalls : List (Captured Nat Nat) :=
  [PerCallResidualPublicationR52.witnessNew, PerCallResidualPublicationR52.witnessOld]
def witnessPlan : List (Endpoint Nat × AuthenticatedResidualConsumerR49.Decision) :=
  [(.effectAtom 7, .forward), (.effectAtom 8, .forward)]

theorem concrete_assembly :
    assemble witnessQuery 0 witnessPlan witnessCalls = some witnessQuery.items := rfl

theorem concrete_owner_reads : OwnerReads witnessInputs witnessQuery witnessCalls := by
  unfold OwnerReads; decide

theorem concrete_sources : ∀ r ∈ witnessCalls,
    Installed PerCallResidualPublicationR52.witnessStore r ∧ DrainSource witnessInputs r ∧
      ModeSource witnessInputs witnessQuery r ∧ NativeSource witnessInputs witnessQuery r := by
  intro r member
  rcases List.mem_cons.mp member with rfl | rest
  · refine ⟨⟨rfl, rfl⟩, ?_, ?_, ?_⟩
    · unfold DrainSource Window; decide
    · simp only [ModeSource, PerCallResidualPublicationR52.witnessNew, witnessForward]; unfold Window; decide
    · unfold NativeSource; decide
  · rcases List.mem_singleton.mp rest with rfl
    refine ⟨⟨rfl, rfl⟩, ?_, ?_, ?_⟩
    · unfold DrainSource Window; decide
    · simp only [ModeSource, PerCallResidualPublicationR52.witnessOld, witnessOldForward]; decide
    · unfold NativeSource; decide

theorem concrete_whole_publication :
    wholeObserve witnessInputs PerCallResidualPublicationR52.witnessStore witnessQuery witnessPlan witnessCalls = true := by
  apply source_whole_observed _ _ _ _ _ _ (by decide) concrete_assembly
  · intro index
    cases index with
    | zero => rfl
    | succ index => cases index <;> rfl
  · exact concrete_sources
  · rfl
  · decide
  · exact concrete_owner_reads
  · simp only [witnessCalls, CutChain, CutShape, CutOrder]; decide

/-- Accepted canonical/deduplicated source inventory [7,8], preserving initial
sibling 8, adding only new 7, and not appending AlreadyPresent 8. -/
theorem concrete_parent_frame :
    witnessQuery.frame.after.lowerAtoms = witnessQuery.frame.before.lowerAtoms ++ witnessCalls.filterMap atomPart :=
  (whole_exact_native_frame _ _ _ _ _ concrete_whole_publication).2.2.2

theorem concrete_missing_reordered_foreign_fact_rejected :
    assemble witnessQuery 0 witnessPlan [PerCallResidualPublicationR52.witnessNew] = none ∧
    assemble witnessQuery 0 witnessPlan witnessCalls.reverse = none ∧
    assemble witnessQuery 0 witnessPlan (witnessCalls ++ [PerCallResidualPublicationR52.witnessNew]) = none ∧
    assemble { witnessQuery with publication := 11 } 0 witnessPlan witnessCalls = none ∧
    assemble { witnessQuery with originalFact := { witnessFact with fact := 301 } } 0 witnessPlan witnessCalls = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The input/current owner tables agree with these deliberately altered
snapshots, so rejection is at prefix/suffix checks, not missing table reads. -/
def frameInputs (before after : CurrentEmissionOwnershipR47.RowBounds Nat) : Inputs Nat Nat Nat :=
  { witnessInputs with
    initialRows := fun row => if row = 9 then some before else none
    after := { witnessInputs.after with current := { witnessNative with
      effectRows := fun row => if row = 9 then some after else none } } }
def frameQuery (before after : CurrentEmissionOwnershipR47.RowBounds Nat) : Query Nat Nat Nat Nat :=
  { witnessQuery with frame := { witnessQuery.frame with before, after } }

theorem concrete_prefix_suffix_rejected :
    ¬ OwnerReads (frameInputs ⟨[], [], [99], []⟩ witnessAfter)
      (frameQuery ⟨[], [], [99], []⟩ witnessAfter) witnessCalls ∧
    ¬ OwnerReads (frameInputs witnessBefore ⟨[], [], [8, 7, 7], []⟩)
      (frameQuery witnessBefore ⟨[], [], [8, 7, 7], []⟩) witnessCalls ∧
    ¬ OwnerReads (frameInputs witnessBefore witnessBefore) (frameQuery witnessBefore witnessBefore) witnessCalls ∧
    ¬ OwnerReads (frameInputs witnessBefore ⟨[], [], [8, 7, 10], []⟩)
      (frameQuery witnessBefore ⟨[], [], [8, 7, 10], []⟩) witnessCalls := by
  unfold OwnerReads; decide

def twoNewCalls : List (Captured Nat Nat) :=
  [PerCallResidualPublicationR52.witnessNew,
    { PerCallResidualPublicationR52.witnessNew with
      probe := { witnessForward with bound := { witnessBound with item := .effectAtom 10 } } }]

theorem concrete_reordered_suffix_rejected :
    ¬ OwnerReads (frameInputs witnessBefore ⟨[], [], [8, 10, 7], []⟩)
      (frameQuery witnessBefore ⟨[], [], [8, 10, 7], []⟩) twoNewCalls := by
  unfold OwnerReads; decide

theorem concrete_suppressed_whole_keeps_existing :
    wholeObserve suppressionInputs ⟨fun _ _ => none, fun _ => none⟩ suppressionQuery
      [(.effectAtom 7, .suppress)] [] = true ∧
    itemCallKeys suppressionQuery.items = [] ∧
    7 ∈ suppressionQuery.frame.after.lowerAtoms ∧ 8 ∈ suppressionQuery.frame.after.lowerAtoms := by decide

theorem concrete_observer_loss_successful_forward :
    witnessCall.returned = true ∧ witnessOldCall.returned = true ∧
    wholeObserve witnessInputs ⟨fun _ _ => none, fun _ => none⟩ witnessQuery witnessPlan witnessCalls = false := by decide

theorem concrete_cut_reordering_rejected :
    ¬ Chronological witnessCalls.reverse ∧
    ¬ Chronological [PerCallResidualPublicationR52.witnessNew,
      { PerCallResidualPublicationR52.witnessOld with completionCut := 0 }] := by decide

end YulangClosure.WholePublicationResidualR53
