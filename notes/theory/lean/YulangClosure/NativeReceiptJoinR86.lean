import YulangClosure.NativeRootPremisesR85

/-!
R86 candidate: an indexed join between the retained pending attachment and a
separate completed clone. The full Native is an input and is never rewritten.
Every Origin index and every matching completion index is counted, including
duplicate records. This is the R57 finite encoding of the pending-receipt
reader, not an extracted Rust implementation or a new R84 consumer.

Sources: candidate_context.rs 2284-2340 and checked_source_drain_in_cuts;
candidate_receiver.rs 3980-4020. R57 omits native drain_index and replay-ack
payloads, and separates cause occurrence/slot. Their encoding and all native
transition/ownership correspondence remain open. No execution is claimed.
-/
namespace YulangClosure.NativeReceiptJoinR86

open ProviderNativeContextR57

variable {S T : Type} [DecidableEq S] [DecidableEq T]

def completeClone (p : Drain S T) : Drain S T := {p with completed := true}

/-- All ten non-completion fields in the unchanged R57 receipt. -/
structure NonCompletionFields (p c : Drain S T) : Prop where
  state : p.state = c.state
  originIndex : p.originIndex = c.originIndex
  createdSeed : p.createdSeed = c.createdSeed
  selectedRelation : p.selectedRelation = c.selectedRelation
  cause : p.cause = c.cause
  slot : p.slot = c.slot
  taskLower : p.taskLower = c.taskLower
  taskUpper : p.taskUpper = c.taskUpper
  incoming : p.incoming = c.incoming
  replay : p.replay = c.replay

theorem completeClone_fields (p : Drain S T) :
    NonCompletionFields p (completeClone p) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem fields_and_completed_determine_clone (p c : Drain S T)
    (fields : NonCompletionFields p c) (done : c.completed = true) :
    c = completeClone p := by
  rcases p with ⟨ps, pi, pk, pr, pc, pl, plo, phi, pin, prep, pdone⟩
  rcases c with ⟨cs, ci, ck, cr, cc, cl, clo, chi, cin, crep, cdone⟩
  rcases fields with ⟨hs, hi, hk, hr, hc, hl, hlo, hhi, hin, hrep⟩
  cases hs
  cases hi
  cases hk
  cases hr
  cases hc
  cases hl
  cases hlo
  cases hhi
  cases hin
  cases hrep
  cases done
  rfl

/-- Source occurrence/pair competitors are enumerated before receipt checks.
Unlike R84 this predicate has no state or slot prefilter on Origins. -/
def originIndices (n : Native S T) (occurrence : S)
    (lower upper : Endpoint T) : List Nat :=
  (List.range n.origins.length).filter fun index =>
    match n.origins[index]? with
    | none => false
    | some o => decide (o.occurrence = occurrence) &&
        match relationRead n o.relation with
        | none => false
        | some r => decide (r.lower = lower ∧ r.upper = upper)

/-- Equality tests the entire completed clone, not only a relation ID or bit. -/
def completionIndices (cs : List (Drain S T)) (p : Drain S T) : List Nat :=
  (List.range cs.length).filter fun index =>
    decide (cs[index]? = some (completeClone p))

/-- Singleton selection supplies its checked equation; no uniqueness law is
assumed. Equal duplicate values at distinct indices remain competitors. -/
def singletonIndex (indices : List Nat) : Option {i : Nat // indices = [i]} :=
  match equal : indices with
  | [i] => some ⟨i, by simp only [equal]⟩
  | _ => none

theorem singletonIndex_empty : singletonIndex [] = none := rfl

theorem singletonIndex_multiple (i j : Nat) (rest : List Nat) :
    singletonIndex (i :: j :: rest) = none := rfl

theorem singletonIndex_unique (indices : List Nat) (i j : Nat)
    (left : indices = [i]) (right : indices = [j]) : i = j :=
  (List.cons.inj (left.symm.trans right)).1

/-- Reduce selection at its original dependent Option type, before the
reader uses the selected subtype's value. Proof irrelevance retains h. -/
theorem singletonIndex_of_eq (indices : List Nat) (i : Nat)
    (h : indices = [i]) : singletonIndex indices = some ⟨i, h⟩ := by
  subst indices
  rfl

theorem completionIndices_single_clone (p : Drain S T) :
    completionIndices [completeClone p] p = [0] := by
  simp [completionIndices, List.range_succ]

theorem completionIndices_duplicate_clone (p : Drain S T) :
    completionIndices [completeClone p, completeClone p] p = [0, 1] := by
  simp [completionIndices, List.range_succ]

theorem completion_index_read (cs : List (Drain S T)) (p : Drain S T)
    (index : Nat) (member : index ∈ completionIndices cs p) :
    cs[index]? = some (completeClone p) := by
  exact of_decide_eq_true (List.mem_filter.mp member).2

theorem completion_index_unique (cs : List (Drain S T)) (p : Drain S T)
    (i j : Nat) (selected : completionIndices cs p = [i])
    (member : j ∈ completionIndices cs p) : j = i := by
  rw [selected] at member
  exact List.mem_singleton.mp member

/-- Indexed identity/receipt guards shared by the pending-receipt capture and
saved-call projection. Incoming/replay values remain arbitrary and are cloned.
The extra false bit represents the in-cuts/saved pending reader specifically. -/
def Guards (o : Origin S T) (p : Drain S T) (originIndex : Nat)
    (occurrence : S) (lower upper : Endpoint T) : Prop :=
  o.occurrence = occurrence ∧ p.originIndex = originIndex ∧
  p.createdSeed = o.relation ∧ p.selectedRelation = o.relation ∧
  p.cause = occurrence ∧ p.slot = o.slot ∧
  p.taskLower = lower ∧ p.taskUpper = upper ∧ p.completed = false

instance (o : Origin S T) (p : Drain S T) (originIndex : Nat)
    (occurrence : S) (lower upper : Endpoint T) :
    Decidable (Guards o p originIndex occurrence lower upper) := by
  unfold Guards
  infer_instance

/-- Both physical lists and their exact indices are retained. A completion
clone never replaces the attached receipt or its owning Origin. -/
structure IndexedJoin (n : Native S T) (cs : List (Drain S T))
    (occurrence : S) (lower upper : Endpoint T) where
  originIndex : Nat
  completionIndex : Nat
  origin : Origin S T
  pending : Drain S T
  completion : Drain S T
  originRead : n.origins[originIndex]? = some origin
  attached : origin.drain = some pending
  completionRead : cs[completionIndex]? = some completion
  guards : Guards origin pending originIndex occurrence lower upper
  clone : completion = completeClone pending
  originSelection : originIndices n occurrence lower upper = [originIndex]
  completionSelection : completionIndices cs pending = [completionIndex]

/-- Finite reader: all competitors are counted, then both indexed records and
all guards are checked. The returned proof fields are constructed by these
decidable checks. No Root/Primitive/selector-law parameter is supplied. -/
def readJoin (n : Native S T) (cs : List (Drain S T))
    (occurrence : S) (lower upper : Endpoint T) :
    Option (IndexedJoin n cs occurrence lower upper) := do
  let oi ← singletonIndex (originIndices n occurrence lower upper)
  match ho : n.origins[oi.val]? with
  | none => none
  | some o =>
      match hp : o.drain with
      | none => none
      | some p =>
          let ci ← singletonIndex (completionIndices cs p)
          match hc : cs[ci.val]? with
          | none => none
          | some c =>
              if checked : Guards o p oi.val occurrence lower upper ∧ c = completeClone p then
                some ⟨oi.val, ci.val, o, p, c, ho, hp, hc,
                  checked.1, checked.2, oi.property, ci.property⟩
              else none

theorem readJoin_missing_origin (n : Native S T) (cs : List (Drain S T))
    (occurrence : S) (lower upper : Endpoint T)
    (missing : originIndices n occurrence lower upper = []) :
    readJoin n cs occurrence lower upper = none := by
  simp [readJoin, missing, singletonIndex]

theorem readJoin_ambiguous_origin (n : Native S T) (cs : List (Drain S T))
    (occurrence : S) (lower upper : Endpoint T) (i j : Nat) (rest : List Nat)
    (ambiguous : originIndices n occurrence lower upper = i :: j :: rest) :
    readJoin n cs occurrence lower upper = none := by
  simp [readJoin, ambiguous, singletonIndex]

theorem readJoin_missing_attachment (n : Native S T) (cs : List (Drain S T))
    (occurrence : S) (lower upper : Endpoint T) (i : Nat) (o : Origin S T)
    (selected : originIndices n occurrence lower upper = [i])
    (indexed : n.origins[i]? = some o) (missing : o.drain = none) :
    readJoin n cs occurrence lower upper = none := by
  have originSelect := singletonIndex_of_eq _ i selected
  simp [readJoin, originSelect, indexed, missing]

theorem readJoin_missing_completion (n : Native S T) (cs : List (Drain S T))
    (occurrence : S) (lower upper : Endpoint T) (i : Nat)
    (o : Origin S T) (p : Drain S T)
    (selected : originIndices n occurrence lower upper = [i])
    (indexed : n.origins[i]? = some o) (attached : o.drain = some p)
    (missing : completionIndices cs p = []) :
    readJoin n cs occurrence lower upper = none := by
  have originSelect := singletonIndex_of_eq _ i selected
  have completionSelect : singletonIndex (completionIndices cs p) = none := by
    simp [singletonIndex, missing]
  simp [readJoin, originSelect, indexed, attached, completionSelect]

theorem readJoin_ambiguous_completion (n : Native S T) (cs : List (Drain S T))
    (occurrence : S) (lower upper : Endpoint T) (i j k : Nat) (rest : List Nat)
    (o : Origin S T) (p : Drain S T)
    (selected : originIndices n occurrence lower upper = [i])
    (indexed : n.origins[i]? = some o) (attached : o.drain = some p)
    (ambiguous : completionIndices cs p = j :: k :: rest) :
    readJoin n cs occurrence lower upper = none := by
  have originSelect := singletonIndex_of_eq _ i selected
  have completionSelect : singletonIndex (completionIndices cs p) = none := by
    simp [singletonIndex, ambiguous]
  simp [readJoin, originSelect, indexed, attached, completionSelect]

theorem readJoin_bad_guards (n : Native S T) (cs : List (Drain S T))
    (occurrence : S) (lower upper : Endpoint T) (i j : Nat)
    (o : Origin S T) (p c : Drain S T)
    (selected : originIndices n occurrence lower upper = [i])
    (indexed : n.origins[i]? = some o) (attached : o.drain = some p)
    (completed : completionIndices cs p = [j]) (read : cs[j]? = some c)
    (bad : ¬ Guards o p i occurrence lower upper) :
    readJoin n cs occurrence lower upper = none := by
  have originSelect := singletonIndex_of_eq _ i selected
  have completionSelect := singletonIndex_of_eq _ j completed
  simp [readJoin, originSelect, indexed, attached, completionSelect, read, bad]

theorem readJoin_accepts (n : Native S T) (cs : List (Drain S T))
    (occurrence : S) (lower upper : Endpoint T) (i j : Nat)
    (o : Origin S T) (p : Drain S T)
    (selected : originIndices n occurrence lower upper = [i])
    (indexed : n.origins[i]? = some o) (attached : o.drain = some p)
    (completed : completionIndices cs p = [j])
    (read : cs[j]? = some (completeClone p))
    (good : Guards o p i occurrence lower upper) :
    (readJoin n cs occurrence lower upper).isSome = true := by
  have originSelect := singletonIndex_of_eq _ i selected
  have completionSelect := singletonIndex_of_eq _ j completed
  simp [readJoin, originSelect, indexed, attached, completionSelect, read, good]

theorem joined_fields (n : Native S T) (cs : List (Drain S T))
    (occurrence : S) (lower upper : Endpoint T)
    (j : IndexedJoin n cs occurrence lower upper) :
    NonCompletionFields j.pending j.completion := by
  rw [j.clone]
  exact completeClone_fields j.pending

theorem joined_flags (n : Native S T) (cs : List (Drain S T))
    (occurrence : S) (lower upper : Endpoint T)
    (j : IndexedJoin n cs occurrence lower upper) :
    j.pending.completed = false ∧ j.completion.completed = true := by
  refine ⟨j.guards.2.2.2.2.2.2.2.2, ?_⟩
  rw [j.clone]
  rfl

theorem joined_records_distinct (n : Native S T) (cs : List (Drain S T))
    (occurrence : S) (lower upper : Endpoint T)
    (j : IndexedJoin n cs occurrence lower upper) : j.pending ≠ j.completion := by
  intro same
  have flags := joined_flags n cs occurrence lower upper j
  have equal := congrArg Drain.completed same
  rw [flags.1, flags.2] at equal
  cases equal

theorem joined_completion_not_attached (n : Native S T) (cs : List (Drain S T))
    (occurrence : S) (lower upper : Endpoint T)
    (j : IndexedJoin n cs occurrence lower upper) :
    j.origin.drain ≠ some j.completion := by
  intro attached
  exact joined_records_distinct n cs occurrence lower upper j
    (Option.some.inj (j.attached.symm.trans attached))

/-- The original index cannot be reused for a completed-attachment replacement.
This does not assert that no equal replacement occurs elsewhere as a competitor. -/
theorem joined_replacement_not_at_origin_index (n : Native S T)
    (cs : List (Drain S T)) (occurrence : S) (lower upper : Endpoint T)
    (j : IndexedJoin n cs occurrence lower upper) :
    n.origins[j.originIndex]? ≠ some {j.origin with drain := some j.completion} := by
  intro replaced
  have same := Option.some.inj (j.originRead.symm.trans replaced)
  have attached := congrArg Origin.drain same
  exact joined_completion_not_attached n cs occurrence lower upper j attached

/-- Occurrence/pair singleton selection has not proved the separate R57
state/relation-ID selector equation supplied here. With that exact equation,
R57 still reads the pending attachment, not the completion vector. -/
theorem joined_R57_rootDrain (n : Native S T) (cs : List (Drain S T))
    (occurrence : S) (lower upper : Endpoint T)
    (j : IndexedJoin n cs occurrence lower upper)
    (selected : ProviderNativeContextR57.originRead n j.origin.relation = some j.origin) :
    rootDrain n j.origin.relation = some j.pending := by
  simp [rootDrain, selected, j.attached]

theorem joined_R57_completed_false (n : Native S T) (cs : List (Drain S T))
    (occurrence : S) (lower upper : Endpoint T)
    (j : IndexedJoin n cs occurrence lower upper)
    (selected : ProviderNativeContextR57.originRead n j.origin.relation = some j.origin) :
    ProviderNativeContextR57.completed n j.origin.relation = false := by
  have pending := (joined_flags n cs occurrence lower upper j).1
  have drain := joined_R57_rootDrain n cs occurrence lower upper j selected
  simp [ProviderNativeContextR57.completed, selected, drain, pending]

/-- Even without a global lifecycle invariant, the particular joined Origin
cannot supply R84 Primitive on that same physical Origin. The attached receipt
equation identifies R84's drain with the pending record, not its clone. -/
theorem joined_origin_blocks_R84_primitive
    (n : Native S T) (cs : List (Drain S T))
    (occurrence : S) (lower upper : Endpoint T)
    (j : IndexedJoin n cs occurrence lower upper)
    (s : OccurrenceQualifiedConsumerR66.Source S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T)
    (q : OccurrenceQualifiedConsumerR66.Request S T)
    (i : OccurrenceQualifiedConsumerR66.Incidence s inventory q) (index : Nat)
    (d : ConstructedPhysicalRootR84.Records S T) (sameOrigin : d.origin = j.origin) :
    ¬ ConstructedPhysicalRootR84.Primitive s inventory n q i index d := by
  intro h
  rcases h with ⟨hs, he, hu, hocc, hstore, hem, ha, hunique, hb, hstate, hslot, hback,
    hcurrent, har, her, hpair, hestate, hastate, heowner, haowner, hpol, heffect,
    hread, hid, hcandidates, horigins, hostate, hoocc, hoslot, hdrain, hindexed,
    hdstate, hseed, hselected, hincoming, hreplay, hcause, hdslot, hdone,
    hlower, hupper, hsource, hslower, hsupper, hv1, hv2⟩
  rw [sameOrigin] at hdrain
  have sameDrain : j.pending = d.drain :=
    Option.some.inj (j.attached.symm.trans hdrain)
  have pending := (joined_flags n cs occurrence lower upper j).1
  rw [sameDrain, hdone] at pending
  cases pending

/-- Parent application on the unchanged entire Native/Records. A separate
completion never repairs R84's completed-attached-receipt premise. No competitors
are removed and no candidate Root is relabeled as the original R66 Root. -/
theorem reachable_join_still_blocks_R84
    (base : Native S T) (p : NativeRootPremisesR85.Producer S T)
    (reachable : NativeRootPremisesR85.Reachable base p)
    (occurrence : S) (lower upper : Endpoint T)
    (_join : IndexedJoin p.native p.completions occurrence lower upper)
    (s : OccurrenceQualifiedConsumerR66.Source S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T)
    (q : OccurrenceQualifiedConsumerR66.Request S T)
    (i : OccurrenceQualifiedConsumerR66.Incidence s inventory q) (index : Nat)
    (d : ConstructedPhysicalRootR84.Records S T) :
    ¬ ConstructedPhysicalRootR84.Primitive s inventory p.native q i index d :=
  NativeRootPremisesR85.reachable_blocks_R84_primitive base p reachable
    s inventory q i index d

/-- Native capture windows do not truncate or replace either physical list. -/
structure Cuts where
  originCut : Nat
  originEnd : Nat
  completionCut : Nat
  completionEnd : Nat

def ValidCuts (n : Native S T) (cs : List (Drain S T)) (w : Cuts) : Prop :=
  w.originCut ≤ w.originEnd ∧ w.originEnd ≤ n.origins.length ∧
  w.completionCut ≤ w.completionEnd ∧ w.completionEnd ≤ cs.length

instance (n : Native S T) (cs : List (Drain S T)) (w : Cuts) :
    Decidable (ValidCuts n cs w) := by unfold ValidCuts; infer_instance

def originIndicesInCuts (n : Native S T) (w : Cuts) (occurrence : S)
    (lower upper : Endpoint T) : List Nat :=
  (originIndices n occurrence lower upper).filter fun i =>
    decide (w.originCut ≤ i ∧ i < w.originEnd)

def completionIndicesInCuts (cs : List (Drain S T)) (w : Cuts)
    (p : Drain S T) : List Nat :=
  (completionIndices cs p).filter fun i =>
    decide (w.completionCut ≤ i ∧ i < w.completionEnd)

/-- This has cut-local singleton equations. It does not contain or imply the
full-inventory singleton equations required by IndexedJoin or R57/R84. -/
structure WindowJoin (n : Native S T) (cs : List (Drain S T)) (w : Cuts)
    (occurrence : S) (lower upper : Endpoint T) where
  originIndex : Nat
  completionIndex : Nat
  origin : Origin S T
  pending : Drain S T
  completion : Drain S T
  originRead : n.origins[originIndex]? = some origin
  attached : origin.drain = some pending
  completionRead : cs[completionIndex]? = some completion
  guards : Guards origin pending originIndex occurrence lower upper
  clone : completion = completeClone pending
  valid : ValidCuts n cs w
  originSelection : originIndicesInCuts n w occurrence lower upper = [originIndex]
  completionSelection : completionIndicesInCuts cs w pending = [completionIndex]

def readJoinInCuts (n : Native S T) (cs : List (Drain S T)) (w : Cuts)
    (occurrence : S) (lower upper : Endpoint T) :
    Option (WindowJoin n cs w occurrence lower upper) :=
  if valid : ValidCuts n cs w then do
    let oi ← singletonIndex (originIndicesInCuts n w occurrence lower upper)
    match ho : n.origins[oi.val]? with
    | none => none
    | some o =>
        match hp : o.drain with
        | none => none
        | some p =>
            let ci ← singletonIndex (completionIndicesInCuts cs w p)
            match hc : cs[ci.val]? with
            | none => none
            | some c =>
                if checked : Guards o p oi.val occurrence lower upper ∧ c = completeClone p then
                  some ⟨oi.val, ci.val, o, p, c, ho, hp, hc,
                    checked.1, checked.2, valid, oi.property, ci.property⟩
                else none
  else none

theorem readJoinInCuts_invalid (n : Native S T) (cs : List (Drain S T))
    (w : Cuts) (occurrence : S) (lower upper : Endpoint T)
    (invalid : ¬ ValidCuts n cs w) :
    readJoinInCuts n cs w occurrence lower upper = none := by
  simp [readJoinInCuts, invalid]

theorem readJoinInCuts_ambiguous_origin (n : Native S T) (cs : List (Drain S T))
    (w : Cuts) (occurrence : S) (lower upper : Endpoint T)
    (i j : Nat) (rest : List Nat)
    (ambiguous : originIndicesInCuts n w occurrence lower upper = i :: j :: rest) :
    readJoinInCuts n cs w occurrence lower upper = none := by
  by_cases valid : ValidCuts n cs w
  · simp [readJoinInCuts, valid, ambiguous, singletonIndex]
  · simp [readJoinInCuts, valid]

theorem readJoinInCuts_ambiguous_completion (n : Native S T) (cs : List (Drain S T))
    (w : Cuts) (occurrence : S) (lower upper : Endpoint T)
    (i j k : Nat) (rest : List Nat) (o : Origin S T) (p : Drain S T)
    (selected : originIndicesInCuts n w occurrence lower upper = [i])
    (indexed : n.origins[i]? = some o) (attached : o.drain = some p)
    (ambiguous : completionIndicesInCuts cs w p = j :: k :: rest) :
    readJoinInCuts n cs w occurrence lower upper = none := by
  have originSelect := singletonIndex_of_eq _ i selected
  have completionSelect : singletonIndex (completionIndicesInCuts cs w p) = none := by
    simp [singletonIndex, ambiguous]
  by_cases valid : ValidCuts n cs w
  · simp [readJoinInCuts, valid, originSelect, indexed, attached, completionSelect]
  · simp [readJoinInCuts, valid]

theorem readJoinInCuts_accepts (n : Native S T) (cs : List (Drain S T))
    (w : Cuts) (occurrence : S) (lower upper : Endpoint T) (i j : Nat)
    (o : Origin S T) (p : Drain S T) (valid : ValidCuts n cs w)
    (selected : originIndicesInCuts n w occurrence lower upper = [i])
    (indexed : n.origins[i]? = some o) (attached : o.drain = some p)
    (completed : completionIndicesInCuts cs w p = [j])
    (read : cs[j]? = some (completeClone p))
    (good : Guards o p i occurrence lower upper) :
    (readJoinInCuts n cs w occurrence lower upper).isSome = true := by
  have originSelect := singletonIndex_of_eq _ i selected
  have completionSelect := singletonIndex_of_eq _ j completed
  simp [readJoinInCuts, valid, originSelect, indexed, attached, completionSelect, read, good]

theorem window_join_fields (n : Native S T) (cs : List (Drain S T))
    (w : Cuts) (occurrence : S) (lower upper : Endpoint T)
    (j : WindowJoin n cs w occurrence lower upper) :
    NonCompletionFields j.pending j.completion := by
  rw [j.clone]
  exact completeClone_fields j.pending

theorem window_origin_index_unique (n : Native S T) (cs : List (Drain S T))
    (w : Cuts) (occurrence : S) (lower upper : Endpoint T)
    (j : WindowJoin n cs w occurrence lower upper) (index : Nat)
    (member : index ∈ originIndicesInCuts n w occurrence lower upper) :
    index = j.originIndex := by
  rw [j.originSelection] at member
  exact List.mem_singleton.mp member

theorem window_completion_index_unique (n : Native S T) (cs : List (Drain S T))
    (w : Cuts) (occurrence : S) (lower upper : Endpoint T)
    (j : WindowJoin n cs w occurrence lower upper) (index : Nat)
    (member : index ∈ completionIndicesInCuts cs w j.pending) :
    index = j.completionIndex := by
  rw [j.completionSelection] at member
  exact List.mem_singleton.mp member

theorem window_join_completion_not_attached (n : Native S T) (cs : List (Drain S T))
    (w : Cuts) (occurrence : S) (lower upper : Endpoint T)
    (j : WindowJoin n cs w occurrence lower upper) :
    j.origin.drain ≠ some j.completion := by
  intro attached
  have same := Option.some.inj (j.attached.symm.trans attached)
  have flag := congrArg Drain.completed same
  have pending : j.pending.completed = false := j.guards.2.2.2.2.2.2.2.2
  rw [pending, j.clone] at flag
  cases flag

theorem window_origin_blocks_R84_primitive
    (n : Native S T) (cs : List (Drain S T)) (w : Cuts)
    (occurrence : S) (lower upper : Endpoint T)
    (j : WindowJoin n cs w occurrence lower upper)
    (s : OccurrenceQualifiedConsumerR66.Source S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T)
    (q : OccurrenceQualifiedConsumerR66.Request S T)
    (i : OccurrenceQualifiedConsumerR66.Incidence s inventory q) (index : Nat)
    (d : ConstructedPhysicalRootR84.Records S T) (sameOrigin : d.origin = j.origin) :
    ¬ ConstructedPhysicalRootR84.Primitive s inventory n q i index d := by
  intro h
  rcases h with ⟨hs, he, hu, hocc, hstore, hem, ha, hunique, hb, hstate, hslot, hback,
    hcurrent, har, her, hpair, hestate, hastate, heowner, haowner, hpol, heffect,
    hread, hid, hcandidates, horigins, hostate, hoocc, hoslot, hdrain, hindexed,
    hdstate, hseed, hselected, hincoming, hreplay, hcause, hdslot, hdone,
    hlower, hupper, hsource, hslower, hsupper, hv1, hv2⟩
  rw [sameOrigin] at hdrain
  have sameDrain : j.pending = d.drain :=
    Option.some.inj (j.attached.symm.trans hdrain)
  have pending : j.pending.completed = false := j.guards.2.2.2.2.2.2.2.2
  rw [sameDrain, hdone] at pending
  cases pending

/-- All global competitors in the chosen window survive the index filter. -/
theorem origin_competitor_retained_in_cuts (n : Native S T) (w : Cuts)
    (occurrence : S) (lower upper : Endpoint T) (index : Nat)
    (competitor : index ∈ originIndices n occurrence lower upper)
    (inside : w.originCut ≤ index ∧ index < w.originEnd) :
    index ∈ originIndicesInCuts n w occurrence lower upper := by
  exact List.mem_filter.mpr ⟨competitor, by simpa only [decide_eq_true_eq] using inside⟩

theorem completion_competitor_retained_in_cuts (cs : List (Drain S T))
    (w : Cuts) (p : Drain S T) (index : Nat)
    (competitor : index ∈ completionIndices cs p)
    (inside : w.completionCut ≤ index ∧ index < w.completionEnd) :
    index ∈ completionIndicesInCuts cs w p := by
  exact List.mem_filter.mpr ⟨competitor, by simpa only [decide_eq_true_eq] using inside⟩

end YulangClosure.NativeReceiptJoinR86
