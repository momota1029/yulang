import YulangClosure.ReachedSlotCompletenessR59

/-! Owner-local primitive readers; no reader soundness or existing Inputs is
supplied. General Rust extraction and execution correspondence remain open. -/
namespace YulangClosure.NativeLocalDecodeR60
open ProviderNativeContextR57
open ReachedSlotSearchR58
variable {S T : Type} [DecidableEq S] [DecidableEq T]

def rowRead (n : Native S T) (index : Nat) : Option EffectRow :=
  unique (fun r => decide (r.state = n.state ∧ n.state = n.state ∧ r.index = index)) n.effectRows

def viewRead (n : Native S T) (index : Nat) : Option (View S) :=
  unique (fun v => decide (v.state = n.state ∧ v.index = index)) n.views

def fromOption (error : Failure) : Option A → Except Failure A
  | none => .error error | some value => .ok value

def rows (n : Native S T) (index : Nat) : Except Failure (Bounds ReachedSlotSearchR58.Endpoint) :=
  (fromOption (nativeFailure .rowLookup .boundMismatch) (rowRead n index)).map EffectRow.bounds

def views (n : Native S T) (index : Nat) : Except Failure (View S) :=
  fromOption (nativeFailure .viewLookup .boundMismatch) (viewRead n index)

theorem unique_filter_eq {A : Type} (test : A → Bool) (xs : List A) (x : A)
    (read : unique test xs = some x) : xs.filter test = [x] := by
  unfold ProviderNativeContextR57.unique SourceInternalContextR55.unique at read
  cases filtered : xs.filter test with
  | nil => simp [filtered] at read
  | cons head rest =>
    cases rest with
    | nil => simpa [filtered] using read
    | cons next tail => simp [filtered] at read

theorem unique_spec {A : Type} (test : A → Bool) (xs : List A) (x : A)
    (read : unique test xs = some x) : x ∈ xs ∧ test x = true := by
  have filtered := unique_filter_eq test xs x read
  exact List.mem_filter.mp (by rw [filtered]; simp)

theorem from_option_success (error : Failure) (x : Option A) (a : A)
    (read : fromOption error x = .ok a) : x = some a := by
  cases x with
  | none => cases read
  | some value => cases read; rfl

theorem row_reader_projection (n : Native S T) (index : Nat) (r : EffectRow)
    (read : rowRead n index = some r) :
    (current n).effectRows (.effectRow n.state index) = some (effectBounds r.state r.bounds) :=
  effect_row_reader n index r read

theorem view_reader_projection (n : Native S T) (index : Nat) (v : View S)
    (read : viewRead n index = some v) :
    v.state = n.state ∧ v.index = index ∧ (arrival n).views index = some (view v) := by
  have own : v.state = n.state ∧ v.index = index := of_decide_eq_true (unique_spec _ _ _ read).2
  refine ⟨own.1,own.2,?_⟩
  change (unique (fun v => decide (v.state = n.state ∧ v.index = index)) n.views).map view = some (view v)
  change (viewRead n index).map view = _
  rw [read]
  rfl


def rawSlot (rowIndex : Nat) (lane : LowerLane) (index : Nat) : Slot :=
  ⟨.effect rowIndex, match lane with | .row => .effectLowerRow | .atom => .effectLowerAtom,index⟩
def requestedSlot (n : Native S T) (rowIndex : Nat) (lane : LowerLane) (index : Nat) :=
  slot (S := S) (T := T) n.state (rawSlot rowIndex lane index)
def requestedBound (n : Native S T) (rowIndex : Nat) (target : EffectEndpoint) :=
  bound (S := S) n.state (⟨.effect rowIndex,.positive,.effect target⟩ : Bound T)
def atomCompatible : EffectEndpoint → Bool | .row _ => false | _ => true

theorem current_row_slot (n : Native S T) (rowIndex index item : Nat) (r : EffectRow)
    (read : rowRead n rowIndex = some r) (itemRead : r.bounds.lowerRows[index]? = some item) :
    CurrentEmissionOwnershipR47.currentBound (current n) (requestedSlot n rowIndex .row index) =
      some (requestedBound n rowIndex (.row item)) := by
  have own : r.state = n.state ∧ n.state = n.state ∧ r.index = rowIndex :=
    of_decide_eq_true (unique_spec _ _ _ read).2
  have rowEq := effect_row_reader n rowIndex r read
  rw [own.1] at rowEq
  simp [CurrentEmissionOwnershipR47.currentBound,requestedSlot,rawSlot,slot,row,lane,
    rowEq,effectBounds,itemRead,requestedBound,bound,polarity,endpoint]

theorem current_atom_slot (n : Native S T) (rowIndex index : Nat) (item : EffectEndpoint) (r : EffectRow)
    (read : rowRead n rowIndex = some r) (itemRead : r.bounds.lowerAtoms[index]? = some item)
    (compatible : atomCompatible item = true) :
    CurrentEmissionOwnershipR47.currentBound (current n) (requestedSlot n rowIndex .atom index) =
      some (requestedBound n rowIndex item) := by
  have own : r.state = n.state ∧ n.state = n.state ∧ r.index = rowIndex :=
    of_decide_eq_true (unique_spec _ _ _ read).2
  have rowEq := effect_row_reader n rowIndex r read
  rw [own.1] at rowEq
  cases item <;> simp_all [atomCompatible,CurrentEmissionOwnershipR47.currentBound,
    requestedSlot,rawSlot,slot,row,lane,effectBounds,requestedBound,bound,polarity,endpoint]

structure TargetRead (n : Native S T) (rowIndex : Nat) (lane : LowerLane) (index : Nat) where
  target : EffectEndpoint
  current : CurrentEmissionOwnershipR47.currentBound (ProviderNativeContextR57.current n)
    (requestedSlot n rowIndex lane index) = some (requestedBound n rowIndex target)

def targetRead (n : Native S T) (rowIndex : Nat) (lane : LowerLane) (index : Nat) :
    Except Failure (TargetRead n rowIndex lane index) :=
  match read : rowRead n rowIndex with
  | none => .error (nativeFailure .rowLookup .boundMismatch)
  | some r => match lane with
    | .row => match itemRead : r.bounds.lowerRows[index]? with
      | none => .error (nativeFailure .physicalOwner .boundMismatch)
      | some item => .ok ⟨.row item,current_row_slot n rowIndex index item r read itemRead⟩
    | .atom => match itemRead : r.bounds.lowerAtoms[index]? with
      | none => .error (nativeFailure .physicalOwner .boundMismatch)
      | some item => if compatible : atomCompatible item = true then
          .ok ⟨item,current_atom_slot n rowIndex index item r read itemRead compatible⟩
        else .error (nativeFailure .physicalOwner .boundMismatch)

theorem support_reads_from_view_inventory (n : Native S T) (search : Search S T)
    (index : Nat) (v : View S) (family : S) (ordinal : Nat)
    (read : views n index = .ok v) (closed : v.tail = none)
    (member : (family,ordinal) ∈ v.allowed.zipIdx) :
    AuthenticatedResidualConsumerR49.SupportReads (inputs n search)
      (support (T := T) ⟨n.state,v.index,ordinal,family,v⟩) := by
  have rawRead := from_option_success _ _ v read
  have own := view_reader_projection n index v rawRead
  have same : viewRead n v.index = some v := by simpa [own.2.1] using rawRead
  have itemRead : v.allowed[ordinal]? = some family := List.mk_mem_zipIdx_iff_getElem?.mp member
  unfold AuthenticatedResidualConsumerR49.SupportReads
  refine ⟨?_,?_,?_,?_,?_⟩
  · change (if n.state = n.state then (unique (fun candidate => decide (candidate.state = n.state ∧ candidate.index = v.index)) n.views).map (fun _ => v.index) else none) = some v.index
    simp only [ite_true]
    change (viewRead n v.index).map (fun _ => v.index) = _
    rw [same]
    rfl
  · exact view_reader_equation n v same
  · exact native_member_reader n v.index ordinal v family same itemRead
  · simp [support,view,itemRead]
  · simp [support,view,closed]


def matching (n : Native S T) (requested : CurrentEmissionOwnershipR47.Slot (Key S T)) : List (Emission T × Nat) :=
  n.emissions.zipIdx.filter (fun pair => (emission (S := S) pair.1).physical == requested)

theorem indexed_filter_projection {A B : Type} (xs : List A) (f : A → B) (test : B → Bool) :
    (xs.map f).filter test = (xs.zipIdx.filter (fun pair => test (f pair.1))).map (fun pair => f pair.1) := by
  have same : xs.map f = xs.zipIdx.map (fun pair => f pair.1) := by
    calc
      xs.map f = (xs.zipIdx.map Prod.fst).map f := congrArg (List.map f) (List.zipIdx_map_fst 0 xs).symm
      _ = _ := by simp only [List.map_map]; rfl
  rw [same,List.filter_map]
  rfl

theorem matching_projection (n : Native S T) (requested : CurrentEmissionOwnershipR47.Slot (Key S T)) :
    CurrentEmissionOwnershipR47.emissionsForSlot (current n) requested =
      (matching n requested).map (fun pair => emission pair.1) :=
  indexed_filter_projection n.emissions emission (fun e => e.physical == requested)

theorem matching_selected (n : Native S T) (requested : CurrentEmissionOwnershipR47.Slot (Key S T))
    (e : Emission T) (index : Nat) (selected : matching n requested = [(e,index)]) :
    n.emissions[index]? = some e ∧ (emission (S := S) e).physical = requested ∧
      CurrentEmissionOwnershipR47.emissionsForSlot (current n) requested = [emission e] := by
  have member : (e,index) ∈ matching n requested := by rw [selected]; simp
  have facts := List.mem_filter.mp member
  refine ⟨List.mk_mem_zipIdx_iff_getElem?.mp facts.1,?_,?_⟩
  · simpa only [beq_iff_eq] using facts.2
  · rw [matching_projection,selected]
    rfl

structure PhysicalRead (n : Native S T) (rowIndex : Nat) (c : Cell) where
  sourceTarget : TargetRead n rowIndex c.lane c.index
  targetSame : sourceTarget.target = c.target
  nativeEmission : Emission T
  emissionIndex : Nat
  selected : matching n (requestedSlot n rowIndex c.lane c.index) = [(nativeEmission,emissionIndex)]
  emissionChecks : (emission (S := S) nativeEmission).bound = requestedBound n rowIndex c.target ∧
    (emission (S := S) nativeEmission).bound = (emission nativeEmission).readback.bound ∧
    (emission (S := S) nativeEmission).physical = (emission nativeEmission).readback.slot
  nativeAdmission : Admission T
  admissionRead : n.admissions[nativeEmission.admission]? = some nativeAdmission
  admissionBound : (admission (S := S) nativeAdmission).bound = requestedBound n rowIndex c.target
  relation : Nat
  admissionRelation : nativeAdmission.relation = some relation
  nativeRelation : Relation T
  relationReadback : relationRead n relation = some nativeRelation
  relationPair : (endpoint n.state nativeRelation.lower, endpoint n.state nativeRelation.upper) =
    CurrentEmissionOwnershipR47.boundPair (requestedBound n rowIndex c.target)

def PhysicalRead.value {n : Native S T} {rowIndex : Nat} {c : Cell} (r : PhysicalRead n rowIndex c) : Physical T :=
  ⟨r.nativeEmission.admission,r.emissionIndex,r.nativeAdmission,r.nativeEmission,r.relation,[]⟩

/-- Current slot first; then unique emission, readback, indexed admission,
relation and exact pair. No ancestry or Internal policy runs in this reader. -/
def checkPhysical (n : Native S T) (rowIndex : Nat) (c : Cell) : Except Failure (PhysicalRead n rowIndex c) :=
  match _currentRead : targetRead n rowIndex c.lane c.index with
  | .error error => .error error
  | .ok target => if targetSame : target.target = c.target then
    match selected : matching n (requestedSlot n rowIndex c.lane c.index) with
    | [] => .error (nativeFailure .physicalOwner .missingEmission)
    | [(e,index)] =>
      if checks : (emission (S := S) e).bound = requestedBound n rowIndex c.target ∧
          (emission (S := S) e).bound = (emission e).readback.bound ∧
          (emission (S := S) e).physical = (emission e).readback.slot then
        match admissionRead : n.admissions[e.admission]? with
        | none => .error (nativeFailure .physicalOwner .missingAdmission)
        | some a => if admissionBound : (admission (S := S) a).bound = requestedBound n rowIndex c.target then
          match admissionRelation : a.relation with
          | none => .error (nativeFailure .physicalOwner .missingRelation)
          | some relation => match relationReadback : relationRead n relation with
            | none => .error (nativeFailure .physicalOwner .foreignRelation)
            | some nativeRelation => if relationPair :
                (endpoint (S := S) n.state nativeRelation.lower, endpoint n.state nativeRelation.upper) =
                CurrentEmissionOwnershipR47.boundPair (requestedBound n rowIndex c.target) then
                .ok ⟨target,targetSame,e,index,selected,checks,a,admissionRead,admissionBound,
                  relation,admissionRelation,nativeRelation,relationReadback,relationPair⟩
              else .error (nativeFailure .physicalOwner .foreignRelation)
          else .error (nativeFailure .physicalOwner .boundMismatch)
      else .error (nativeFailure .physicalOwner .boundMismatch)
    | _::_::_ => .error (nativeFailure .physicalOwner .ambiguousPhysicalSlot)
    else .error (nativeFailure .physicalOwner .boundMismatch)

def readPhysical (n : Native S T) (rowIndex : Nat) (c : Cell) : Except Failure (Physical T) :=
  (checkPhysical n rowIndex c).map PhysicalRead.value

theorem relation_read_live (n : Native S T) (index : Nat) (r : Relation T)
    (read : relationRead n index = some r) : index ∈ (current n).liveRelations := by
  have facts := unique_spec _ _ _ read
  have own : r.state = n.state ∧ r.index = index := of_decide_eq_true facts.2
  change index ∈ (n.relations.filter (fun r => decide (r.state = n.state))).map Relation.index
  exact List.mem_map.mpr ⟨r,List.mem_filter.mpr ⟨facts.1,by simp [own.1]⟩,own.2⟩

theorem physical_receipt_decodes (n : Native S T) (search : Search S T) (rowIndex : Nat) (c : Cell)
    (r : PhysicalRead n rowIndex c) :
    AuthenticatedResidualConsumerR49.StepReads (inputs n search)
      (endpoint n.state (.effect (.row rowIndex))) (step (.physical r.value)) ∧
    AuthenticatedResidualConsumerR49.next (step (S := S) (.physical r.value)) = endpoint (S := S) n.state (.effect c.target) := by
  have selected := matching_selected n _ r.nativeEmission r.emissionIndex r.selected
  have currentRead := r.sourceTarget.current
  rw [r.targetSame] at currentRead
  have admissionRead : (current n).admissions[r.nativeEmission.admission]? = some (admission (S := S) r.nativeAdmission) := by
    simp only [current,List.getElem?_map,r.admissionRead,Option.map_some]
  have emissionRead : (current n).emissions[r.emissionIndex]? = some (emission (S := S) r.nativeEmission) := by
    simp only [current,List.getElem?_map,selected.1,Option.map_some]
  constructor
  · change ProviderEntryArrivalR48.EdgeReads (arrival n) _ (physical r.value)
    unfold ProviderEntryArrivalR48.EdgeReads
    refine ⟨admissionRead,emissionRead,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,r.admissionRelation,?_,?_⟩
    · change CurrentEmissionOwnershipR47.emissionsForSlot (current n) (emission (S := S) r.nativeEmission).physical = _
      rw [selected.2.1]
      exact selected.2.2
    · exact r.emissionChecks.1.trans r.admissionBound.symm
    · exact r.emissionChecks.2.2.symm
    · exact r.emissionChecks.2.1.symm.trans (r.emissionChecks.1.trans r.admissionBound.symm)
    · change CurrentEmissionOwnershipR47.currentBound (current n) (emission (S := S) r.nativeEmission).physical = some (admission (S := S) r.nativeAdmission).bound
      rw [selected.2.1,r.admissionBound]
      exact currentRead
    · change (emission (S := S) r.nativeEmission).physical.owner = (admission (S := S) r.nativeAdmission).bound.owner
      rw [selected.2.1,r.admissionBound]
      rfl
    · change (emission (S := S) r.nativeEmission).physical.lane = .effectLowerRow ∨ (emission (S := S) r.nativeEmission).physical.lane = .effectLowerAtom
      rw [selected.2.1]
      cases c.lane <;> simp [requestedSlot,rawSlot,slot,lane]
    · simp only [physical,PhysicalRead.value]
      rw [r.admissionBound]
      trivial
    · change endpoint n.state (.effect (.row rowIndex)) = CurrentEmissionOwnershipR47.rowEndpoint (admission (S := S) r.nativeAdmission).bound.owner
      rw [r.admissionBound]
      rfl
    · change (admission (S := S) r.nativeAdmission).bound.polarity = .positive
      rw [r.admissionBound]
      rfl
    · exact relation_read_live n r.relation r.nativeRelation r.relationReadback
    · change (current n).relationPair r.relation = some (CurrentEmissionOwnershipR47.boundPair (admission (S := S) r.nativeAdmission).bound)
      change (relationRead n r.relation).map (fun rel => (endpoint n.state rel.lower,endpoint n.state rel.upper)) = _
      rw [r.relationReadback,r.admissionBound]
      exact congrArg some r.relationPair
  · change (admission (S := S) r.nativeAdmission).bound.item = _
    rw [r.admissionBound]
    rfl

structure Policy (T : Type) where
  internalRoot : Physical T → Except Failure (InternalReceipt T)
  ancestry : Nat → Nat → Except Failure Unit

def constructedReaders (n : Native S T) (policy : Policy T) : Readers S T :=
  ⟨n.state,n.relations.length,rows n,views n,readPhysical n,policy.internalRoot,policy.ancestry⟩

theorem concrete_local_decode (n : Native S T) (search : Search S T) (policy : Policy T) :
    LocalDecode (constructedReaders n policy) (inputs n search) := by
  constructor
  · intro rowIndex c p read
    change (checkPhysical n rowIndex c).map PhysicalRead.value = .ok p at read
    cases checked : checkPhysical n rowIndex c with
    | error error => simp [checked,Except.map] at read
    | ok receipt =>
      have same : receipt.value = p := by simpa [checked,Except.map] using read
      subst p
      exact physical_receipt_decodes n search rowIndex c receipt
  · intro index v family ordinal read owned closed member
    exact support_reads_from_view_inventory n search index v family ordinal read closed member


/-- R59 completeness and existing consumer refinement, on the very same Native
and inputs, with the concrete decoder supplied by construction. -/
theorem complete_candidates_on_constructed_inputs (n : Native S T) (search : Search S T)
    (policy : Policy T) (q : Query) (limits : Limits) (r : Resource)
    (results : List (Branch S T))
    (run : Run (constructedReaders n policy) q limits (.live ⟨r,[initial q],[],.pop⟩) (.success results))
    (goal : Branch S T) (checked : Checked (constructedReaders n policy) q goal)
    (terminal : goal.endpoint = q.target) :
    goal ∈ results ∧
    AuthenticatedResidualConsumerR49.pathCheck (inputs n search)
      (encodedEndpoint (constructedReaders n policy) q.root)
      (goal.steps.map ProviderNativeContextR57.step)
      (encodedEndpoint (constructedReaders n policy) q.target) = true ∧
    AuthenticatedResidualConsumerR49.Arrival (inputs n search)
      (encodedEndpoint (constructedReaders n policy) q.target)
      (encodedEndpoint (constructedReaders n policy) q.root) :=
  ReachedSlotCompletenessR59.complete_candidates_apply_existing_consumer
    (constructedReaders n policy) q limits r results run goal checked terminal (inputs n search)
    (concrete_local_decode n search policy)

theorem constructed_candidate_iff (n : Native S T) (policy : Policy T) (q : Query)
    (limits : Limits) (r : Resource) (results : List (Branch S T))
    (run : Run (constructedReaders n policy) q limits (.live ⟨r,[initial q],[],.pop⟩) (.success results))
    (goal : Branch S T) : goal ∈ results ↔
      Checked (constructedReaders n policy) q goal ∧ goal.endpoint = q.target :=
  ReachedSlotCompletenessR59.successful_results_exactly_checked_targets
    (constructedReaders n policy) q limits r results run goal

theorem physical_reader_independent_of_policy (n : Native S T) (first second : Policy T)
    (rowIndex : Nat) (c : Cell) :
    (constructedReaders n first).physical rowIndex c = (constructedReaders n second).physical rowIndex c := rfl

def fixturePolicy : Policy Nat := ⟨fixtureReaders.internalRoot,fixtureReaders.ancestry⟩
def failPolicy : Policy Nat :=
  ⟨fun _ => .error (nativeFailure .firstEntry .missingInternal),
    fun _ _ => .error (nativeFailure .laterAncestry .missingUseAncestry)⟩
def goodEntryPhysical : Physical Nat := fixturePhysical 4 0 0 []

theorem concrete_physical_and_policy_separation :
    readPhysical fixtureNative 4 fixtureCell = .ok goodEntryPhysical ∧
    readPhysical fixtureNative 6 fixtureCell = .ok fixtureEdge ∧
    ReachedSlotSearchR58.policy (constructedReaders fixtureNative failPolicy) .entrySearch
      (initial ⟨.row 4,.annotationMember 0 0,.entrySearch⟩) goodEntryPhysical =
      .error (nativeFailure .firstEntry .missingInternal) := ⟨rfl,rfl,rfl⟩

theorem concrete_rows_views_and_decoder :
    rows fixtureNative 4 = .ok fixtureBounds ∧ views fixtureNative 0 = .ok fixtureView ∧
    LocalDecode (constructedReaders fixtureNative fixturePolicy) (inputs fixtureNative fixtureSearch) :=
  ⟨rfl,rfl,concrete_local_decode _ _ _⟩

def staleNative : Native Nat Nat :=
  { fixtureNative with emissions :=
    [{ fixtureEmission 4 0 with readbackSlot := fixtureSlot 5 },fixtureEmission 6 1] }
def duplicateNative : Native Nat Nat :=
  { fixtureNative with emissions :=
    [{ fixtureEmission 4 0 with readbackSlot := fixtureSlot 5 },fixtureEmission 4 0,fixtureEmission 6 1] }
def wrongRelationNative : Native Nat Nat :=
  { fixtureNative with relations :=
    [⟨1,0,.effect (.row 99),.effect (.row 4)⟩,⟨1,1,.effect (.annotationMember 0 0),.effect (.row 6)⟩] }

theorem stale_duplicate_and_relation_rejected :
    readPhysical staleNative 4 fixtureCell = .error (nativeFailure .physicalOwner .boundMismatch) ∧
    readPhysical duplicateNative 4 fixtureCell = .error (nativeFailure .physicalOwner .ambiguousPhysicalSlot) ∧
    readPhysical wrongRelationNative 4 fixtureCell = .error (nativeFailure .physicalOwner .foreignRelation) :=
  ⟨rfl,rfl,rfl⟩

theorem swapped_lane_index_and_foreign_owner_rejected :
    readPhysical { fixtureNative with emissions :=
      [{ fixtureEmission 4 0 with physical := ⟨.effect 4,.effectLowerRow,0⟩ },fixtureEmission 6 1] }
      4 fixtureCell = .error (nativeFailure .physicalOwner .missingEmission) ∧
    readPhysical { fixtureNative with emissions :=
      [{ fixtureEmission 4 0 with physical := ⟨.effect 4,.effectLowerAtom,1⟩ },fixtureEmission 6 1] }
      4 fixtureCell = .error (nativeFailure .physicalOwner .missingEmission) ∧
    readPhysical { fixtureNative with emissions :=
      [{ fixtureEmission 4 0 with state := 2 },fixtureEmission 6 1] }
      4 fixtureCell = .error (nativeFailure .physicalOwner .missingEmission) ∧
    readPhysical { fixtureNative with state := 2 } 4 fixtureCell =
      .error (nativeFailure .rowLookup .boundMismatch) := ⟨rfl,rfl,rfl,rfl⟩

theorem canonical_row_and_crossed_view_unavailable :
    readPhysical fixtureNative 40 fixtureCell = .error (nativeFailure .rowLookup .boundMismatch) ∧
    views { fixtureNative with views := [{ fixtureView with state := 2 }] } 0 =
      .error (nativeFailure .viewLookup .boundMismatch) ∧
    views { fixtureNative with views := [{ fixtureView with index := 1 }] } 0 =
      .error (nativeFailure .viewLookup .boundMismatch) := ⟨rfl,rfl,rfl⟩

theorem reordered_support_member_rejected :
    ¬ AuthenticatedResidualConsumerR49.SupportReads
      (inputs { fixtureNative with views := [{ fixtureView with allowed := [11,7] }] } fixtureSearch)
      (support (S := Nat) (T := Nat) ⟨1,0,0,7,fixtureView⟩) := by decide

def rowAtomNative : Native Nat Nat :=
  { fixtureNative with effectRows := [⟨1,4,40,⟨[],[],[.row 6],[]⟩⟩] }

theorem malformed_row_atom_rejected_before_emission :
    readPhysical { rowAtomNative with emissions := [] } 4 ⟨.atom,0,.row 6⟩ =
      .error (nativeFailure .physicalOwner .boundMismatch) ∧
    readPhysical { rowAtomNative with emissions := [fixtureEmission 4 0,fixtureEmission 4 0] }
      4 ⟨.atom,0,.row 6⟩ = .error (nativeFailure .physicalOwner .boundMismatch) := ⟨rfl,rfl⟩

def openViewNative : Native Nat Nat :=
  { fixtureNative with views := [{ fixtureView with tail := some 9 }] }
def supportQuery : Query := ⟨.support 0,.annotationMember 0 0,.catchSearch⟩

theorem open_support_tail_rejected_at_search_guard :
    Run (constructedReaders openViewNative fixturePolicy) supportQuery nativeLimits
      (.live ⟨resourceAt 0 8,[initial supportQuery],[],.pop⟩)
      (.failure (nativeFailure .supportTail .missingCommonEndpoint)) :=
  .next (.failure (.tail (r' := resourceAt 2 8) (index := 0)
    (v := { fixtureView with tail := some 9 }) (by decide) rfl rfl rfl (by decide))) (.refl _)

end YulangClosure.NativeLocalDecodeR60
