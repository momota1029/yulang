import Yulang.GeneralDeclarativeI65I75ProjectedReceiptMeaning425

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
open GeneralDeclarativeI65
open Checker408 (Problem)
open Check408 (TypeWire Write)
open ExplicitPick419 (eqWrite eq_write419)
open CommonNominalFullCarrier (Ty Equivalent)

/-- A parameterized representation for an internal projected write.
This module deliberately does not register a tag in the public checker.
The ordered nodes distinguish occurrence from the two source issuer paths. -/
def encodeProjectedKey425 (tag : Nat) (key : ProjectedReceiptKey425) : TypeWire :=
  .node tag
    [key.declarationOrdinal,key.declarationId,key.associatedEquationId,key.outputOrdinal,
     key.outputName,key.fixedTarget,key.site.fieldBinder,key.site.tailBinder,key.site.label,
     key.site.lower,key.site.center,key.site.upper,key.site.fieldLower,key.site.fieldUpper,
     key.site.tailLower,key.site.tailUpper]
    [.node 0 key.occurrence [],.node 1 key.site.lowerIssuer [],.node 2 key.site.upperIssuer []]

def decodeProjectedKey425 (tag : Nat) : TypeWire → Option ProjectedReceiptKey425
  | .node actual [d,id,eqn,i,name,dest,b,t,l,lo,center,hi,fl,fh,tl,th]
      [.node 0 occ [],.node 1 lowSrc [],.node 2 highSrc []] =>
    if actual = tag then
      some ⟨occ,d,id,eqn,i,name,dest,⟨b,t,l,lo,center,hi,fl,fh,tl,th,lowSrc,highSrc⟩⟩
    else none
  | _ => none

theorem projected_wire_roundtrip425 (tag : Nat) (key : ProjectedReceiptKey425) :
    decodeProjectedKey425 tag (encodeProjectedKey425 tag key) = some key := by
  cases key with
  | mk occ decl id eqn i name out site =>
    cases site
    simp [decodeProjectedKey425,encodeProjectedKey425]

theorem decoded_projection_is_canonical_wire425 {tag : Nat} {wire : TypeWire} {key}
    (read : decodeProjectedKey425 tag wire = some key) : encodeProjectedKey425 tag key = wire := by
  unfold decodeProjectedKey425 at read
  split at read
  · split at read
    · injection read with matching
      subst key
      simp_all only [encodeProjectedKey425]
    · cases read
  · cases read

theorem projected_wire_injective425 (tag : Nat) :
    Function.Injective (encodeProjectedKey425 tag) := by
  intro a b eq
  have decoded := congrArg (decodeProjectedKey425 tag) eq
  simpa [projected_wire_roundtrip425] using decoded

/-- Old scalar, compound and native roots use tags at most 8; an
available new tag cannot be a legacy named or compound RHS. This
does not assert that any numeric tag has already been allocated. -/
theorem projected_wire_is_not_an_old_named_RHS425 {s slots c p}
    (term : NamedMixedTree401 s slots c p) {tag : Nat}
    (fresh : 8 < tag) (key : ProjectedReceiptKey425) :
    encodeProjectedKey425 tag key ≠ Check408.encodeRhs term := by
  cases term <;> intro eq <;> injection eq with contradictory <;> omega

def encodeProjectedWrite425 {p : Problem} (tag : Nat) (data : PreparedWrite p) : Write :=
  let q := p.root
  let d := data.original
  ⟨q.occurrence,d.ordinal,d.outIndex.val,q.demand.outputs[d.outIndex],.explicit d.assoc,
    encodeProjectedKey425 tag (projectedKey425 data)⟩

/-- Even if a named value is equivalent in every fit, the *actual*
legacy event serializer cannot produce this exact projected receipt.
The proof uses the existing public serialization, not a mock emitter. -/
theorem projected_receipt_cannot_be_emitted_by_old_event_wire425
    {p : Problem} (d : PreparedWrite p) {tag : Nat} (fresh : 8 < tag)
    {s q} (e : Event s q) :
    encodeProjectedWrite425 tag d ∉ Check408.encodedEventWrites e := by
  intro contained
  unfold Check408.encodedEventWrites at contained
  obtain ⟨i,found⟩ := List.mem_ofFn.mp contained
  have shape := congrArg Write.typedRhs found
  exact projected_wire_is_not_an_old_named_RHS425 (e.outputs i).rhs fresh (projectedKey425 d) shape.symm

/-- Replay the exact old outer Write shape with a new preparatory
projection payload. This is not a Result-level checker or election;
only replay of an originally retained associated output is covered. -/
def replayProjectedWrite425 (p : Problem) (tag : Nat) (wire : PrepareWire) (offered : Write) :
    Option (PreparedWrite p) := do
  if 8 < tag then
    let d ← readRetainedPickWrite423 p wire
    if eqWrite offered (encodeProjectedWrite425 tag d) then some d else none
  else none

theorem replay_projected_write_requires_exact_original_write425
    {p : Problem} {tag wire offered d} :
    replayProjectedWrite425 p tag wire offered = some d ↔
      8 < tag ∧ readRetainedPickWrite423 p wire = some d ∧
        offered = encodeProjectedWrite425 tag d := by
  unfold replayProjectedWrite425
  by_cases fresh : 8 < tag
  · cases read : readRetainedPickWrite423 p wire with
    | none => simp [fresh]
    | some actual =>
      by_cases equal : offered = encodeProjectedWrite425 tag actual
      · have compare := (eq_write419 _ _).mpr equal
        simp [fresh,compare]
        intro h
        simpa [h] using equal
      · have elsewhere : eqWrite offered (encodeProjectedWrite425 tag actual) = false := by
          cases b : eqWrite offered (encodeProjectedWrite425 tag actual) with
          | false => rfl
          | true => exact (equal ((eq_write419 _ _).mp b)).elim
        simp [fresh,elsewhere]
        intro h
        simpa [h] using equal
  · simp [fresh]

theorem replay_projected_write_keeps_actual_head_and_target425
    {p : Problem} {tag wire offered data}
    (h : replayProjectedWrite425 p tag wire offered = some data)
    (m : I72.Model) (fit : I72.Fits p.state m) :
    ∃ k : ProjectedReceiptKey425,
      decodeProjectedKey425 tag offered.typedRhs = some k ∧
      offered.occurrence = k.occurrence ∧ offered.declarationOrdinal = k.declarationOrdinal ∧
      offered.outputOrdinal = k.outputOrdinal ∧ offered.target.target = k.fixedTarget ∧
      k.OriginalSites p.state.core ∧ k.Meaning m ∧
      ∃ v : Ty, k.valueAt m = some v ∧
        data.typed.actualRightValue m =
          some (offered.occurrence,offered.declarationOrdinal,offered.outputOrdinal,offered.target.target,v) := by
  obtain ⟨fresh,original,same⟩ := replay_projected_write_requires_exact_original_write425.mp h
  subst offered
  let key := projectedKey425 data
  have verified : readProjectedReceipt425 p wire key = some data :=
    read_projected_receipt_is_exact425.mpr ⟨original,rfl⟩
  obtain ⟨meaning,v,atValue,bodyResult⟩ :=
    accepted_exact_key_denotes_full_projected_capture425 verified m fit
  exact ⟨key,projected_wire_roundtrip425 tag key,rfl,rfl,rfl,rfl,
    accepted_projected_receipt_names_both_original_endpoint_sources425 verified,
    meaning,v,atValue,bodyResult⟩

theorem replay_projected_write_keeps_literal_source_body425
    {p : Problem} {tag wire offered data}
    (h : replayProjectedWrite425 p tag wire offered = some data) :
    let key := projectedKey425 data
    offered.target.name = key.outputName ∧
    offered.body = .explicit ⟨key.associatedEquationId,key.outputName,.var key.site.fieldBinder⟩ := by
  obtain ⟨_,original,same⟩ := replay_projected_write_requires_exact_original_write425.mp h
  subst offered
  have read : readProjectedReceipt425 p wire (projectedKey425 data) = some data :=
    read_projected_receipt_is_exact425.mpr ⟨original,rfl⟩
  have shape := (accepted_key_is_exact_original_literal_field_use425 read).2.2.2.1
  exact ⟨rfl,congrArg GeneralDictionaryAssociatedProvenance.Body.explicit
    (List.cons.inj (data.original.actualAssoc.symm.trans shape)).1⟩

/-- Certificate choices do not affect the actual exact written report.
This includes the full B6 body and target, not only the projected
part of the typed wire. -/
theorem same_key_has_same_full_projected_wire425
    {p : Problem} {left right : PrepareWire} {key d e}
    (a : readProjectedReceipt425 p left key = some d)
    (b : readProjectedReceipt425 p right key = some e) (tag : Nat) :
    encodeProjectedWrite425 tag d = encodeProjectedWrite425 tag e := by
  have source := one_exact_receipt_replays_one_original_B6_term425 a b
  have first := (read_projected_receipt_is_exact425.mp a).2
  have other := (read_projected_receipt_is_exact425.mp b).2
  have same := first.trans other.symm
  simp only [encodeProjectedWrite425,source.2.2.1,source.2.2.2.1,source.2.1,same]

theorem raw_root_K2_precludes_projected_write_replay425 {p : Problem}
    (raw : RootCycle p.state p.root) (tag : Nat) (wire : PrepareWire) (offered : Write) :
    replayProjectedWrite425 p tag wire offered = none := by
  cases h : replayProjectedWrite425 p tag wire offered with
  | none => rfl
  | some accepted => exact (accepted.original.rawSafe raw).elim

end Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
