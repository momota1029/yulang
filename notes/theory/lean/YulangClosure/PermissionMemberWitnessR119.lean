import YulangClosure.NativePermissionDecoderR118

/-!
R119 CONSTRUCTED / UNCHECKED. No Lean/Lake/checker execution, printed theorem
types or axiom results have been observed. Audit commands below are future work.

This is conditional finite list mathematics, not a Rust operational model.
The capture searches the retained Permission.concrete in order; the consumer
reads that SAME permission value at that SAME captured index. Registration,
packed permission storage, native endpoint member and permission member remain
separate coordinates. Id denotes a complete resolved identity, not an index.

Rust interpretation of position/get, stable record and vector identity between
capture and consumption, owner/state/batch pointers and full operation identity
remain OPEN. Equality of Lean values does not authenticate a Rust pointer.
R39's PRE-constructor Action/row/Inputs and prepare/permissionFor equations,
and R45 extraction, remain separate OPEN premises. Post-state membership cannot
reconstruct the no-previous-registration guard. No source domain is reduced.
-/
namespace YulangClosure.PermissionMemberWitnessR119

open ComputationPermissionEntryR39

variable {Id : Type} [DecidableEq Id]

/-- Ordered first-equality search, retaining duplicates and original positions.
This is a candidate transcription of iter().position, not an authenticated one. -/
def orderedSearch : List Id → Id → Option Nat
  | [], _ => none
  | first :: rest, family =>
      if first = family then some 0
      else match orderedSearch rest family with
        | none => none
        | some index => some (Nat.succ index)

/-- Derive the actual indexed value from the successful search computation. -/
theorem search_index_read (xs : List Id) (family : Id) (member : Nat)
    (searched : orderedSearch xs family = some member) :
    xs[member]? = some family := by
  induction xs generalizing member with
  | nil => simp [orderedSearch] at searched
  | cons first rest ih =>
    by_cases same : first = family
    · have index : 0 = member := by
        simpa [orderedSearch, same] using searched
      subst member
      simp [same]
    · cases tailSearch : orderedSearch rest family with
      | none => simp [orderedSearch, same, tailSearch] at searched
      | some index =>
        have position : Nat.succ index = member := by
          simpa [orderedSearch, same, tailSearch] using searched
        subst member
        simpa using ih index tailSearch

/-- List membership is constructed from a successful indexed read. -/
theorem indexed_read_member (xs : List Id) (member : Nat) (family : Id)
    (read : xs[member]? = some family) : family ∈ xs := by
  induction xs generalizing member with
  | nil => simp at read
  | cons first rest ih =>
    cases member with
    | zero =>
      have same : first = family := by simpa using read
      subst first
      simp
    | succ index =>
      have tailRead : rest[index]? = some family := by simpa using read
      exact List.mem_cons_of_mem first (ih index tailRead)

/-- Both phases contribute: search fixes the captured identity, while the
same-record/same-index consumer read supplies its observed value. Neither
membership nor a faithful-decoder law is an input. -/
theorem same_record_search_read (permission : Permission Id)
    (searchedFamily consumedFamily : Id) (permissionMember : Nat)
    (searched : orderedSearch permission.concrete searchedFamily = some permissionMember)
    (read : permission.concrete[permissionMember]? = some consumedFamily) :
    consumedFamily = searchedFamily ∧ searchedFamily ∈ permission.concrete := by
  have expected := search_index_read permission.concrete searchedFamily permissionMember searched
  have same : consumedFamily = searchedFamily := Option.some.inj (read.symm.trans expected)
  have member := indexed_read_member permission.concrete permissionMember consumedFamily read
  exact ⟨same, same ▸ member⟩

/-- Apply the two-phase result to R118's concrete registration-keyed selection
and native family read. The permission searched and read is the selected value;
the permission member is NOT the native endpoint member or packed storage slot.
This is only the finite read consequence, not successful Suppress/extract. -/
theorem selected_retained_member
    (views : List (Nat × List Id)) (permissions : List (Nat × Permission Id))
    (endpoint : NativePermissionDecoderR118.Endpoint)
    (registration storage permissionMember : Nat)
    (permission : Permission Id) (providerFamily consumedFamily : Id)
    (nativeRead : NativePermissionDecoderR118.readFamily views endpoint = some providerFamily)
    (retainedRead : NativePermissionDecoderR118.readPermission permissions registration storage =
      some permission)
    (searched : orderedSearch permission.concrete providerFamily = some permissionMember)
    (consumerRead : permission.concrete[permissionMember]? = some consumedFamily) :
    (∃ allowed, views[endpoint.view]? = some (endpoint.view, allowed) ∧
      allowed[endpoint.member]? = some providerFamily) ∧
    NativePermissionDecoderR118.matching permissions registration = [(storage, permission)] ∧
    consumedFamily = providerFamily ∧ providerFamily ∈ permission.concrete := by
  have joined := same_record_search_read permission providerFamily consumedFamily
    permissionMember searched consumerRead
  exact ⟨NativePermissionDecoderR118.read_family_exact views endpoint providerFamily nativeRead,
    NativePermissionDecoderR118.read_permission_exact permissions registration storage permission
      retainedRead, joined.1, joined.2⟩

/-- Conditional application to the SAME R45 output permission. This does not
construct extract's owning reads or R39's PRE-constructor event. -/
theorem certificate_member_if_extracted {Artifact Term Fact : Type}
    [DecidableEq Artifact] [DecidableEq Term] [DecidableEq Fact]
    (e : InternalPermissionIncidenceR45.Inputs Artifact Id Term Fact)
    (q : InternalPermissionIncidenceR45.Query Artifact Id)
    (probe : InternalPermissionIncidenceR45.Probe Artifact Id Term Fact)
    (out : InternalPermissionIncidenceR45.Certificate Artifact Id Term Fact)
    (providerFamily consumedFamily : Id) (permissionMember : Nat)
    (accepted : InternalPermissionIncidenceR45.extract e q probe = some out)
    (searched : orderedSearch probe.permission.concrete providerFamily = some permissionMember)
    (consumerRead : probe.permission.concrete[permissionMember]? = some consumedFamily) :
    providerFamily ∈ out.permission.concrete := by
  have member := (same_record_search_read probe.permission providerFamily consumedFamily
    permissionMember searched consumerRead).2
  have same := (InternalPermissionIncidenceR45.accepted_payload e q probe out accepted).1
  rw [same]
  exact member

/-- A duplicate family retains its first position; registration 7 is in packed
slot 0, permission member 1 names family 9, and native member 0 also names 9. -/
def examplePermission : Permission Nat :=
  { NativePermissionDecoderR118.examplePermission with registration := 7, concrete := [4, 9, 9] }

theorem distinct_coordinates_and_duplicates :
    orderedSearch examplePermission.concrete 9 = some 1 ∧
    examplePermission.concrete[1]? = some 9 ∧
    NativePermissionDecoderR118.readPermission [(0, examplePermission)] 7 0 =
      some examplePermission ∧
    NativePermissionDecoderR118.readFamily [(0, [9])] ⟨0, 0⟩ = some 9 ∧
    (7 : Nat) ≠ 0 ∧ (1 : Nat) ≠ 7 ∧ (1 : Nat) ≠ 9 := by decide

end YulangClosure.PermissionMemberWitnessR119

-- Future audits only. No output or axiom list has been observed.
#check @YulangClosure.PermissionMemberWitnessR119.search_index_read
#print axioms YulangClosure.PermissionMemberWitnessR119.search_index_read
#check @YulangClosure.PermissionMemberWitnessR119.indexed_read_member
#print axioms YulangClosure.PermissionMemberWitnessR119.indexed_read_member
#check @YulangClosure.PermissionMemberWitnessR119.same_record_search_read
#print axioms YulangClosure.PermissionMemberWitnessR119.same_record_search_read
#check @YulangClosure.PermissionMemberWitnessR119.selected_retained_member
#print axioms YulangClosure.PermissionMemberWitnessR119.selected_retained_member
#check @YulangClosure.PermissionMemberWitnessR119.certificate_member_if_extracted
#print axioms YulangClosure.PermissionMemberWitnessR119.certificate_member_if_extracted
#check @YulangClosure.PermissionMemberWitnessR119.distinct_coordinates_and_duplicates
#print axioms YulangClosure.PermissionMemberWitnessR119.distinct_coordinates_and_duplicates
