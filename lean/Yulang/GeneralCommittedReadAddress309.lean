import Yulang.GeneralCommittedReadTrace309

namespace Yulang.GeneralCommittedReadAddress309
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedEvidence231 (Certificate)
open GeneralNominalCenteredHeadAllocEncoding renaming registry → compileRegistry
open GeneralGeneratedDictionaryRun299 (Entry Read)
open GeneralCommittedReadTrace309 (Trace FrameProof)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Plan)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls} {r : Registry} {s : State roles} {root : Occurrence roles}
variable {m : Assignment} {read : Read} {decode : Nat → Occurrence roles}

def cursor (read : Read) (start : Nat) : List Nat → Option Nat
  | [] => some start
  | pos::ps => do
    let row ← read start
    let sub ← row.children[pos]?
    cursor read sub ps

def subtree (d : Payload) : List Nat → Option Payload
  | [] => some d
  | pos::ps => do
    let picked ← (match d with | .node _ ds => ds[pos]?)
    subtree picked ps

theorem there_left {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (paired : All₂ R xs ys) (p : Nat) (x : α) (atLeft : xs[p]? = some x) :
    ∃ y, ys[p]? = some y ∧ R x y := by
  induction paired generalizing p with
  | nil => simp at atLeft
  | cons h t ih =>
    cases p with
    | zero =>
      have eq := Option.some.inj atLeft
      cases eq
      exact ⟨_,rfl,h⟩
    | succ p => exact ih p atLeft

theorem there_right {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (paired : All₂ R xs ys) (p : Nat) (y : β) (atRight : ys[p]? = some y) :
    ∃ x, xs[p]? = some x ∧ R x y := by
  induction paired generalizing p with
  | nil => simp at atRight
  | cons h t ih =>
    cases p with
    | zero =>
      have eq := Option.some.inj atRight
      cases eq
      exact ⟨_,rfl,h⟩
    | succ p => exact ih p atRight

/-- A positional cursor walk in the verified table and the corresponding
payload walk succeed or fail together. At any successful address, there is
a subtrace for exactly that occurrence and payload; no de-duplication or
cross-branch search occurs. -/
theorem address (ps : List Nat) {i : Nat} {d : Payload}
    (trace : Trace r s root m read decode i d) :
    (∃ j e, cursor read i ps = some j ∧ subtree d ps = some e ∧ Trace r s root m read decode j e) ∨
    (cursor read i ps = none ∧ subtree d ps = none) := by
  induction ps generalizing i d with
  | nil => exact .inl ⟨i,d,rfl,rfl,trace⟩
  | cons p ps ih =>
    cases trace with
    | node i row ds _ frame child =>
      have readback := frame.1
      cases found : row.children[p]? with
      | none =>
        have missing : ds[p]? = none := by
          cases present : ds[p]? with
          | none => rfl
          | some e =>
            obtain ⟨j,hit,_⟩ := there_right child p e present
            rw [found] at hit
            cases hit
        exact .inr ⟨by simp [cursor,readback,found],by simp [subtree,missing]⟩
      | some j =>
        obtain ⟨e,seen,proof⟩ := there_left child p j found
        rcases ih proof with ⟨last,out,walk,part,support⟩|⟨none,payloadNone⟩
        · exact .inl ⟨last,out,by simpa [cursor,readback,found] using walk,
            by simpa [subtree,seen] using part,support⟩
        · exact .inr ⟨by simpa [cursor,readback,found] using none,
            by simpa [subtree,seen] using payloadNone⟩

theorem subtrace {ps : List Nat} {i j : Nat} {d e : Payload}
    (trace : Trace r s root m read decode i d)
    (walk : cursor read i ps = some j) (part : subtree d ps = some e) :
    Trace r s root m read decode j e := by
  rcases address ps trace with ⟨k,out,seen,picked,proof⟩|⟨missing,_⟩
  · cases Option.some.inj (walk.symm.trans seen)
    cases Option.some.inj (part.symm.trans picked)
    exact proof
  · rw [walk] at missing
    cases missing

theorem here {i : Nat} {d : Payload} (trace : Trace r s root m read decode i d) :
    GeneralNominalSaturationState.Generated s.core.erased.current root (decode i) ∧
    ∃ e ds, FrameProof r s m read decode i e ∧ d = .node e.key ds := by
  cases trace with
  | node i e ds reached proof below => exact ⟨reached,e,ds,proof,rfl⟩

end Yulang.GeneralCommittedReadAddress309
