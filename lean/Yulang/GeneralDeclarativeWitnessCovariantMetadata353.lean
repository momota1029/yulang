import Yulang.GeneralDeclarativeWitnessCovariantHead352
import Yulang.GeneralSourceMetadataBareBundle291

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCovariantMetadata353
open GeneralSourceMetadataBareBundle291 (InputBundle compile)
open GeneralSourceMetadataBundle291 (SourceBundle)
open GeneralSourceMetadataRows291 (Row Source)
open CommonDeclaredNominalInspection (Parameter Registry)
open GeneralDeclarationPatterns (Constructor)

deriving instance DecidableEq for Constructor
open GeneralDeclarativeWitnessCovariant352 (covariant)

structure Declaration where
  key : Nat
  parameters : List Parameter
  deriving DecidableEq

/-- Syntax and variance are independent input, not solver proof bits. -/
structure Input where
  sourceInput : InputBundle
  variance : List Declaration

def findRow (s : Source) (key : Nat) : Option Row := s.rows.find? (fun row => row.key == key)

def inactive (s : Source) : Bool :=
  (match s.fallback with | .absent => true | .identityEmptyLayout => false) &&
    decide (s.rows.map Row.key).Nodup

def table (key : Nat) : Registry := List.replicate key [] ++ [covariant]

theorem table_key (key : Nat) : (table key)[key]? = some covariant := by
  rw [table,List.getElem?_append_right (by simp)]
  simp

structure Checked (p : Input) (key : Nat) where
  source : SourceBundle
  assembled : compile p.sourceInput = some source
  declared : Row
  snapshot : Row
  declared_row : findRow source.declared key = some declared
  snapshot_row : findRow source.snapshot key = some snapshot
  declared_shape : declared.ctor = some ⟨[.type],key⟩
  snapshot_shape : snapshot.ctor = some ⟨[.type],key⟩
  declared_unclassified : declared.classification = .unclassified
  snapshot_unclassified : snapshot.classification = .unclassified
  authoredMode : p.variance = [⟨key,covariant⟩]

def unclassified : GeneralSourceMetadataRows291.Class → Bool
  | .unclassified => true
  | _ => false

theorem unclassified_exact {c : GeneralSourceMetadataRows291.Class} (h : unclassified c = true) :
    c = .unclassified := by cases c <;> cases h <;> rfl

def check (p : Input) (key : Nat) : Option (Checked p key) :=
  match assembled : compile p.sourceInput with
  | none => none
  | some source =>
    if inactive source.declared && inactive source.snapshot then
      match d : findRow source.declared key, w : findRow source.snapshot key with
      | some r,some s =>
        if dr : r.ctor = some ⟨[.type],key⟩ then
          if sr : s.ctor = some ⟨[.type],key⟩ then
            if du : unclassified r.classification = true then
              if su : unclassified s.classification = true then
                if real : p.variance = [⟨key,covariant⟩] then
                  some ⟨source,assembled,r,s,d,w,dr,sr,unclassified_exact du,unclassified_exact su,real⟩
                else none
              else none
            else none
          else none
        else none
      | _,_ => none
    else none

theorem author_not_fallback {p : Input} {key : Nat} (certificate : Checked p key) :
    certificate.declared ∈ certificate.source.declared.rows ∧
    certificate.snapshot ∈ certificate.source.snapshot.rows ∧
    p.variance = [⟨key,covariant⟩] :=
  ⟨List.mem_of_find?_eq_some certificate.declared_row,
   List.mem_of_find?_eq_some certificate.snapshot_row,certificate.authoredMode⟩

end Yulang.GeneralDeclarativeWitnessCovariantMetadata353
