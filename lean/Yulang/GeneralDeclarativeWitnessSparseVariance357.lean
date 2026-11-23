import Yulang.CommonDeclarationVarianceLowering
import Yulang.CommonDeclarationVarianceTable
import Yulang.CommonDeclarationVarianceExamples

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessSparseVariance357
open CommonNominalFieldTemplates (Body)
open CommonDeclarationVarianceSyntax (Program Expr)
open CommonDeclarationVarianceLowering (lower Lowered Scope lower_exact)
open CommonDeclarationVarianceOccurrences (Universe)
open CommonDeclarationVarianceTable (deriveVariance derive_variance_exact TableJudgment)
open CommonDeclaredNominalInspection (Parameter Kind)
open CommonDeclaredNominalVariance (Variance)

structure Header (count : Nat) where
  name : Nat
  written : List (Kind × Fin count)
  deriving DecidableEq

def entry {count : Nat} (headers : List (Header count)) (name : Nat) : Option (Header count) :=
  headers.find? (fun h => h.name == name)

def kindAt {types rows : Nat} (p : Fin (types+rows)) : Kind :=
  if p.val < types then .value else .row

structure Source (nodes types rows : Nat) where
  headers : List (Header (types+rows))
  bodies : Fin nodes → Body nodes types rows
  roots : Fin (types+rows) → Fin nodes

def scope (nodes types rows : Nat) : Scope (Fin nodes) (Fin (types+rows)) nodes types rows :=
  ⟨id,Fin.castAdd rows,Fin.natAdd types⟩

def wellFormed {nodes types rows} (s : Source nodes types rows) : Prop :=
  let formals := s.headers.flatMap (List.map Prod.snd ∘ Header.written)
  (s.headers.map Header.name).Nodup ∧ formals.Nodup ∧
    (∀ p : Fin (types+rows),p ∈ formals) ∧
    s.headers.all (fun h => h.written.all fun q => decide (q.1 = kindAt q.2)) = true

def valid {nodes types rows} (s : Source nodes types rows) : Bool :=
  let formals := s.headers.flatMap (List.map Prod.snd ∘ Header.written)
  decide ((s.headers.map Header.name).Nodup ∧ formals.Nodup) &&
  (List.finRange (types+rows)).all (fun p => decide (p ∈ formals)) &&
  s.headers.all (fun h => h.written.all fun q => decide (q.1 = kindAt q.2))

theorem valid_iff {nodes types rows} (s : Source nodes types rows) :
    valid s = true ↔ wellFormed s := by
  simp [valid,wellFormed,List.all_eq_true,and_assoc]

def tryLower {nodes types rows} (s : Source nodes types rows) (i : Fin nodes) :
    Option (Expr (Fin nodes) (Fin (types+rows))) :=
  lower (scope nodes types rows) (fun n => (entry s.headers n).map Header.written) (s.bodies i)

structure Made {nodes types rows} (s : Source nodes types rows) where
  program : Program (Fin nodes) (Fin (types+rows))
  root : program.root = s.roots
  fromBodies : ∀ i, tryLower s i = some (program.body i)
  headers : wellFormed s

def compile {nodes types rows} (s : Source nodes types rows) : Option (Made s) :=
  if ok : valid s = true then
    if allGood : (List.finRange nodes).all (fun i => (tryLower s i).isSome) = true then
      let seen := fun i => List.all_eq_true.mp allGood i (List.mem_finRange i)
      let body := fun i => (tryLower s i).get (seen i)
      some ⟨⟨body,s.roots⟩,rfl,fun i => by
        change tryLower s i = some ((tryLower s i).get (seen i))
        exact (Option.some_get (seen i)).symm,
        (valid_iff s).mp ok⟩
    else none
  else none

abbrev Values (count : Nat) := List (Fin count × Variance)

def variance {nodes types rows} {s : Source nodes types rows} (checked : Made s) : Values (types+rows) :=
  deriveVariance checked.program (CommonDeclarationVarianceExamples.pool nodes (types+rows))

theorem uses_sources {nodes types rows} {s : Source nodes types rows} (c : Made s) (i : Fin nodes) :
    Lowered (scope nodes types rows) (fun n => (entry s.headers n).map Header.written)
      (s.bodies i) (c.program.body i) :=
  (lower_exact ..).mp (c.fromBodies i)

theorem modes_from_source {nodes types rows} {s : Source nodes types rows} (c : Made s) :
    TableJudgment c.program (List.finRange (types+rows)) (variance c) :=
  (derive_variance_exact c.program (CommonDeclarationVarianceExamples.pool nodes (types+rows)) (variance c)).mp rfl

def modeOf {count : Nat} (vs : Values count) (p : Fin count) : Option Variance :=
  (vs.find? (fun q => q.1 == p)).map Prod.snd

def parameters {count : Nat} (vs : Values count) : List (Kind × Fin count) → Option (List Parameter)
  | [] => some []
  | (kind,p) :: tail => do
    let v ← modeOf vs p
    let more ← parameters vs tail
    pure (⟨kind,v⟩ :: more)

def lookup {nodes types rows} {s : Source nodes types rows} (c : Made s) (name : Nat) :
    Option (List Parameter) := do
  let row ← entry s.headers name
  parameters (variance c) row.written

theorem none_if_absent {nodes types rows} {s : Source nodes types rows} (c : Made s) {name : Nat}
    (missing : entry s.headers name = none) : lookup c name = none := by
  simp [lookup,missing]

theorem some_if_nullary {nodes types rows} {s : Source nodes types rows} (c : Made s) {name row}
    (found : entry s.headers name = some row) (empty : row.written = []) : lookup c name = some [] := by
  simp [lookup,found,empty,parameters]

theorem lookup_authored {nodes types rows} {s : Source nodes types rows} (c : Made s) {name vs}
    (found : lookup c name = some vs) :
    ∃ row ∈ s.headers, row.name = name ∧ entry s.headers name = some row ∧
      parameters (variance c) row.written = some vs := by
  unfold lookup at found
  cases h : entry s.headers name with
  | none => simp [h] at found
  | some row =>
    have test : (row.name == name) = true := List.find?_some (p := fun h : Header (types+rows) => h.name == name) h
    exact ⟨row,List.mem_of_find?_eq_some h,beq_iff_eq.mp test,rfl,(by simpa [h] using found)⟩

end Yulang.GeneralDeclarativeWitnessSparseVariance357
