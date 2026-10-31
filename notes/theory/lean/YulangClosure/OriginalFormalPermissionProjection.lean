import Std

/-!
Structural slice of `shadow_apply.rs:2638–2696`, pinned by
FORMAL-PERMISSION-PROJECTION-20261028/r1. This is not the original effect
hygiene theorem. Annotation policy is the Authoritative 2026-10-10 integration
note §§1–1.2 (including the October 15/16 corrections).

`walk` models lookup through already captured nodes, including failure. Node
polarity is retained but not inspected, exactly as the exporter. Tuple storage
uses mathematical natural addresses; native checked overflow is an additional
failure before this slice. Other graph node constructors are `other`, since
all reject at every nonempty structural path. Row keys and metadata are opaque
identities, never inferred from concrete family equality.

No theorem assumes capture preservation or claims the Rust capture constructs
this graph. `unrelated_capture_can_succeed` demonstrates why exporter success
alone cannot establish that missing bridge. This is a countermodel to that
logical implication, not a source-qualified Rust counterexample.
-/
namespace YulangClosure.OriginalFormalPermissionProjection

inductive Step where
  | argument | result | element (index : Nat)
  deriving DecidableEq, Repr

inductive Node where
  | function (positive : Bool) (argument argumentEffect resultEffect result : Nat)
  | tuple (positive : Bool) (start length : Nat)
  | row (positive : Bool) (key : Nat) (effect : Bool)
  | other
  deriving DecidableEq, Repr

structure Graph where
  nodes : Nat → Option Node
  tupleChildren : Nat → Option Nat
  negativeRoots : Nat → Option Nat

/-- Final Function steps select effects; intermediate steps select values.
An Element can never be a final step. -/
def walk (g : Graph) (current : Nat) : List Step → Option Nat
  | [] => none
  | step :: rest =>
    match g.nodes current, step with
    | some (.function _ a ae _re _r), .argument =>
        match rest with
        | [] => some ae
        | _ :: _ => walk g a rest
    | some (.function _ _a _ae re r), .result =>
        match rest with
        | [] => some re
        | _ :: _ => walk g r rest
    | some (.tuple _ start len), .element index =>
        if index < len then
          match rest with
          | [] => none
          | _ :: _ => (g.tupleChildren (start + index)).bind (fun child => walk g child rest)
        else none
    | _, _ => none

def effectPort (g : Graph) (root : Nat) (path : List Step) : Option Nat := do
  let current ← g.negativeRoots root
  let port ← walk g current path
  match g.nodes port with
  | some (.row _ _ true) => some port
  | _ => none

/-- Opaque IDs stand for the complete parameter, HIR occurrence, owner, scope,
source-row and resolved concrete operand records, without quotienting them. -/
structure Permission where
  parameter : Nat
  occurrence : Nat
  owner : Nat
  scope : Nat
  sourceRow : Nat
  concrete : List Nat
  path : List Step
  deriving DecidableEq, Repr

structure Exported where
  permission : Permission
  port : Nat
  deriving DecidableEq, Repr

def project (g : Graph) (domains : Nat → Option Nat) (p : Permission) : Option Exported := do
  let root ← domains p.parameter
  let port ← effectPort g root p.path
  pure ⟨p, port⟩

/-- All-or-error list projection, after the exporter's source-owner filter. -/
def projectAll (g : Graph) (domains : Nat → Option Nat) : List Permission → Option (List Exported)
  | [] => some []
  | p :: ps => do
    let exported ← project g domains p
    let rest ← projectAll g domains ps
    pure (exported :: rest)

theorem function_argument (g : Graph) (n a ae re r : Nat) (polarity : Bool)
    (node : g.nodes n = some (.function polarity a ae re r)) :
    walk g n [.argument] = some ae := by simp [walk, node]

theorem function_result (g : Graph) (n a ae re r : Nat) (polarity : Bool)
    (node : g.nodes n = some (.function polarity a ae re r)) :
    walk g n [.result] = some re := by simp [walk, node]

theorem function_nested (g : Graph) (n a ae re r : Nat) (polarity : Bool)
    (step : Step) (tail : List Step)
    (node : g.nodes n = some (.function polarity a ae re r)) :
    walk g n (.argument :: step :: tail) = walk g a (step :: tail) ∧
    walk g n (.result :: step :: tail) = walk g r (step :: tail) := by
  simp [walk, node]

theorem tuple_element (g : Graph) (n start len index child : Nat) (polarity : Bool)
    (step : Step) (tail : List Step)
    (node : g.nodes n = some (.tuple polarity start len))
    (within : index < len) (stored : g.tupleChildren (start + index) = some child) :
    walk g n (.element index :: step :: tail) = walk g child (step :: tail) := by
  simp [walk, node, within, stored]

theorem tuple_final_rejected (g : Graph) (n index : Nat) :
    walk g n [.element index] = none := by
  cases h : g.nodes n with
  | none => simp [walk, h]
  | some node => cases node <;> simp [walk, h]

theorem missing_root_rejected (g : Graph) (root : Nat) (path : List Step)
    (missing : g.negativeRoots root = none) : effectPort g root path = none := by
  simp [effectPort, missing]

theorem export_provenance (g : Graph) (domains : Nat → Option Nat)
    (p : Permission) (out : Exported) (success : project g domains p = some out) :
    out.permission = p ∧ ∃ root current polarity key,
      domains p.parameter = some root ∧ g.negativeRoots root = some current ∧
      walk g current p.path = some out.port ∧
      g.nodes out.port = some (.row polarity key true) := by
  unfold project effectPort at success
  cases domain : domains p.parameter with
  | none => simp [domain] at success
  | some root =>
    cases captured : g.negativeRoots root with
    | none => simp [domain, captured] at success
    | some current =>
      cases walked : walk g current p.path with
      | none => simp [domain, captured, walked] at success
      | some port =>
        cases found : g.nodes port with
        | none => simp [domain, captured, walked, found] at success
        | some node =>
          cases node with
          | function => simp [domain, captured, walked, found] at success
          | tuple => simp [domain, captured, walked, found] at success
          | other => simp [domain, captured, walked, found] at success
          | row polarity key effect =>
            cases effect with
            | false => simp [domain, captured, walked, found] at success
            | true =>
              simp [domain, captured, walked, found] at success
              cases success
              exact ⟨rfl, root, current, polarity, key, rfl, captured, walked, found⟩

theorem list_export_provenance (g : Graph) (domains : Nat → Option Nat)
    (ps : List Permission) (outs : List Exported)
    (success : projectAll g domains ps = some outs) :
    outs.map Exported.permission = ps := by
  induction ps generalizing outs with
  | nil => simp [projectAll] at success; subst outs; rfl
  | cons p ps ih =>
    cases first : project g domains p with
    | none => simp [projectAll, first] at success
    | some out =>
      cases remaining : projectAll g domains ps with
      | none => simp [projectAll, first, remaining] at success
      | some rest =>
        simp [projectAll, first, remaining] at success
        subst outs
        simp [(export_provenance g domains p out first).1, ih rest remaining]

/-- A graph with an unrelated row can pass every export check. Thus no theorem
about original constructor identity follows merely from export success. -/
def unrelatedGraph : Graph :=
  { nodes := fun n => if n = 0 then some (.function false 0 1 1 0)
                       else if n = 1 then some (.row false 99 true) else none
    tupleChildren := fun _ => none
    negativeRoots := fun _ => some 0 }

def samplePermission : Permission := ⟨7, 11, 13, 17, 19, [23], [.result]⟩

theorem unrelated_capture_can_succeed :
    project unrelatedGraph (fun _ => some 29) samplePermission =
      some ⟨samplePermission, 1⟩ ∧ (1 : Nat) ≠ 2 := by
  decide

/-- Shared/merged rows do not erase distinct source records, even when both
permissions resolve to exactly the same graph node and concrete family list. -/
theorem equal_family_distinct_occurrences :
    let p := samplePermission
    let q := {p with occurrence := 12, sourceRow := 20}
    projectAll unrelatedGraph (fun _ => some 29) [p, q] =
      some [⟨p, 1⟩, ⟨q, 1⟩] ∧ p.concrete = q.concrete ∧ p ≠ q := by
  decide

end YulangClosure.OriginalFormalPermissionProjection
