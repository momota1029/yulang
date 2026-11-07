import Yulang.CommonSymbolicProfileSupport

/-!
# Reconstructing finite primitive tables from shared common nodes

An auxiliary table may assign guards, projected payloads and ordinary children
independently. Such a table is not automatically realizable. `CoherentAt`
requires every referenced entry to agree with the independent interpretation
of one shared node assignment. Only the finite declared support is checked.

Exact reconstruction and arbitrary-assignment support congruence are proved
below. They specify the obligation of a future projection-family solver;
they do not provide an unconstrained solution of that obligation.
-/

namespace Yulang.CommonSymbolicProfileCoherence

open Common (Ty Row)
open CommonPayloadProjection (Payload)
open CommonSymbolicRecordProfiles
open CommonSymbolicProfileSupport
open CommonSymbolicSourceProfiles (compileNode)
open PresenceOpenTailGenerationLowering (Pool)
open Core.PresenceGeneration (TyTerm)

universe u v

structure Tables (Node : Type u) (Child : Type v) where
  guards : GuardAtom Node → Bool
  projections : Query Node → Option Ty
  children : Child → Ty

def Tables.canonical (nodes : Node → Ty) (children : Child → Ty) : Tables Node Child where
  guards := fun query => query.eval nodes
  projections := fun query => query.kind.eval query.hidden query.label (nodes query.node)
  children := children

def Agrees (first last : Tables Node Child) (references : List (Reference Node Child)) : Prop :=
  ∀ reference ∈ references, match reference with
    | .guard query => first.guards query = last.guards query
    | .projection query => first.projections query = last.projections query
    | .payload child => first.children child = last.children child

/-- All entries refer back to the same `nodes` and `children`. In the actual
source specialization those two interpretations are the same shared values. -/
def CoherentAt (nodes : Node → Ty) (children : Child → Ty) (tables : Tables Node Child)
    (references : List (Reference Node Child)) : Prop :=
  Agrees tables (Tables.canonical nodes children) references

theorem canonical_coherent (nodes : Node → Ty) (children : Child → Ty)
    (references : List (Reference Node Child)) :
    CoherentAt nodes children (Tables.canonical nodes children) references := by
  intro reference _
  cases reference <;> rfl

theorem agrees_append (first last : Tables Node Child) (before after : List (Reference Node Child)) :
    Agrees first last (before ++ after) ↔ Agrees first last before ∧ Agrees first last after := by
  simp only [Agrees, List.mem_append, or_imp, forall_and]

theorem agrees_restrict (first last : Tables Node Child) (before after : List (Reference Node Child))
    (contained : Fits (fun reference => reference ∈ after) before) (same : Agrees first last after) :
    Agrees first last before := fun reference member => same reference (contained reference member)

def evalBool (tables : Tables Node Child) : BoolExpr Node → Bool
  | .literal value => value
  | .atom query => tables.guards query
  | .and first last => evalBool tables first && evalBool tables last
  | .or first last => evalBool tables first || evalBool tables last
  | .not source => !evalBool tables source

def evalProfile (tables : Tables Node Child) : ProfileExpr Node Child → Option Ty
  | .none => none
  | .some payload => some (payload.evalLayer tables.children)
  | .project kind hidden label node => tables.projections ⟨kind, hidden, label, node⟩
  | .both first last => bothTypes (evalProfile tables first) (evalProfile tables last)
  | .either first last => eitherTypes (evalProfile tables first) (evalProfile tables last)
  | .withTrivial source => withTrivialType (evalProfile tables source)
  | .ite condition yes no => if evalBool tables condition then evalProfile tables yes else evalProfile tables no

def evalSummary (tables : Tables Node Child) (summary : Summary Node Child) : Meaning :=
  ⟨evalBool tables summary.records, evalBool tables summary.outsideRecords, evalBool tables summary.present,
    evalBool tables summary.initialField, evalBool tables summary.initialOptional,
    evalProfile tables summary.field, evalProfile tables summary.optional⟩

theorem payload_agrees (first last : Tables Node Child) (payload : Payload Child)
    (same : Agrees first last (payloadReferences payload)) :
    payload.evalLayer first.children = payload.evalLayer last.children := by
  induction payload with
  | ref child => exact same (.payload child) (by simp [payloadReferences])
  | bottom | top => rfl
  | union a b before after | inter a b before after =>
      have parts := (agrees_append first last _ _).mp same
      simp only [Payload.evalLayer, before parts.1, after parts.2]

theorem bool_agrees (first last : Tables Node Child) (expression : BoolExpr Node)
    (same : Agrees first last (boolReferences expression)) :
    evalBool first expression = evalBool last expression := by
  induction expression with
  | literal => rfl
  | atom query => exact same (.guard query) (by simp [boolReferences])
  | and a b before after | or a b before after =>
      have parts := (agrees_append first last _ _).mp same
      simp only [evalBool, before parts.1, after parts.2]
  | not source ih => exact congrArg Bool.not (ih same)

theorem profile_agrees (first last : Tables Node Child) (expression : ProfileExpr Node Child)
    (same : Agrees first last (profileReferences expression)) :
    evalProfile first expression = evalProfile last expression := by
  induction expression with
  | none => rfl
  | some payload => exact congrArg some (payload_agrees first last payload same)
  | project kind hidden label node => exact same (.projection ⟨kind, hidden, label, node⟩) (by simp [profileReferences])
  | both a b before after | either a b before after =>
      have parts := (agrees_append first last _ _).mp same
      simp only [evalProfile, before parts.1, after parts.2]
  | withTrivial source ih => exact congrArg withTrivialType (ih same)
  | ite condition yes no before after =>
      have parts : Agrees first last (boolReferences condition) ∧
          Agrees first last (profileReferences yes) ∧ Agrees first last (profileReferences no) := by
        simpa only [profileReferences, agrees_append, and_assoc] using same
      simp only [evalProfile, bool_agrees first last condition parts.1,
        before parts.2.1, after parts.2.2]

/-- Entries outside a finite syntactic support have no effect on any compiled
guard, profile or payload. This permits a genuinely finite table representation. -/
theorem summary_agrees (first last : Tables Node Child) (summary : Summary Node Child)
    (same : Agrees first last (summaryReferences summary)) :
    evalSummary first summary = evalSummary last summary := by
  unfold evalSummary
  congr 1
  all_goals first
    | apply bool_agrees
    | apply profile_agrees
  all_goals intro reference member; exact same reference (by simp [summaryReferences, member])

theorem evalBool_canonical (nodes : Node → Ty) (children : Child → Ty) (expression : BoolExpr Node) :
    evalBool (Tables.canonical nodes children) expression = expression.eval nodes := by
  induction expression <;> simp_all [evalBool, BoolExpr.eval, Tables.canonical]

theorem evalProfile_canonical (nodes : Node → Ty) (children : Child → Ty) (expression : ProfileExpr Node Child) :
    evalProfile (Tables.canonical nodes children) expression = expression.eval nodes children := by
  induction expression <;> simp_all only [evalProfile, ProfileExpr.eval, evalBool_canonical]
  all_goals rfl

theorem evalSummary_canonical (nodes : Node → Ty) (children : Child → Ty) (summary : Summary Node Child) :
    evalSummary (Tables.canonical nodes children) summary = summary.eval nodes children := by
  simp only [evalSummary, Summary.eval, evalBool_canonical, evalProfile_canonical]

theorem coherent_reconstruction (nodes : Node → Ty) (children : Child → Ty)
    (tables : Tables Node Child) (summary : Summary Node Child)
    (coherent : CoherentAt nodes children tables (summaryReferences summary)) :
    evalSummary tables summary = summary.eval nodes children :=
  (summary_agrees tables (Tables.canonical nodes children) summary coherent).trans
    (evalSummary_canonical nodes children summary)

variable {m : Nat}

/-- The finite eight-reference-kinds-per-node table suffices for this fixed query.
The explicit coherence premise is about one shared original assignment. -/
theorem compileNode_reconstruction (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (hidden : List Nat) (label : Nat) (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (tables : Tables (Fin pool.size) (Fin pool.size))
    (coherent : CoherentAt values values tables (poolUniverse pool hidden label)) :
    evalSummary tables (compileNode pool hidden label term member) =
      meaning hidden label ((CommonPresenceConstraintGraph.lowerNode pool term member).eval rows values) := by
  have localCoherence := agrees_restrict tables (Tables.canonical values values) _ _
    (compileNode_pool_support pool term member hidden label) coherent
  exact (coherent_reconstruction values values tables _ localCoherence).trans
    (CommonSymbolicSourceProfiles.compileNode_exact pool hidden label term member rows values)

theorem pool_payload_reconstruction (pool : Pool m) (hidden : List Nat) (label : Nat)
    (values : Fin pool.size → Ty) (tables : Tables (Fin pool.size) (Fin pool.size))
    (coherent : CoherentAt values values tables (poolUniverse pool hidden label))
    (payload : Payload (Fin pool.size)) :
    payload.evalLayer tables.children = payload.evalLayer values := by
  have each (node : Fin pool.size) : tables.children node = values node :=
    coherent (.payload node) (payload_mem_poolUniverse pool hidden label node)
  induction payload <;> simp_all [Payload.evalLayer]

/-- Even required-target discharge is sound for an auxiliary table only once
its finite primitive entries are tied to the same original common values. -/
theorem coherent_required_exact (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (label : Nat) (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (tables : Tables (Fin pool.size) (Fin pool.size))
    (coherent : CoherentAt values values tables (poolUniverse pool [] label))
    (payload : Payload (Fin pool.size)) :
    Common.Subtype ((CommonPresenceConstraintGraph.lowerNode pool term member).eval rows values)
        (Common.required label (payload.evalLayer values)) ↔
      CommonPayloadProjection.ProfileBelow
        (evalProfile tables (compileNode pool [] label term member).field) (payload.evalLayer tables.children) := by
  have field := congrArg Meaning.field (compileNode_reconstruction pool term member [] label rows values tables coherent)
  change evalProfile tables (compileNode pool [] label term member).field = _ at field
  rw [field, pool_payload_reconstruction pool [] label values tables coherent]
  exact CommonRecordTargetProfiles.subtype_required_iff _ _ label

/-- Independent projection parameters can falsely satisfy a required-field
constraint for a scalar. Their reconstruction cannot be omitted. -/
theorem independent_projection_not_sound :
    ∃ nodes : Unit → Ty, ∃ tables : Tables Unit Unit,
      CommonPayloadProjection.ProfileBelow
          (evalProfile tables (.project .field [] 0 ())) .bottom ∧
        ¬ Common.Subtype (nodes ()) (Common.required 0 .bottom) := by
  let nodes : Unit → Ty := fun _ => .base .int
  let tables : Tables Unit Unit := ⟨fun _ => true, fun _ => some .bottom, fun _ => .bottom⟩
  refine ⟨nodes, tables, Common.subtype_refl _, ?_⟩
  rw [CommonRecordTargetProfiles.subtype_required_iff]
  exact id

end Yulang.CommonSymbolicProfileCoherence
