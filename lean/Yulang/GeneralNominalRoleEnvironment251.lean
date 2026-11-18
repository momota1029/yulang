import Yulang.GeneralNominalMixedSchema251
import Yulang.GeneralNominalStableCaptureStep250
/-! Capture, binder and target expressions are separate roles. This permits
one source name to be read historically and as a replaced aggregate. -/
namespace Yulang.GeneralNominalRoleEnvironment251
open Core.PresenceGeneration (CompTerm TyTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalMaterialization (Mode)
open GeneralNominalRebaseProjectionView243 (Bounds)
open CommonNominalFullCarrier

structure Syntax where
 old : Nat → CompTerm Nat
 capture : Nat → Bounds
 binder : Nat → TyTerm Nat
 target : Nat → CompTerm Nat

structure Values where
 old : Assignment
 lower : Nat → Ty
 upper : Nat → Ty
 binder : Nat → Ty
 target : Assignment

def read (env : Syntax) (assignment : Assignment) : Values :=
 ⟨GeneralNominalRebaseRawView243.read env.old assignment,
 fun name => (env.capture name).lower.eval model assignment,
 fun name => (env.capture name).upper.eval model assignment,
 fun name => (env.binder name).eval model assignment,
 GeneralNominalRebaseRawView243.read env.target assignment⟩

def variables (outputs : List Nat) (env : Syntax) (mode : Mode) (name : Nat) : TyTerm Nat :=
 if name ∈ outputs then env.binder name else match mode with
 | .actual => env.binder name
 | .lower => (env.capture name).lower
 | .upper => (env.capture name).upper

def Values.variables (outputs : List Nat) (values : Values) (mode : Mode) (name : Nat) : Ty :=
 if name ∈ outputs then values.binder name else match mode with
 | .actual => values.binder name
 | .lower => values.lower name
 | .upper => values.upper name

theorem variables_exact (outputs : List Nat) (env : Syntax) (assignment : Assignment) (mode : Mode) (name : Nat) :
 (variables outputs env mode name).eval model assignment = (read env assignment).variables outputs mode name := by
 unfold variables Values.variables
 split <;> cases mode <;> rfl

def Requirement (outputs : List Nat) (values : Values) (name : Nat) (mode : Mode) (actual : Ty) : Prop :=
 if name ∈ outputs then Equivalent actual (values.binder name) else match mode with
 | .actual => Subtype (values.lower name) actual ∧ Subtype actual (values.upper name)
 | .lower => Equivalent actual (values.lower name)
 | .upper => Equivalent actual (values.upper name)

def requirement (outputs : List Nat) (env : Syntax) (name : Nat) (mode : Mode) : GeneralNominalRebaseSchemaView243.Requirement :=
 if name ∈ outputs then .equal (env.binder name) else match mode with
 | .actual => .interval (env.capture name).lower (env.capture name).upper
 | .lower => .equal (env.capture name).lower
 | .upper => .equal (env.capture name).upper

theorem requirement_exact (outputs : List Nat) (env : Syntax) (assignment : Assignment) (name : Nat) (mode : Mode) (actual : Ty) :
 (requirement outputs env name mode).Holds assignment actual ↔ Requirement outputs (read env assignment) name mode actual := by
 unfold requirement Requirement
 split <;> cases mode <;> rfl

structure Related (first last : Values) : Prop where
 old : first.old = last.old
 lower : ∀ name, Equivalent (first.lower name) (last.lower name)
 upper : ∀ name, Equivalent (first.upper name) (last.upper name)
 binder : ∀ name, Equivalent (first.binder name) (last.binder name)
 target : GeneralNominalAssignmentCongruence238.Same first.target last.target

theorem variables_related (same : Related first last) (outputs : List Nat) (mode : Mode) (name : Nat) :
 Equivalent (first.variables outputs mode name) (last.variables outputs mode name) := by
 unfold Values.variables
 split
 · exact same.binder name
 · cases mode with
   | actual => exact same.binder name
   | lower => exact same.lower name
   | upper => exact same.upper name

theorem requirement_related (same : Related first last) (outputs : List Nat) (name : Nat) (mode : Mode) (actual : Ty) :
 Requirement outputs first name mode actual ↔ Requirement outputs last name mode actual := by
 have self : Equivalent actual actual := ⟨subtype_refl _,subtype_refl _⟩
 unfold Requirement
 split
 · exact GeneralNominalRawCongruence238.equiv_iff self (same.binder name)
 · cases mode with
   | lower => exact GeneralNominalRawCongruence238.equiv_iff self (same.lower name)
   | upper => exact GeneralNominalRawCongruence238.equiv_iff self (same.upper name)
   | actual =>
     exact and_congr (GeneralNominalAssignmentCongruence238.subtype_iff (same.lower name) self)
       (GeneralNominalAssignmentCongruence238.subtype_iff self (same.upper name))
end Yulang.GeneralNominalRoleEnvironment251
