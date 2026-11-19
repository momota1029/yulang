import Yulang.GeneralRebaseCompoundExpr273
import Yulang.GeneralRebaseTreeSchema272

namespace Yulang.GeneralRebaseCompoundSchema273
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedPlans231 (variables emittedSchema)
open GeneralNominalCenteredHeadMatSchemas (Equation Schema)
open GeneralRebaseCompoundExpr273 (Env run)

abbrev Table := Nat → Option Ty

def Certified (m : Assignment) (table : Table) : Prop :=
 ∀ id v, table id = some v → Equivalent (m id).1 v

def Uniform (s : State roles) (table : Table) : Prop :=
 ∀ m, Models s m → Certified m table

def environment (table : Table) (plan : Plan roles) : Env :=
 fun mode n => table (GeneralRebaseTreeSchema272.identity plan mode n)

theorem environment_sound (table : Table) (plan : Plan roles) (m : Assignment)
 (honest : Certified m table) :
 GeneralRebaseCompoundExpr273.Certified (environment table plan) (variables plan m) := by
 intro mode id t hit
 rw [GeneralRebaseTreeSchema272.identity_exact]
 exact honest _ _ hit

def equationResult (env : Env) (id : Nat) (e : Equation) : Option Ty :=
 if e.target = id then run env e.mode e.expression else none

def lookup (env : Env) (schema : Schema) (id : Nat) : Option Ty :=
 schema.equations.findSome? (equationResult env id)

theorem lookup_sound (env : Env) (schema : Schema) (id : Nat) (reduced : Ty)
 (vars : GeneralRebaseTreeExprCompile272.Variables) (m : Assignment)
 (honest : GeneralRebaseCompoundExpr273.Certified env vars) (holds : schema.Holds vars m)
 (hit : lookup env schema id = some reduced) : Equivalent (m id).1 reduced := by
 obtain ⟨first,e,last,list,value,_⟩ := List.findSome?_eq_some_iff.mp hit
 have member : e ∈ schema.equations := by
   rw [list]
   exact List.mem_append_right _ List.mem_cons_self
 unfold equationResult at value
 split at value
 · rename_i target
   have out := holds e member
   change Equivalent (m e.target).1 _ at out
   rw [target] at out
   exact GeneralDictionaryDefaultExpression209.equivalent_trans out
     (GeneralRebaseCompoundExpr273.sound env vars honest _ _ _ value)
 · contradiction

def derive (table : Table) (plan : Plan roles) : Table :=
 fun id => (table id).or (lookup (environment table plan) (emittedSchema plan) id)

theorem derive_sound (m : Assignment) (table : Table) (plan : Plan roles)
 (seed : Certified m table) (holds : GeneralNominalVersionedPlans231.Outputs plan m) :
 Certified m (derive table plan) := by
 intro id v hit
 unfold derive at hit
 cases prior : table id with
 | none =>
   exact lookup_sound _ _ id v _ m (environment_sound table plan m seed) holds
     (by simpa [prior,Option.or] using hit)
 | some priorValue =>
   have same := Option.some.inj (by simpa [prior,Option.or] using hit)
   exact same ▸ seed id priorValue prior

theorem derive_uniform (s : State roles) (table : Table) (plan : Plan roles)
 (uniform : Uniform s table) (retained : plan ∈ s.plans) : Uniform s (derive table plan) :=
 fun m valid => derive_sound m table plan (uniform m valid) (valid.2.1 plan retained).2.2

def empty : Table := fun _ => none

theorem empty_uniform (s : State roles) : Uniform s empty := by
 intro _ _ _ _ hit
 cases hit

def fromTrees (table : GeneralRebaseTreeInterpreter272.Source) : Table :=
 fun id => (table id).map GeneralRebaseFiniteTree272.value

theorem fromTrees_certified (m : Assignment) (table : GeneralRebaseTreeInterpreter272.Source)
 (good : GeneralRebaseTreeInterpreter272.Certified m table) : Certified m (fromTrees table) := by
 intro id t hit
 obtain ⟨tree,present,rfl⟩ := Option.map_eq_some_iff.mp hit
 exact (good id tree present).2

end Yulang.GeneralRebaseCompoundSchema273
