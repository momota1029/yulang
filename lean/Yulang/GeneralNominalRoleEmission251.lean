import Yulang.GeneralNominalRoleChild251
namespace Yulang.GeneralNominalRoleEmission251
open GeneralNominalRoleEnvironment251 (Syntax)
open GeneralNominalRoleRequests251 (Request)
open GeneralNominalCenters (Plan)
open GeneralDeclarations (Clause)

/-- Both endpoint requests are retained, including variable patterns. -/
def inputRequests (plan : Plan roles) (env : Syntax) (clause : Clause) (valid : clause.Signature roles)
 (index : Fin (roles clause.role).arity) : List Request :=
 let bounds := GeneralNominalRoleChild251.argument plan env clause valid index
 [⟨GeneralNominalRoleChild251.pattern clause valid index,bounds.lower,.lower⟩,
  ⟨GeneralNominalRoleChild251.pattern clause valid index,bounds.upper,.upper⟩]

def clauseRequests (plan : Plan roles) (env : Syntax) (clause : Clause) (valid : clause.Signature roles) : List Request :=
 (List.ofFn (inputRequests plan env clause valid)).flatten ++
 clause.outputs.map fun equation => ⟨equation.rhs,GeneralNominalRoleChild251.outputTarget plan env clause equation,.actual⟩

def rootRequests (plan : Plan roles) (env : Syntax) : List Request :=
 (GeneralNominalMaterialization.rootRequests plan.packet.declaration plan.packet.site.occurrence).map
   fun request => ⟨request.pattern,(env.target request.target).ty,request.mode⟩

def requests (plan : Plan roles) (env : Syntax) : List Request :=
 rootRequests plan env ++
 (GeneralCanonicalChildOrder.canonicalRequirements plan.packet.declaration.requirements).attach.flatMap fun clause =>
   clauseRequests plan env clause.val (plan.packet.checked.signature.2.2.2 clause.val
     ((GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property))

theorem root_count (plan : Plan roles) (env : Syntax) :
 (rootRequests plan env).length = (GeneralNominalMaterialization.rootRequests plan.packet.declaration plan.packet.site.occurrence).length := by
 simp [rootRequests]

theorem input_count (plan : Plan roles) (env : Syntax) (clause : Clause) (valid : clause.Signature roles)
 (index : Fin (roles clause.role).arity) : (inputRequests plan env clause valid index).length = 2 := rfl

theorem clause_count (plan : Plan roles) (env : Syntax) (clause : Clause) (valid : clause.Signature roles) :
 (clauseRequests plan env clause valid).length = 2 * (roles clause.role).arity + clause.outputs.length := by
 have lengths (xs : List (List Request)) (each : ∀ x ∈ xs, x.length = 2) : xs.flatten.length = 2 * xs.length := by
   induction xs with
   | nil => rfl
   | cons head tail ih =>
     have one := each head (by simp)
     have two := ih (fun x member => each x (List.mem_cons_of_mem _ member))
     simp only [List.flatten_cons,List.length_append,List.length_cons,one,two]
     omega
 have count := lengths (List.ofFn (inputRequests plan env clause valid)) (by
   intro x member
   obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
   exact input_count plan env clause valid index)
 simpa only [clauseRequests,List.length_append,List.length_map,List.length_ofFn] using
   congrArg (fun n => n + clause.outputs.length) count
end Yulang.GeneralNominalRoleEmission251
