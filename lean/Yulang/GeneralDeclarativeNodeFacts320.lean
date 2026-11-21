import Yulang.GeneralDeclarativeOutputFacts320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14000
set_option maxHeartbeats 3800000
namespace Yulang.GeneralDeclarativeNodeFacts320
open GeneralDeclarations (Declaration Clause Registry Checked)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand Bounds bounds_sound)
open GeneralDeclarativeAssembly320 (Meaning ChildDenotes Node head_sound named_sound)
open GeneralDeclarativeNormalized320 (normalized_where_clause ordered_map)
open GeneralDeclarativeArgumentFacts320 (headFact whereFacts compiled_head compiled_where)
open GeneralDeclarativeOutputFacts320 (childFact rootFact compiled_child_outputs compiled_root_outputs)
open GeneralDeclarativeBatch320 (zipFacts zip_sound collect)
open CommonRoleOutermostResolver (All₂)

def clauseFacts (r : Registry) (interp : Interpretation) (capture : Nat → Capture)
    (clause : Clause) (child : Demand) : Option (List Equation) :=
  if child.role = clause.role then do
    let args ← zipFacts (whereFacts r.constructors interp capture) child.arguments clause.arguments
    let outputs ← zipFacts (childFact r.constructors interp capture) clause.outputs child.outputs
    pure (args ++ outputs)
  else none

/-- An ordinary-state compiler, not an installation. All logical names
are supplied by the source-side demand presentation. It doesn't allocate,
select an implementation, or run any child. -/
def nodeFacts (r : Registry) (interp : Interpretation) (capture : Nat → Capture)
    (decl : Declaration) (d : Demand) (children : List Demand) : Option (List Equation) :=
  if decl.role = d.role then do
    let head ← zipFacts (headFact r.constructors interp capture) d.arguments decl.head
    let requirements ← zipFacts (clauseFacts r interp capture) decl.requirements children
    let outputs ← collect (rootFact r interp decl d capture) d.outputs
    pure (head ++ requirements ++ outputs)
  else none

theorem compiled_clause {s r interp capture decl clause child facts}
    (checked : GeneralDeclarations.DeclarationChecked r.constructors r.roles decl)
    (belongs : clause ∈ decl.requirements)
    (bound : ∀ name ∈ decl.inputNames, Bounds s (capture name))
    (generated : clauseFacts r interp capture clause child = some facts)
    (settled : facts ⊆ s.equations) (m : Assignment) (valid : Models s m) :
    ChildDenotes r.constructors interp capture m clause child := by
  by_cases role : child.role = clause.role
  · cases args : zipFacts (whereFacts r.constructors interp capture) child.arguments clause.arguments with
    | none => simp [clauseFacts,role,args] at generated
    | some aa =>
      cases outs : zipFacts (childFact r.constructors interp capture) clause.outputs child.outputs with
      | none => simp [clauseFacts,role,args,outs] at generated
      | some oo =>
        have batch : aa ++ oo = facts := by simpa [clauseFacts,role,args,outs] using generated
        subst facts
        refine ⟨role,normalized_where_clause checked belongs bound ?_ m valid,
          compiled_child_outputs outs (fun _ h => settled (List.mem_append_right _ h)) m valid⟩
        exact compiled_where args (fun _ h => settled (List.mem_append_left _ h))
  · simp [clauseFacts,role] at generated

theorem compiled_clauses {s r interp capture decl children facts}
    (checked : GeneralDeclarations.DeclarationChecked r.constructors r.roles decl)
    (bound : ∀ name ∈ decl.inputNames, Bounds s (capture name))
    (generated : zipFacts (clauseFacts r interp capture) decl.requirements children = some facts)
    (settled : facts ⊆ s.equations) (m : Assignment) (valid : Models s m) :
    All₂ (ChildDenotes r.constructors interp capture m) decl.requirements children := by
  apply ordered_map (zip_sound generated)
  rintro _ listed _ _ ⟨one,compiled,sub⟩
  exact compiled_clause checked listed bound compiled (fun _ h => settled (sub h)) m valid

/-- Mechanical sufficient producer from the actual source compiler and
ordinary fact inclusion. The separate accepted-frontier theorem has to
justify the logical capture naming and ordinary completeness. -/
theorem batch_node_sound {s r interp capture decl d kids facts}
    (checked : Checked r) (visible : decl ∈ r.declarations)
    (captures : ∀ n ∈ decl.inputNames, Bounds s (capture n))
    (bounds : ∀ arg ∈ d.arguments, Bounds s arg)
    (generated : nodeFacts r interp capture decl d kids = some facts)
    (settled : facts ⊆ s.equations)
    (m : Assignment) (valid : Models s m) : Meaning r interp m d decl capture kids := by
  by_cases role : decl.role = d.role
  · cases hd : zipFacts (headFact r.constructors interp capture) d.arguments decl.head with
    | none => simp [nodeFacts,role,hd] at generated
    | some hs =>
      cases req : zipFacts (clauseFacts r interp capture) decl.requirements kids with
      | none => simp [nodeFacts,role,hd,req] at generated
      | some cs =>
        cases result : collect (rootFact r interp decl d capture) d.outputs with
        | none => simp [nodeFacts,role,hd,req,result] at generated
        | some os =>
          have batch : hs ++ cs ++ os = facts := by simpa [nodeFacts,role,hd,req,result] using generated
          subst facts
          have head := compiled_head hd (fun _ h => settled (List.mem_append_left _ (List.mem_append_left _ h))) bounds
          have children := compiled_clauses (checked.2 decl visible) captures req
            (fun _ h => settled (List.mem_append_left _ (List.mem_append_right _ h))) m valid
          have output := compiled_root_outputs result (fun _ h => settled (List.mem_append_right _ h))
          exact ⟨visible,role,fun n h => bounds_sound (captures n h) m valid,
            ordered_map head (fun _ _ _ _ h => head_sound h m valid),children,
            fun o h => named_sound checked visible (output o h) m valid⟩
  · simp [nodeFacts,role] at generated

theorem batch_chosen {s r interp capture decl d kids facts}
    (checked : Checked r) (visible : decl ∈ r.declarations)
    (captures : ∀ n ∈ decl.inputNames, Bounds s (capture n))
    (bounds : ∀ arg ∈ d.arguments, Bounds s arg)
    (generated : nodeFacts r interp capture decl d kids = some facts)
    (settled : facts ⊆ s.equations)
    (m : Assignment) (valid : Models s m) : Node r interp m d decl.id kids :=
  ⟨decl,capture,rfl,batch_node_sound checked visible captures bounds generated settled m valid⟩

end Yulang.GeneralDeclarativeNodeFacts320
