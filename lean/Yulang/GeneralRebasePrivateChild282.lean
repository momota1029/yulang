import Yulang.GeneralRebasePrivateSchema282

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebasePrivateChild282
open GeneralNominalCenters (Plan Site)
open GeneralRebasePrivateKey282 (port Excludes different_purpose capture_private binder_private)
open GeneralRebasePrivateHead282 (output_private schema_private)
open GeneralRebasePrivateSchema282 (SiteSafe)
open GeneralRebaseAggregateTags281 (Tag)
open GeneralDeclarations
open GeneralNominalVersionedFrame231 (frame capture binder childSite emittedCenter clauseChild)
open GeneralDeclarationDemands (inputInterval outputTarget)
open GeneralNominalSaturationState (Packet)

theorem allocation_args (p : Packet roles) (tag : Tag) (clause : Clause)
    (idx : Fin (roles clause.role).arity) :
    port p.context.state.seed owner decl tag ≠ ((frame p).allocation p.declaration.id clause |>.arguments idx).1 ∧
    port p.context.state.seed owner decl tag ≠ ((frame p).allocation p.declaration.id clause |>.arguments idx).2 :=
  ⟨different_purpose tag (by decide : 2 ≤ 3),different_purpose tag (by decide : 2 ≤ 4)⟩

theorem allocation_out (p : Packet roles) (tag : Tag) (clause : Clause) (name : Nat) :
    port p.context.state.seed owner decl tag ≠ ((frame p).allocation p.declaration.id clause).outputs name :=
  different_purpose tag (by decide : 2 ≤ 5)

theorem center_private {q : Plan roles} (apart : Excludes q.packet owner decl tag)
    (clause idx : Nat) (pattern : GeneralDeclarationPatterns.Pattern) :
    port q.packet.context.state.seed owner decl tag ≠ emittedCenter q clause idx pattern := by
  unfold emittedCenter
  cases GeneralDeclarationPatterns.normalize pattern
  all_goals first
    | exact binder_private apart _
    | exact different_purpose tag (by decide : 2 ≤ 9)

theorem child_arguments {q : Plan roles} (apart : Excludes q.packet owner decl tag)
    (clause : Clause) (valid : clause.Signature roles) (idx : Fin (roles clause.role).arity) :
    port q.packet.context.state.seed owner decl tag ≠ ((clauseChild q.packet clause valid).demand.arguments idx).1 ∧
    port q.packet.context.state.seed owner decl tag ≠ ((clauseChild q.packet clause valid).demand.arguments idx).2 := by
  let p := q.packet
  let w := clause.arguments[idx.val]'(by rw [valid.1]; exact idx.isLt)
  change port p.context.state.seed owner decl tag ≠
    (inputInterval (capture p) (((frame p).allocation p.declaration.id clause).arguments idx) w).1 ∧
    port p.context.state.seed owner decl tag ≠
    (inputInterval (capture p) (((frame p).allocation p.declaration.id clause).arguments idx) w).2
  unfold inputInterval
  cases GeneralDeclarationPatterns.normalize w
  all_goals first | exact capture_private apart _ | exact allocation_args p tag clause idx

theorem child_site {q : Plan roles} (apart : Excludes q.packet owner decl tag)
    (clause : Clause) (valid : clause.Signature roles) :
    SiteSafe (childSite q clause valid) (port q.packet.context.state.seed owner decl tag) := by
  intro idx
  exact ⟨(child_arguments apart clause valid idx).1,(child_arguments apart clause valid idx).2,
    center_private apart _ _ _⟩

theorem child_output_target (q : Plan roles) (tag : Tag) (clause : Clause) (eqn : Equation) :
    port q.packet.context.state.seed owner decl tag ≠ outputTarget q.packet.declaration (capture q.packet)
       ((frame q.packet).allocation q.packet.declaration.id clause).outputs eqn := by
  unfold outputTarget
  split
  · split
    · exact output_private q tag _
    · exact allocation_out q.packet tag clause _
  · exact allocation_out q.packet tag clause _

theorem child_output (q : Plan roles) (tag : Tag) (clause : Clause) (valid : clause.Signature roles)
    (o : GeneralSourceState.Output) (listed : o ∈ (clauseChild q.packet clause valid).demand.outputs) :
    port q.packet.context.state.seed owner decl tag ≠ o.target := by
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp listed
  exact child_output_target q tag clause e

end Yulang.GeneralRebasePrivateChild282
