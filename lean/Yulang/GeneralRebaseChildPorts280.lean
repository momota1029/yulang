import Yulang.GeneralRebaseClosedChildIdentity279

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseChildPorts280
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalSaturationState (Packet)
open GeneralSourceState (Interval)
open GeneralRebaseClosedChildShape279 (Canonical argList input_is_port)
open GeneralNominalCenteredHeadMatCompletionRequests (Formed outputs)
open GeneralDeclarationPatterns (normalize)

def ports (seed parent declaration clause position : Nat) : Interval :=
  (GeneralNominalIdentities.source seed (GeneralNominalAllocation.origin parent declaration 3 clause position),
   GeneralNominalIdentities.source seed (GeneralNominalAllocation.origin parent declaration 4 clause position))

def fixed (packet : Packet roles) (clause : Clause) (valid : clause.Signature roles) : Occurrence roles :=
  let raw := GeneralNominalVersionedFrame231.clauseChild packet clause valid
  let args := fun i : Fin (roles clause.role).arity =>
    ports packet.context.state.seed packet.site.occurrence.identity packet.declaration.id clause.id i.val
  { raw with demand := { raw.demand with arguments := args } }

def fixedSite (plan : Plan roles) (clause : Clause) (valid : clause.Signature roles) : Site roles :=
  ⟨fixed plan.packet clause valid,(GeneralNominalVersionedFrame231.childSite plan clause valid).center⟩

theorem fixed_id (packet : Packet roles) (clause : Clause) (valid : clause.Signature roles) :
    (fixed packet clause valid).identity =
      (GeneralNominalVersionedFrame231.clauseChild packet clause valid).identity := rfl

theorem fixed_role (packet : Packet roles) (clause : Clause) (valid : clause.Signature roles) :
    (fixed packet clause valid).demand.role = clause.role := rfl

theorem fixed_outputs (packet : Packet roles) (clause : Clause) (valid : clause.Signature roles) :
    (fixed packet clause valid).demand.outputs =
      (GeneralNominalVersionedFrame231.clauseChild packet clause valid).demand.outputs := rfl

theorem fixed_arguments (packet : Packet roles) (clause : Clause) (valid : clause.Signature roles) :
    List.ofFn (fixed packet clause valid).demand.arguments =
     argList roles packet.context.state.seed packet.site.occurrence.identity packet.declaration.id clause := rfl

theorem fixed_center (p : Plan roles) (clause : Clause) (valid : clause.Signature roles)
    (i : Fin (roles clause.role).arity) :
    (fixedSite p clause valid).center i = (GeneralNominalVersionedFrame231.childSite p clause valid).center i := rfl

theorem nonvariable_unchanged (packet : Packet roles) (clause : Clause) (valid : clause.Signature roles)
    (i : Fin (roles clause.role).arity)
    (h : ∀ name, normalize (clause.arguments[i.val]'(by rw [valid.1]; exact i.isLt)) ≠ .var name) :
    (fixed packet clause valid).demand.arguments i =
      (GeneralNominalVersionedFrame231.clauseChild packet clause valid).demand.arguments i := by
  change _ = GeneralDeclarationDemands.inputInterval _ _ _
  rw [input_is_port _ _ _ h]
  rfl

theorem bare_capture (packet : Packet roles) (clause : Clause) (valid : clause.Signature roles)
    (i : Fin (roles clause.role).arity)
    (h : normalize (clause.arguments[i.val]'(by rw [valid.1]; exact i.isLt)) = .var name) :
    (GeneralNominalVersionedFrame231.clauseChild packet clause valid).demand.arguments i =
     (GeneralNominalVersionedFrame231.capture packet).inputs name := by
  change GeneralDeclarationDemands.inputInterval _ _ _ = _
  simp only [GeneralDeclarationDemands.inputInterval,h]

theorem fixed_canonical (packet : Packet roles) (c : Clause) (valid : c.Signature roles)
    (visible : packet.declaration ∈ r.declarations) (member : c ∈ packet.declaration.requirements)
    (above : root.identity ≤ packet.site.occurrence.identity) (seed : packet.context.state.seed = s) :
    Canonical r s root (fixed packet c valid) := by
  refine Or.inr ⟨packet.site.occurrence.identity,packet.declaration,visible,c,member,above,?_,rfl,?_⟩
  · change GeneralNominalIdentities.source packet.context.state.seed _ = _
    rw [seed]
    rfl
  · rw [fixed_arguments,seed]

theorem fixed_output_formula (packet : Packet roles) (c : Clause) (valid : c.Signature roles) :
    (fixed packet c valid).demand.outputs =
      outputs packet.context.state.seed packet.site.occurrence.identity packet.declaration c := by
  change c.outputs.map _ = c.outputs.map _
  apply List.map_congr_left
  intro equation _
  rfl

theorem fixed_formed (packet : Packet roles) (c : Clause) (valid : c.Signature roles)
    (visible : packet.declaration ∈ r.declarations) (member : c ∈ packet.declaration.requirements)
    (above : root.identity ≤ packet.site.occurrence.identity) (seed : packet.context.state.seed = s) :
    Formed r s root (fixed packet c valid) := by
  refine Or.inr ⟨packet.site.occurrence.identity,packet.declaration,visible,c,member,above,?_,?_⟩
  · change GeneralNominalIdentities.source packet.context.state.seed _ = _
    rw [seed]
    rfl
  · rw [fixed_output_formula,seed]

theorem fixed_distinct (seed parent decl clause pos : Nat) :
    (ports seed parent decl clause pos).1 ≠ (ports seed parent decl clause pos).2 := by
  intro equal
  have keys := (GeneralNominalIdentities.source_identity seed _ _).mp equal
  have purp : (3 : Nat) = 4 := congrArg (fun k : GeneralNominalIdentities.Origin => k.2.2.1) keys
  omega

end Yulang.GeneralRebaseChildPorts280
