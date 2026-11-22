import Yulang.GeneralDeclarativeWhereEndpoint346

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWhereReuse346
open GeneralDeclarations (Registry Clause)
open GeneralNominalCenters (Plan)
open GeneralWhereVersionInstall317 (Journal Models)
open GeneralWhereOriginDelta318 (Cell)
open GeneralWhereOriginTrace318 (Trace rawOf from_lookup)
open GeneralWhereOriginConfig318 (history_config)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary checked_compiled)
open GeneralNominalCandidates (Context)
open GeneralWhereVersionCompiler317 (schema)
open GeneralVersionedEndpointAddress315 (atCell fields footprint)
open GeneralDictionaryBinderLocations (sourceSlot)
open GeneralNominalVersionedPlans231 (variables)
open GeneralNominalCommonBridge (Assignment)

structure SameAuthor {p q : Plan rs} (c : Cell p) (d : Cell q) : Prop where
  invocation : p.packet.site.occurrence.identity = q.packet.site.occurrence.identity
  declaration : p.packet.declaration = q.packet.declaration
  clause : c.clause = d.clause
  ordinal : c.index = d.index
  side : c.side = d.side
  pattern : c.pattern = d.pattern
  code : c.expression = d.expression
  operands : footprint p c.side.mode c.expression = footprint q d.side.mode d.expression

theorem same_author {p q : Plan rs} (c : Cell p) (d : Cell q)
    (checked : GeneralDeclarations.Checked p.packet.registry)
    (registry : p.packet.registry = q.packet.registry)
    (interpretation : p.packet.context.interpretation = q.packet.context.interpretation)
    (seed : p.packet.context.state.seed = q.packet.context.state.seed)
    (here : p.packet.declaration ∈ p.packet.registry.declarations)
    (previous : q.packet.declaration ∈ q.packet.registry.declarations)
    (target : c.row.target = d.row.target) : SameAuthor c d := by
  obtain ⟨owner,decl,mode,clauseId,arg,operand⟩ := fields seed target
  have declEq := GeneralDictionaryEmissionPlans.declaration_key_unique _ checked _ _
    here (registry.symm ▸ previous) decl
  have clauseEq := GeneralVersionedCompoundRows313.key_unique Clause.id _
    p.packet.checked.identified.1 c.clause d.clause c.listed (declEq.symm ▸ d.listed) clauseId
  have located : c.clause.arguments[c.index]? = some d.pattern := by
    rw [clauseEq,arg]; exact d.located
  have samePat := Option.some.inj (c.located.symm.trans located)
  have printed : GeneralNominalCenteredHeadMatExpressions.translate
     p.packet.registry.constructors p.packet.context.interpretation c.pattern = some d.expression := by
    rw [registry,interpretation,samePat]
    exact d.translated
  have sameCode := Option.some.inj (c.translated.symm.trans printed)
  exact ⟨owner,declEq,clauseEq,arg,mode,samePat,sameCode,operand⟩

/-- A physical reuse acquires its prior author's literal stamp and
compiled source/RHS/mode, not just semantic equality of its target. -/
theorem replay {j : Journal rs} {p : Plan rs} (checked : (boundary rs).Checked r)
    (trace : Trace r j)
    (frame : Frame (Compiled r) j.mixed.core focus tag p)
    (c : Cell p) {i : Fin (rawOf j).base.slots}
    (hit : sourceSlot (rawOf j).base c.row.target = some i) (m : Assignment) (valid : Models j m) :
    ∃ (k : Nat) (prior : Plan rs) (d : Cell prior), j.versionedWhere[k]? = some prior ∧
      d.row.target = c.row.target ∧ d.row ∈ (schema prior).equations ∧ SameAuthor c d ∧
      d.row.Holds (variables prior m) m ∧ c.row.Holds (variables p m) m := by
  have atSeed : (rawOf j).seed = p.packet.context.state.seed :=
    congrArg (fun ctx : Context => ctx.state.seed) frame.context_eq.symm
  obtain ⟨prior,old,d,eq,stored,_⟩ := from_lookup trace hit (c.high atSeed)
  obtain ⟨k,recorded⟩ := List.mem_iff_getElem?.mp old
  have config := history_config trace prior old
  have registry := frame.registry_eq.trans config.registry.symm
  have interpretation := (congrArg Context.interpretation frame.context_eq).trans config.interp.symm
  have seed := atSeed.symm.trans config.seed.symm
  have proper := (checked_compiled checked).2
  have checkedP : GeneralDeclarations.Checked p.packet.registry := frame.registry_eq.symm ▸ proper
  have current : p.packet.declaration ∈ p.packet.registry.declarations := frame.registry_eq.symm ▸ frame.visible
  have oldVisible : prior.packet.declaration ∈ prior.packet.registry.declarations := config.registry.symm ▸ config.visible
  exact ⟨k,prior,d,recorded,eq,stored,same_author c d checkedP registry interpretation seed current oldVisible eq.symm,
    (valid.2 prior old).1.rows _ stored,GeneralWhereOriginConfig318.already_holds checked trace frame c hit m valid⟩

end Yulang.GeneralDeclarativeWhereReuse346
