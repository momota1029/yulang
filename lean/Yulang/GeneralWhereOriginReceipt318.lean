import Yulang.GeneralWhereOriginCheckedFixture318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 14000000
namespace Yulang.GeneralWhereOriginReceipt318
open GeneralWhereOriginTrace318 (Trace rawOf from_lookup)
open GeneralWhereOriginDelta318 (Cell)
open GeneralWhereOriginConfig318 (history_config)
open GeneralWhereVersionInstall317 (Journal)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary checked_compiled)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalCandidates (Context)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralWhereVersionCompiler317 (schema)
open GeneralVersionedEndpointAddress315 (atCell fields)
open GeneralNominalCenteredHeadMatSchemas (Equation)
open GeneralDictionaryBinderLocations (sourceSlot)

/-- Receipt for a present endpoint. It identifies the full checked source
declaration, owner, where-clause, argument position and exact stored row.
The whole old occurrence need not equal the current one. -/
theorem exact_receipt {j : Journal rs} {i : Fin (rawOf j).base.slots}
    (checked : (boundary rs).Checked r) (trace : Trace r j)
    (frame : Frame (Compiled r) j.mixed.core focus entryKey p) (c : Cell p)
    (found : sourceSlot (rawOf j).base c.row.target = some i) :
    ∃ q ∈ j.versionedWhere, ∃ written : Cell q,
      q.packet.site.occurrence.identity = p.packet.site.occurrence.identity ∧
      q.packet.declaration = p.packet.declaration ∧ written.clause = c.clause ∧
      written.index = c.index ∧ written.side = c.side ∧
      written.row = c.row ∧ written.row ∈ (schema q).equations := by
  have currentSeed : (rawOf j).seed = p.packet.context.state.seed :=
    congrArg (fun x : Context => x.state.seed) frame.context_eq.symm
  obtain ⟨q,seen,d,target,written,_⟩ := from_lookup trace found (c.high currentSeed)
  have cfg := history_config trace q seen
  have seed := cfg.seed.trans currentSeed
  have addr : atCell q d.side d.clause.id d.index d.row.expression =
      atCell p c.side c.clause.id c.index c.row.expression := target
  obtain ⟨who,key,side,clause,pos,_⟩ := fields seed addr
  have decl := GeneralDictionaryEmissionPlans.declaration_key_unique (Compiled r)
    (checked_compiled checked).2 _ _ cfg.visible frame.visible key
  have clauseEq := GeneralVersionedCompoundRows313.key_unique GeneralDeclarations.Clause.id _
    p.packet.checked.identified.1 _ _ (decl ▸ d.listed) c.listed clause
  have old := d.located
  rw [clauseEq,pos] at old
  have pat := Option.some.inj (old.symm.trans c.located)
  have oldCode := d.translated
  have sameRegistry := cfg.registry.trans frame.registry_eq.symm
  have sameView := cfg.interp.trans (congrArg Context.interpretation frame.context_eq).symm
  rw [sameRegistry,sameView,pat] at oldCode
  have coded := Option.some.inj (oldCode.symm.trans c.translated)
  have mode : d.row.mode = c.row.mode := congrArg GeneralVersionedEndpointAddress315.Side.mode side
  have row := GeneralWhereOriginSchema318.row_ext d.row c.row target mode coded
  exact ⟨q,seen,d,who,decl,clauseEq,pos,side,row,written⟩

end Yulang.GeneralWhereOriginReceipt318
