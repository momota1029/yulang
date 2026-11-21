import Yulang.GeneralVersionedEndpointPatch315

set_option backward.isDefEq.respectTransparency false
/-! Real endpoint positions identify the expression under the same checked
compiler. Model agreement across reads is not needed: colliding versioned
addresses decode the same ordered source IDs. -/
namespace Yulang.GeneralVersionedEndpointSourceKey315
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralVersionedEndpointAddress315 (Side atCell fields coherent)
open GeneralNominalCenteredHeadMatExpressions (translate value)
open GeneralNominalCenteredHeadMatSchemas
open GeneralNominalVersionedPlans231 (variables)
open GeneralVersionedTraceDomain313 (seed)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalCommonBridge (Assignment)

abbrev Row := GeneralNominalCenteredHeadMatSchemas.Equation

structure SourceRow (p : Plan roles) (side : Side) (clause : Clause) (pos : Nat) (row : Row) : Prop where
  listed : clause ∈ p.packet.declaration.requirements
  source : ∃ pat, clause.arguments[pos]? = some pat ∧
    translate p.packet.registry.constructors p.packet.context.interpretation pat = some row.expression
  mode : row.mode = side.mode

theorem from_endpoint {p : Plan roles} {row : Row}
    (recovered : GeneralVersionedEndpointLedger314.Endpoint p row) :
    ∃ side clause pos, SourceRow p side clause pos row := by
  obtain ⟨clause,listed,pos,kind,pat,tag,atPos,_,decoded,_,mode⟩ := recovered
  rcases tag with rfl|rfl
  · exact ⟨.lower,clause,pos,listed,⟨pat,atPos,decoded⟩,mode⟩
  · exact ⟨.upper,clause,pos,listed,⟨pat,atPos,decoded⟩,mode⟩

theorem coherent_on_trace {s : State roles} {p q : Plan roles} {a b : Side} {c d : Clause} {i j : Nat}
    {left right : Row}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (f : Frame (Compiled registry) s.core focus key p) (stored : q ∈ s.plans)
    (first : SourceRow p a c i left) (last : SourceRow q b d j right)
    (same : atCell p a c.id i left.expression = atCell q b d.id j right.expression) :
    ∀ m : Assignment, value (variables p m) left.mode left.expression = value (variables q m) right.mode right.expression := by
  have cfg := GeneralVersionedSiteOrigins312.stored_current_config actual stored
  have oldSeed := cfg.1.trans (congrArg (fun c => c.state.seed) f.context_eq).symm
  obtain ⟨_,keySame,atSide,clauseSame,atPos,_⟩ := fields oldSeed.symm same
  subst b; subst j
  have oldRegistry := (GeneralNominalVersionedMixedRegistry234.reachable actual).2.1 q stored
  have oldInterp := cfg.2.2.trans (congrArg GeneralNominalCandidates.Context.interpretation f.context_eq).symm
  have prior : q.packet ∈ s.core.erased.current.packets := by
    rw [(GeneralNominalVersionedMixedChoiceHistory236.reachable actual).2]
    exact List.mem_map.mpr ⟨q,stored,rfl⟩
  have oldVisible := GeneralNominalVersionedMixedChoiceHistory236.visible actual prior
  have decl := GeneralDictionaryEmissionPlans.declaration_key_unique _
    (GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked).2 _ _ f.visible oldVisible keySame
  have clauses := GeneralVersionedCompoundRows313.key_unique Clause.id _
    p.packet.checked.identified.1 c d first.listed (decl.symm ▸ last.listed) clauseSame
  subst d
  obtain ⟨pat,atPat,translated⟩ := first.source
  obtain ⟨other,oldPat,oldTranslated⟩ := last.source
  have samePat := Option.some.inj (oldPat.symm.trans atPat)
  subst other
  have oldCatalogue := congrArg Registry.constructors (oldRegistry.trans f.registry_eq.symm)
  rw [oldCatalogue,oldInterp] at oldTranslated
  have code := Option.some.inj (oldTranslated.symm.trans translated)
  rw [code] at same
  intro m
  rw [first.mode,last.mode,code]
  exact coherent oldSeed.symm same m

end Yulang.GeneralVersionedEndpointSourceKey315
