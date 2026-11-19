import Yulang.GeneralRebaseInspectionChecks268

namespace Yulang.GeneralRebaseInspectionProbe268
open GeneralDeclarations (Registry Declaration)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCandidates (Context Metadata)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalCenters (Site SameInputs)
open GeneralNominalRecursiveCandidates (arguments)
open GeneralNominalVersionedCandidates231 (inputs InspectionPending Prepared Failed)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded)
open GeneralRebaseInspectionChecks268 (BoundList Head check check_sound)
open GeneralRebasePartialBool268 (Answer Reflect both either neg)
open GeneralRebasePartialFinite268 (any any_sound)
open GeneralRebaseRawK2Probe268 (bool_reflect)
open GeneralRebaseCandidateChecks267 (allKnown allKnown_exact)

def awaiting (registry : Registry) (ctx : Context) (focus : Occurrence roles) (decl : Declaration)
 (metadata : Answer) (head : BoundList ctx → Answer) : Answer :=
 let answer := check registry ctx focus decl metadata head
 both (some (decl.role == focus.demand.role)) (both (neg answer.2) (neg answer.1))

theorem awaiting_sound (registry : Registry) (ctx : Context) (focus : Occurrence roles) (decl : Declaration)
 (metadata : Answer) (head : BoundList ctx → Answer) (metaSound : Reflect (Metadata registry ctx) metadata)
 (headSound : ∀ bounds, arguments ctx (inputs focus) = some bounds → Reflect (Head registry ctx focus decl bounds) (head bounds)) :
 Reflect (decl.role = focus.demand.role ∧ ¬ Failed registry ctx focus decl ∧ ¬ Prepared registry ctx focus decl)
  (awaiting registry ctx focus decl metadata head) := by
 have one := check_sound registry ctx focus decl metadata head metaSound headSound
 exact GeneralRebasePartialBool268.both_sound (bool_reflect _ _ (beq_iff_eq ..))
   (GeneralRebasePartialBool268.both_sound (GeneralRebasePartialBool268.neg_sound one.2)
    (GeneralRebasePartialBool268.neg_sound one.1))

def raw (registry : Registry) (ctx : Context) (focus : Occurrence roles)
 (metadata : Answer) (head : Declaration → BoundList ctx → Answer) : Answer :=
 both (some (allKnown ctx.state (inputs focus).demand))
  (any (fun decl => awaiting registry ctx focus decl metadata (head decl)) registry.declarations)

theorem raw_sound (registry : Registry) (ctx : Context) (focus : Occurrence roles)
 (metadata : Answer) (head : Declaration → BoundList ctx → Answer)
 (metaSound : Reflect (Metadata registry ctx) metadata)
 (headSound : ∀ decl ∈ registry.declarations, ∀ bounds, arguments ctx (inputs focus) = some bounds → Reflect (Head registry ctx focus decl bounds) (head decl bounds)) :
 Reflect (InspectionPending registry ctx focus) (raw registry ctx focus metadata head) :=
 GeneralRebasePartialBool268.both_sound (bool_reflect _ _ (allKnown_exact ..))
  (any_sound _ _ _ (fun decl onList => awaiting_sound registry ctx focus decl metadata
    (head decl) metaSound (headSound decl onList)))

def probe (registry : Registry) (state : State roles) (focus : Occurrence roles)
 (metadata : Answer) (head : Declaration → BoundList state.core.erased.current.context → Answer)
 (compare : Site roles → Site roles → Answer) : Answer :=
 either (raw (Encoded registry) state.core.erased.current.context focus metadata head)
  (neg (GeneralRebaseAdministrativeProbe268.ready state focus compare))

theorem probe_sound (registry : Registry) (state : State roles) (focus : Occurrence roles)
 (metadata : Answer) (head : Declaration → BoundList state.core.erased.current.context → Answer)
 (compare : Site roles → Site roles → Answer)
 (metaSound : Reflect (Metadata (Encoded registry) state.core.erased.current.context) metadata)
 (headSound : ∀ decl ∈ (Encoded registry).declarations, ∀ bounds,
   arguments state.core.erased.current.context (inputs focus) = some bounds →
   Reflect (Head (Encoded registry) state.core.erased.current.context focus decl bounds) (head decl bounds))
 (compareSound : ∀ first ∈ state.core.sites, ∀ last ∈ state.core.sites,
   Reflect (SameInputs (Models state) first last) (compare first last)) :
 Reflect ((Boundary roles).InspectionPending registry state focus) (probe registry state focus metadata head compare) :=
 GeneralRebasePartialBool268.either_sound (raw_sound (Encoded registry) state.core.erased.current.context focus metadata head
   metaSound headSound) (GeneralRebasePartialBool268.neg_sound
    (GeneralRebaseAdministrativeProbe268.ready_sound state focus compare compareSound))

end Yulang.GeneralRebaseInspectionProbe268
