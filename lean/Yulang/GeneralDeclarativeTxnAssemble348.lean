import Yulang.GeneralDeclarativeTxnQuiet348

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTxnAssemble348
open GeneralDeclarations (Registry)
open GeneralNominalCenters (Plan)
open GeneralNominalCandidates (Context)
open GeneralWhereVersionInstall317 (Journal Models install)
open GeneralWhereVersionSemantics317 (Holds)
open GeneralNominalVersionedEffects231 (ClassEffects)
open GeneralWhereOriginSuccessor318 (SilentChildren with_parent)
open GeneralWhereOriginSupport318 (journalSources journal_models)
open GeneralDeclarativeWhereTxn348 (Txn SourcePermit)
open GeneralDeclarativeTxnEffects348 (literal_requests)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralWhereOriginTrace318 (rawOf)
open GeneralNominalRefinements (Refines)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalCommonBridge (Assignment)

/-- Independently checked raw refinement, frozen-plan equations and
the actual already-current request family's effects. The pre- and
post-journal model predicates are not part of this packet condition. -/
def LegalPatch (j : Journal rs) (ctx : Context) (p : Plan rs) (m : Assignment) : Prop :=
  GeneralNominalState.Models ctx.state m ∧ Holds p m ∧
    ClassEffects j.mixed.core p.packet.site.occurrence p m

theorem install_iff {j : Journal rs} {ctx : Context} {p : Plan rs}
    (physical : Refines (rawOf j) ctx.state) (quiet : SilentChildren p) (m : Assignment) :
    Models (install j ctx p) m ↔ Models j m ∧ LegalPatch j ctx p m := by
  constructor
  · intro accepted
    have stamp : p ∈ (install j ctx p).versionedWhere := List.mem_append_right _ List.mem_cons_self
    obtain ⟨well,full⟩ := accepted.2 p stamp
    have effects := (GeneralNominalVersionedFrameTransport232.class_effects_of_requests_eq
      (plan := p) (model := m) (literal_requests j ctx p quiet p.packet.site.occurrence)).mp full
    exact ⟨GeneralDeclarativeJournalPrefix347.previous physical m accepted,accepted.1.1.1,well,effects⟩
  · rintro ⟨previous,raw,typed,outputs⟩
    exact with_parent previous raw typed outputs quiet

/-- A separate producer can discharge feasibility by extending only
the frozen raw footprint and providing the patch's checked local
ingredients. The entire old journal is carried by footprint
transport, not assumed to be re-established by the producer. -/
theorem without_post_assumption {r : Registry} {j : Journal rs} {ctx : Context} {p : Plan rs}
    (reg : (boundary rs).Checked r)
    (located : Frame (Compiled r) j.mixed.core p.packet.site.occurrence p.packet.declaration.id p)
    (view : SourcePermit r j p)
    (physical : Refines (rawOf j) ctx.state)
    (meaning : ctx.interpretation = j.mixed.core.erased.current.context.interpretation)
    (choices : GeneralNominalCycleSteps.ChoiceCompatible j.mixed.core.erased.current p.packet)
    (quiet : SilentChildren p)
    (canExtend : ∀ m,Models j m → ∃ n, LegalPatch j ctx p n ∧ Agree (journalSources j) m n) :
    Txn r j ctx p := by
  refine ⟨reg,located,⟨view⟩,⟨physical⟩,meaning,choices,?_⟩
  intro m fit
  obtain ⟨n,patch,same⟩ := canExtend m fit
  exact ⟨n,(install_iff physical quiet n).mpr ⟨(journal_models j same).mp fit,patch⟩,same⟩

end Yulang.GeneralDeclarativeTxnAssemble348
