import Yulang.GeneralWhereOriginDelta318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 21000000
namespace Yulang.GeneralWhereOriginTrace318
open GeneralDeclarations (Registry)
open GeneralNominalCenters (Plan)
open GeneralNominalCandidates (Context)
open GeneralNominalVersionedJournal232 (State)
open GeneralWhereVersionInstall317 (Journal InstallStep install Models)
open GeneralWhereOriginDelta318 (High Cell Delta Keeps)
open GeneralNominalCenteredHeadMatSchemas (Equation)
open GeneralWhereVersionCompiler317 (schema)
open GeneralNominalVersionedPlans231 (variables)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)
open GeneralNominalCommonBridge (Assignment)

abbrev rawOf (j : Journal rs) := j.mixed.core.erased.current.context.state

def withContext (j : Journal rs) (ctx : Context) : Journal rs :=
  ⟨GeneralNominalVersionedRefresh232.refresh j.mixed ctx,j.versionedWhere⟩

/-- An explicitly checked trace on the experimental branch. Legacy history
enters unchanged. Later refreshes may move raw slots but cannot introduce
an unexplained high source. Each install must be a real C317 install and
supply its finite checked layout delta. -/
inductive Trace (r : Registry) : Journal rs → Prop where
  | legacy (s : State rs) :
      (∀ i : Fin s.core.erased.current.context.state.base.slots,
        ¬ High s.core.erased.current.context.state (s.core.erased.current.context.state.base.source i)) →
      Trace r ⟨s,[]⟩
  | reobserve {j} (ctx : Context) :
      Trace r j → ctx.interpretation = j.mixed.core.erased.current.context.interpretation →
      Keeps (rawOf j) ctx.state → Trace r (withContext j ctx)
  | placed {j} (ctx : Context) (p : Plan rs) :
      Trace r j → InstallStep r j (install j ctx p) →
      Delta (rawOf j) ctx.state p → Trace r (install j ctx p)

def Blame (j : Journal rs) (n : Nat) : Prop :=
  ∃ p ∈ j.versionedWhere, ∃ c : Cell p, c.row.target = n

theorem source_origin {j : Journal rs} (trace : Trace r j) :
    ∀ i : Fin (rawOf j).base.slots, High (rawOf j) ((rawOf j).base.source i) →
      Blame j ((rawOf j).base.source i) := by
  induction trace with
  | legacy s absent =>
    intro i high
    exact False.elim (absent i high)
  | @reobserve j ctx _ _ layout ih =>
    intro i high
    change High ctx.state (ctx.state.base.source i) at high
    obtain ⟨old,eq⟩ := layout.no_insert i high
    have older : High (rawOf j) ((rawOf j).base.source old) := by
      obtain ⟨k,tag,enc⟩ := high
      exact ⟨k,tag,eq.symm.trans (enc.trans (by rw [layout.refinement.seed]))⟩
    obtain ⟨p,found,c,h⟩ := ih old older
    exact ⟨p,found,c,h.trans eq.symm⟩
  | @placed j ctx plan _ _ layout ih =>
    intro i high
    change High ctx.state (ctx.state.base.source i) at high
    rcases layout.split_slot i high with ⟨old,eq⟩|⟨cell,_,eq⟩
    · have older : High (rawOf j) ((rawOf j).base.source old) := by
        obtain ⟨k,tag,enc⟩ := high
        exact ⟨k,tag,eq.symm.trans (enc.trans (by rw [layout.refinement.seed]))⟩
      obtain ⟨p,found,c,h⟩ := ih old older
      exact ⟨p,List.mem_append_left _ found,c,h.trans eq.symm⟩
    · exact ⟨plan,List.mem_append_right _ (List.mem_singleton_self _),cell,eq.symm⟩

theorem from_lookup {j : Journal rs} {i : Fin (rawOf j).base.slots} (trace : Trace r j)
    (located : sourceSlot (rawOf j).base n = some i) (high : High (rawOf j) n) :
    ∃ p ∈ j.versionedWhere, ∃ c : Cell p, c.row.target = n ∧
      c.row ∈ (schema p).equations ∧ GeneralWhereVersionStoredRow317.Endpoint p c.side c.clause c.index c.row := by
  have exactId := (sourceSlot_exact ..).mp located
  obtain ⟨p,found,cell,key⟩ := source_origin trace i (exactId.symm ▸ high)
  exact ⟨p,found,cell,key.trans exactId,cell.written⟩

theorem existing_has_equation {j : Journal rs} {i : Fin (rawOf j).base.slots} (trace : Trace r j)
    (located : sourceSlot (rawOf j).base n = some i) (high : High (rawOf j) n)
    (m : Assignment) (valid : Models j m) :
    ∃ p ∈ j.versionedWhere, ∃ c : Cell p, c.row.target = n ∧
      c.row ∈ (schema p).equations ∧ c.row.Holds (variables p m) m := by
  obtain ⟨p,found,c,key,mem,_⟩ := from_lookup trace located high
  exact ⟨p,found,c,key,mem,(valid.2 p found).1.rows _ mem⟩

end Yulang.GeneralWhereOriginTrace318
