import Yulang.GeneralDeclarativeWitnessOrderedNonpointModel362
import Yulang.GeneralDeclarativeWitnessExecutableRelease362

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 75000
set_option maxHeartbeats 86000000
namespace Yulang.GeneralDeclarativeWitnessCrossOwnerReceiver362
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered run payload)
open GeneralDeclarativeWitnessSeparateAuthorOrder362 (Compared compare lo mid hi)
open GeneralDeclarativeWitnessNonpointPort362 (author frame env ordinary)
open GeneralDeclarativeWitnessOrderedNonpointRepeat362 (Body replay)
open GeneralDeclarativeWitnessNativePreparation360 (Prepared Layout prepare)
open GeneralDeclarativeWitnessNativeInstall360 (World Fits NativeViews)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessCompiler350 (printDemand trip)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessSparseIntervals357 (Compiled)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCommonBridge (Assignment)

def native : Capture := ⟨301,302,303⟩
def asked : Demand := ⟨10,[native,ordinary],[]⟩
def layout (world : World) : Layout :=
  ⟨world.ordinary,[(90,native),(91,ordinary)],[60,61,62,301,302,303],
    fun _ => ⟨0,0,0⟩,fun _ _ => 0⟩

structure Consumed {contra : Bool} (x : Ordered contra) where
  sources : Compared x
  verifiedSources : compare x = some sources
  env : Environment
  lower : Compiled env table false (lo x) (mid x)
  upper : Compiled env table false (mid x) (hi x)
  source : Prepared env frame asked (layout x.after.final)
  authorExact : source.impl = author
  child : Demand
  emitted : source.kids = [child]
  reader : Body env ⟨source.stage,x.after.final.board⟩ child 0

/-- The later source consumes a nonpoint request assembled from three
explicit distinct producer roots. Only a checked common mode table is
passed across declarations; the reader does not guess active grants. -/
def consume {contra} (x : Ordered contra) : Option (Consumed x) :=
  match sources : compare x with
  | none => none
  | some auth => do
    let e ← env
    let lo ← GeneralDeclarativeWitnessSparseIntervals357.compile e table false (lo x) (mid x)
    let hi ← GeneralDeclarativeWitnessSparseIntervals357.compile e table false (mid x) (hi x)
    let p ← prepare e frame asked (layout x.after.final)
    if same : p.impl = author then
      match actual : p.kids with
      | [d] =>
        let result ← replay e ⟨p.stage,x.after.final.board⟩ d 0
        pure ⟨auth,sources,e,lo,hi,p,same,d,actual,result⟩
      | _ => none
    else none

def check {contra x} (u : @Consumed contra x) : Bool :=
  decide (printDemand u.child = (11,[(310,302,311)],[]) ∧ trip u.reader.span = (314,302,315))

theorem actual_read_of_three_independent_sources (contra : Bool) :
    ((run contra).bind fun x => (consume x).map check).getD false = true := by cases contra <;> decide +kernel

theorem preserves_checked_mode_words {contra} {x : Ordered contra} (w : Consumed x) :
    w.lower.rows = w.sources.left.rows ∧ w.upper.rows = w.sources.right.rows :=
  ⟨GeneralDeclarativeWitnessModeScope362.one_authorized_table_cannot_change_comparison_rows w.sources.left w.lower,
    GeneralDeclarativeWitnessModeScope362.one_authorized_table_cannot_change_comparison_rows w.sources.right w.upper⟩

theorem every_reader_fit_still_reads_each_original_owner {contra} {x : Ordered contra}
    (made : run contra = some x) (w : Consumed x) (m : Assignment) (v : NativeViews) (fit : Fits w.reader.world m v) :
    GeneralDeclarativeWitnessFullIntervals357.ContextDerives table m false (lo x) (mid x) ∧
    GeneralDeclarativeWitnessFullIntervals357.ContextDerives table m false (mid x) (hi x) ∧
    v 301 = some (.unary (GeneralDeclarativeWitnessThreeNative362.ctor contra) (.leaf (m (payload contra 0)).1)) ∧
    v 302 = some (.unary (GeneralDeclarativeWitnessThreeNative362.ctor contra) (.leaf (m (payload contra 1)).1)) ∧
    v 303 = some (.unary (GeneralDeclarativeWitnessThreeNative362.ctor contra) (.leaf (m (payload contra 2)).1)) := by
  have initial := GeneralDeclarativeGrowth327.restrict
    ((GeneralDeclarativeWitnessLiteral349.preserves_iff ..).mp w.reader.keeps) m fit.1
  have live := (GeneralDeclarativeWitnessNativePreparation360.same_model_of_prepared w.source m initial).1
  exact GeneralDeclarativeWitnessSeparateAuthorOrder362.all_claims_one_final_fit made w.verifiedSources m v ⟨live,fit.2⟩

end Yulang.GeneralDeclarativeWitnessCrossOwnerReceiver362
