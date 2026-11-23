import Yulang.GeneralDeclarativeWitnessSourceEndpoint359
import Yulang.GeneralDeclarativeOpenFixtureWitness339

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7500000
namespace Yulang.GeneralDeclarativeWitnessActualOpenBody359
open GeneralDeclarativeWitnessSourceEndpoint359 (Witness check check_exact residual_endpoints)
open GeneralDeclarativeWitnessOpenSpine359 (sem)
open GeneralDeclarativeWitnessAuthoredProjection358 (Source)
open GeneralDeclarativeOpenFixtureBase339
  (initial arg eql eqh eqi eqOpen openLo high lowPayload root registry)
open GeneralDeclarativeOpenFixtureRoutes339 (routed w2)
open GeneralDeclarativeOpenFixtureSelection339 (final rootFinal root_grows child_grows dictionary every_model)
open GeneralDeclarativeOpenFixtureModel339 (inhabited)
open GeneralDeclarativeExactOverlay337 (ModelsExact)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeGrowth327 (Extends trans restrict)
open GeneralDeclarativeExactDelete337 (subtract)
open GeneralDeclarativeCompoundDictionary338 (Evidence)
open GeneralDeclarativeOpenFixtureWitness339 (rootOutput)
open GeneralDeclarativeHiddenDecl324 (interpretation)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent Subtype subtype_trans exactEmpty)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_symm eqv_trans)

def authored : Source := ⟨[eql,eqh,eqi,eqOpen]⟩
def lower : Witness := .linked (.chunk [(7,lowPayload)] 4 .stop)
def upper : Witness := .literal high

theorem actually_read_both :
    check authored initial arg.lower lower = true ∧
    check authored initial arg.upper upper = true := by decide +kernel

theorem needs_original_open_row :
    check ⟨[eql,eqh,eqi]⟩ initial arg.lower lower = false := by decide +kernel

theorem initial_to_compiler_final : Extends initial final :=
  trans (trans (GeneralDeclarativeCompoundTree338.tree_exact routed).1.1.1 root_grows) child_grows

def loRemainder (m : Assignment) := subtract [7] (sem m openLo)
def hiRemainder (m : Assignment) := subtract [7] (sem m high)

/-- Link the actual separately selected compiler output 6 and all declared
recursive evidence to the new independent raw source replay. No selection
is inferred from the interval; the same *already checked* model is used. -/
theorem actual_fixed_output_between_source_remainders (m : Assignment) (fit : ModelsExact final w2.reads m) :
    Evidence registry interpretation m root dictionary ∧
    Equivalent (m 6).1 (subtract [7] (m arg.center).1) ∧
    Equivalent (subtract [7] (m arg.lower).1) (loRemainder m) ∧
    Equivalent (subtract [7] (m arg.upper).1) (hiRemainder m) ∧
    Subtype (loRemainder m) (m 6).1 ∧ Subtype (m 6).1 (hiRemainder m) := by
  have base := restrict initial_to_compiler_final m fit.1
  have both : Bound initial.normal 0 1 ∧ Bound initial.normal 1 2 :=
    ⟨.interval List.mem_cons_self,.interval (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have observed := residual_endpoints (arg := arg) (check_exact.mp actually_read_both.1)
    (check_exact.mp actually_read_both.2) both m base [7]
  have out := rootOutput m fit
  exact ⟨every_model m fit,out,observed.1,observed.2.1,subtype_trans observed.2.2.1 out.2,
    subtype_trans out.1 observed.2.2.2⟩

theorem real_ordered_body_and_actual_remainders :
    ∃ m, ModelsExact final w2.reads m ∧
      Evidence registry interpretation m root dictionary ∧
      Subtype (loRemainder m) (m 6).1 ∧ Subtype (m 6).1 (hiRemainder m) ∧
      (m 11).1 = exactEmpty ∧ (m 17).1 = exactEmpty := by
  obtain ⟨m,fit,a,b⟩ := inhabited
  have actual := actual_fixed_output_between_source_remainders m fit
  exact ⟨m,fit,actual.1,actual.2.2.2.2.1,actual.2.2.2.2.2,a,b⟩

end Yulang.GeneralDeclarativeWitnessActualOpenBody359
