import Yulang.GeneralMixedIndexedCompiler305
import Yulang.GeneralMixedReindexOutputFixture305

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralMixedReindexOutputCompiler305
open GeneralDictionaryOutputDepth252 (roles root registry)
open GeneralRebaseDepthScalar285 (refreshed)
open GeneralMixedReindexOutputFixture305 (widened coordinates)
open GeneralSourceDictionaries (Occurrence)
open GeneralMixedDiagnosticHead304 (boundary8)
open GeneralRebaseDiagnosticData268 (Inputs Valid)
open GeneralRebaseDiagnosticV8268 (Complete run)

def bits : Inputs (Occurrence roles) :=
  ⟨some false,some false,some false,some false,.unique (0,[]),
    fun key => if key = 0 then some false else none,some false,some false⟩

theorem complete : Complete bits := by
  refine ⟨by decide,by decide,by decide,by decide,by decide,?_,by decide,by decide⟩
  intro key cs specific
  have actual : (0,([] : List (Occurrence roles))) = (key,cs) :=
    GeneralRebasePartialClassification267.Verdict.unique.inj specific
  have zero : 0 = key := congrArg Prod.fst actual
  subst key
  decide

theorem original : Valid (boundary8 roles) registry refreshed root bits := by
  have selected := GeneralNominalVersionedMixedBoundary234.local_iff.mp
    (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp GeneralRebaseDepthHaltSelection285.selected)
  have ⟨middle,sharing⟩ := B4TargetV8.selected_iff.mp selected
  have ⟨last,merged⟩ := B4TargetV7.selected_iff.mp middle
  cases last with
  | selected safe unique outputs =>
    refine ⟨safe.1,safe.2.1,safe.2.2.1,safe.2.2.2,unique,?_,merged,sharing⟩
    intro key
    change GeneralRebasePartialBool268.Reflect _ (if key = 0 then some false else none)
    split
    · rename_i zero
      subst key
      exact outputs
    · trivial

variable (tag : Nat)

theorem widened_valid : Valid (boundary8 roles) registry (widened tag) root bits :=
  GeneralMixedIndexedCompiler305.valid_forward (GeneralMixedReindexObserver305.indexed (s := refreshed) (coordinates tag))
    (GeneralMixedReindexObserver305.semantics (s := refreshed) (coordinates tag)) registry root bits original

theorem actual_run : run bits = some (.selected 0 []) := rfl

theorem actual_compiler_shared :
    (∀ f, run bits = some f ↔ B4TargetV8.Local (boundary8 roles) registry refreshed root f) ∧
    (∀ f, run bits = some f ↔ B4TargetV8.Local (boundary8 roles) registry (widened tag) root f) :=
  ⟨GeneralRebaseDiagnosticV8268.exact_of_complete (boundary8 roles) registry refreshed root bits original complete,
   GeneralRebaseDiagnosticV8268.exact_of_complete (boundary8 roles) registry (widened tag) root bits (widened_valid tag) complete⟩

end Yulang.GeneralMixedReindexOutputCompiler305
