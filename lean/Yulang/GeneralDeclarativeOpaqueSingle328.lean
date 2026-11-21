import Yulang.GeneralDeclarativeOpaqueCapture328
import Yulang.GeneralDeclarativeOpaqueShared328
import Yulang.GeneralDeclarativeProducedNames325
import Yulang.GeneralDeclarativeFrameReadback325
import Yulang.GeneralDeclarativeSourceNames321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpaqueSingle328
open GeneralDeclarations (Registry Declaration Checked)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeGrowth327 (Extends derives fits)
open GeneralDeclarativeOpaquePlan328 (Plan Read Shape extract)
open GeneralDeclarativeOpaqueNested328 (Builds build run occurrences)
open GeneralDeclarativeOpaqueCapture328 (choose actual_binds ordered_keys)
open GeneralDeclarativeOpaqueConserve328 (Retains)
open GeneralDeclarativeTermWalk322 (Binds)
open GeneralDeclarativeOpaqueGroup328 (Sharing)
open GeneralDeclarativeFrameReadback325 (sourceNames)
open GeneralDeclarativeEmissionForest322 (Placement)
open GeneralDeclarativeTraceNames321 (names)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeNFHead324 (fact)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeEqualities322 (entails)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralDeclarationPatterns (normalize normalizeArgs)
open CommonRoleOutermostResolver (All₂)

def linear (keep : List Nat) (s : State) (a : Capture) (p : Plan) (fallback : Nat → Capture) :
    Nat → Capture :=
  fun n => choose fallback n (run keep s a p).binds

theorem input_list {d : Declaration} (one : d.head = [pat])
    (printed : translate c interp (normalize pat) = some e) : d.inputNames = names e := by
  rw [GeneralDeclarations.Declaration.inputNames,one,
    GeneralDeclarativeSourceNames321.actual_names _ printed]
  simp [normalizeArgs,GeneralDeclarationPatterns.variablesArgs]

theorem supported_plan {s : State} {p : Supported s done} (arg : Capture) (keep : List Nat)
    (fit : Bounds s arg) (shape : Shape code)
    (lo : Trace (restriction p) .lower arg.lower code ls)
    (hi : Trace (restriction p) .upper arg.upper code us) :
    ∃ plan, plan.code = code ∧ Builds s keep arg plan := by
  obtain ⟨plan,spell,visible⟩ := extract shape lo hi
  exact ⟨plan,spell,build keep plan arg fit visible⟩

/-- For an arbitrary checked single-argument declaration in the opaque
supported fragment, transport the constructed actual head to the
existing naming table used by the real ordered where/output compiler.
Only genuine source binders are read; reserved output-only keys are
not accidentally treated as captures. No claim that the original
state already contains the freshly constructed head projection. -/
theorem compiler_head {s t : State} {d : Demand} (checked : Checked r) (visible : impl ∈ r.declarations)
    (one : impl.head = [pat]) (args : d.arguments = [arg]) (range : Bounds s arg)
    (actual : Builds s keep arg plan) (noRepeat : (names plan.code).Nodup)
    (printed : translate r.constructors i (normalize pat) = some plan.code)
    (fallback : Nat → Capture) (place : Placement)
    (ordinary : Extends (run keep s arg plan).state t) :
    let b := linear keep s arg plan fallback
    (∀ n ∈ impl.inputNames, Bounds t (b n)) ∧
    All₂ (fun a p => Bounds t a ∧ Result t (fact r.constructors i (sourceNames impl place b).input a p))
      d.arguments impl.head := by
  let b := linear keep s arg plan fallback
  have listed := input_list one printed
  obtain ⟨_,limits⟩ := GeneralDeclarativeOpaqueCapture328.result actual noRepeat printed fallback
  have fresh : ((run keep s arg plan).binds.map Prod.fst).Nodup := (ordered_keys actual).symm ▸ noRepeat
  have binding : Binds t (sourceNames impl place b).input (occurrences (run keep s arg plan).binds) := by
    intro o present
    obtain ⟨⟨binder,span⟩,used,rfl⟩ := List.mem_map.mp present
    have inInput : binder ∈ impl.inputNames := by
      rw [listed,← ordered_keys actual]
      exact List.mem_map.mpr ⟨_,used,rfl⟩
    change GeneralDeclarativeEqualities322.Derives t (.variable span.center)
      (.variable ((sourceNames impl place b).input binder).center)
    unfold sourceNames
    rw [GeneralDeclarativeProducedNames325.exact_input (checked.2 impl visible) inInput]
    exact derives ordinary (actual_binds (fallback := fallback) fresh _ present)
  refine ⟨fun n used => fits ordinary (limits n (listed ▸ used)),?_⟩
  rw [args,one]
  exact .cons ⟨fits (GeneralDeclarativeGrowth327.trans actual.modeled.grows ordinary) range,
    GeneralDeclarativeForwardHead325.by_walk printed (entails (derives ordinary actual.center)) actual.ordered binding⟩ .nil

end Yulang.GeneralDeclarativeOpaqueSingle328
