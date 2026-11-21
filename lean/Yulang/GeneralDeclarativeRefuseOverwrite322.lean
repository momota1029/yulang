import Yulang.GeneralDeclarativeFootprint321
import Yulang.GeneralDeclarativeEqualities322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRefuseOverwrite322
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeEntailment320 (Holds appendFacts model_append)
open GeneralDeclarativeFootprint321 (equationNames value_same stateNames)
open GeneralDeclarativeEqualities322 (Derives entails)
open GeneralNominalCommonBridge (Assignment)

theorem equality_unchanged {row : Equation} {first last : Assignment}
    (keep : ∀ n ∈ equationNames row, first n = last n) :
    Holds first row ↔ Holds last row := by
  have tgt := keep row.left List.mem_cons_self
  have rhs := value_same first last .actual row.right
    (fun n seen => keep n (List.mem_cons_of_mem _ seen))
  simp only [Holds,tgt,rhs]

/-- If an existing caller target disagrees with its RHS in an original
model, there is no extension making that equation true while preserving
these logical names. Additional fresh names do not change this fact. -/
theorem no_overwrite {row : Equation} {old : Assignment}
    (fails : ¬Holds old row) :
    ¬∃ m : Assignment, Holds m row ∧ ∀ n ∈ equationNames row, m n = old n := by
  rintro ⟨extended,eqn,keep⟩
  exact fails ((equality_unchanged keep).mp eqn)

theorem not_conservative {s : State} {rows : List Equation} {row : Equation}
    (inNew : row ∈ rows) {m : Assignment} (fails : ¬Holds m row)
    (keptNames : equationNames row ⊆ stateNames s ++ extra) :
    ¬∃ after, Models (appendFacts s rows) after ∧
      ∀ n ∈ stateNames s ++ extra, after n = m n := by
  rintro ⟨after,valid,agrees⟩
  exact no_overwrite fails ⟨after,(model_append after).mp valid |>.2 row inNew,
    fun n kept => agrees n (keptNames kept)⟩

theorem no_ordinary_proof_when_model_fails {s : State} {m : Assignment}
    (valid : Models s m) (fails : ¬Holds m ⟨name,code⟩) : ¬Derives s (.variable name) code :=
  fun proof => fails (entails proof m valid)

end Yulang.GeneralDeclarativeRefuseOverwrite322
