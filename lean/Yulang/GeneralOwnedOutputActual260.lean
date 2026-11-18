import Yulang.GeneralOwnedOutputDecoder260
namespace Yulang.GeneralOwnedOutputActual260
open GeneralDictionaryOutputDepth252
open GeneralOutputRebaseSource260 (facts atom initialState finalState)

theorem keys_exact : GeneralRebaseOwnedOutputKeys260.keys 0
 (GeneralNominalVersionedPlans231.emittedSchema plan) = [.binder 2] := by
 rw [emitted_exact]
 rfl

def proposal := GeneralOwnedOutputDecoder260.compile plan 0 atom

theorem proposal_exact : proposal = .ok facts := by
 apply (GeneralOwnedOutputDecoder260.successful ..).mpr
 refine ⟨?_,_,GeneralOutputRebaseSource260.capture_exact,?_⟩
 · rw [emitted_exact]
 · rw [keys_exact]; rfl

def run (state : GeneralRebaseStep258.State facts) : Except GeneralOutputRebaseRun260.Failure
 (Option (GeneralRebaseStep258.State facts)) :=
 match proposal with
 | .error .unhandledReport => .error (.decode .unhandledReport)
 | .error .untranslatedOutputs => .error (.decode .untranslatedOutputs)
 | .ok proposed => match GeneralRebaseCheckedWrite259.commit state proposed with
   | .error outside => .error (.outside outside)
   | .ok result => .ok result

theorem run_equal (state : GeneralRebaseStep258.State facts) : run state = GeneralOutputRebaseRun260.run state := by
 simp only [run,proposal_exact,GeneralOutputRebaseRun260.run,GeneralOutputRebaseSource260.proposal_exact]
 rfl

theorem run_certificate (boundary : GeneralNominalCommonBridge.Assignment)
 (source : GeneralNominalState.Models snapshot boundary) :
 run initialState = .ok (some finalState) ∧ GeneralOutputRebasePublic260.Certificate boundary := by
 rw [run_equal]
 exact GeneralOutputRebasePublic260.run_certificate boundary source
end Yulang.GeneralOwnedOutputActual260
