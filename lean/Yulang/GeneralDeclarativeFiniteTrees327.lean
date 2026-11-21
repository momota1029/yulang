import Yulang.GeneralDeclarativeFiniteCheck327

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeFiniteTrees327
open GeneralDeclarativeFiniteCheck327 (Annotated Justifies validate erase eraseMany)
open GeneralDeclarativeDemand320 (Demand)
open CommonRoleOutermostResolver (Tree All₂ Resolves Classify Summarizes)

mutual
theorem read {rules} (cert : Annotated) (proof : Justifies rules d cert) :
    Resolves rules d (erase cert) := by
  cases proof with
  | pending step => simpa only [erase] using Resolves.pending step
  | rejected step => simpa only [erase] using Resolves.rejected step
  | ambiguous step => simpa only [erase] using Resolves.ambiguous step
  | selected step children =>
    rw [erase]
    exact .selected step (read_many _ children)
termination_by sizeOf cert

theorem read_many {rules} (certs : List Annotated) (proof : All₂ (Justifies rules) ds certs) :
    All₂ (Resolves rules) ds (eraseMany certs) := by
  cases proof with
  | nil => simpa only [eraseMany] using (All₂.nil : All₂ (Resolves rules) [] [])
  | cons prior after =>
    rw [eraseMany]
    exact .cons (read _ prior) (read_many _ after)
termination_by sizeOf certs
end

mutual
theorem keep_calls {rules} (tree : Tree) (proof : Resolves rules d tree) :
    ∃ cert, erase cert = tree ∧ Justifies rules d cert := by
  cases proof with
  | pending step => exact ⟨.pending,by simp [erase],.pending step⟩
  | rejected step => exact ⟨.rejected,by simp [erase],.rejected step⟩
  | ambiguous step => exact ⟨.ambiguous,by simp [erase],.ambiguous step⟩
  | selected step children =>
    obtain ⟨notes,eq,transcript⟩ := keep_calls_many _ children
    exact ⟨.selected _ _ notes,by simp [erase,eq],.selected step transcript⟩
termination_by sizeOf tree

theorem keep_calls_many {rules} (trees : List Tree) (proof : All₂ (Resolves rules) ds trees) :
    ∃ certs, eraseMany certs = trees ∧ All₂ (Justifies rules) ds certs := by
  cases proof with
  | nil => exact ⟨[],by simp [eraseMany],.nil⟩
  | cons first rest =>
    obtain ⟨now,eq,readHere⟩ := keep_calls _ first
    obtain ⟨later,eqs,reads⟩ := keep_calls_many _ rest
    exact ⟨now :: later,by simp [eraseMany,eq,eqs],.cons readHere reads⟩
termination_by sizeOf trees
end

/-- Exact finite derivation verification through all four diagnostics.
This theorem is about supplied finite certificates; it makes no
search, stopping, or classification coverage claim for unsupported source. -/
theorem classifies_iff {rules localCheck}
    (exactHere : ∀ demand f, localCheck demand f = true ↔ rules demand f) :
    Classify rules d verdict ↔
      ∃ cert, validate localCheck d cert = true ∧ Summarizes (erase cert) verdict := by
  constructor
  · rintro ⟨tree,steps,summary⟩
    obtain ⟨cert,eq,witness⟩ := keep_calls tree steps
    exact ⟨cert,(GeneralDeclarativeFiniteCheck327.validates exactHere d cert).mpr witness,eq.symm ▸ summary⟩
  · rintro ⟨cert,valid,summary⟩
    exact ⟨erase cert,read cert ((GeneralDeclarativeFiniteCheck327.validates exactHere d cert).mp valid),summary⟩

end Yulang.GeneralDeclarativeFiniteTrees327
