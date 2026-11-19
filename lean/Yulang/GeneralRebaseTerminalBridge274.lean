import Yulang.GeneralRebaseTerminalMachine274

set_option maxRecDepth 17000
set_option maxHeartbeats 5000000
namespace Yulang.GeneralRebaseTerminalBridge274
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryOptionalInitial229 (registry sourceRegistry declaration)
open GeneralDictionaryVersionedInitialFrame233 (before)
open GeneralDictionaryVersionedPointStage233 (point)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralRebaseTerminalPublic274 (first)
open GeneralRebaseTerminalMachine274 (Stage Event Step Public next owner replay firstBindings pointBindings)
open GeneralRebaseCompoundRows273 (Agrees)
open GeneralRebaseTerminalRows274 (HasLeaf)

noncomputable def raw : Stage → State roles
 | .source => before
 | .installed => first
 | .observed => point
 | .terminal => installed

theorem phase_edges {s t : Stage} (accepted : Step s t) :
 (s = .source ∧ t = .installed) ∨
 (s = .installed ∧ t = .observed) ∨
 (s = .observed ∧ t = .terminal) := by
 obtain ⟨e,h⟩ := accepted
 unfold next at h
 split at h <;> try contradiction
 all_goals split at h <;> try contradiction
 all_goals cases Option.some.inj h
 · exact Or.inl ⟨rfl,rfl⟩
 · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
 · exact Or.inr (Or.inr ⟨rfl,rfl⟩)

theorem realized {s t : Stage} (step : Step s t) :
 GeneralNominalVersionedKernel232.Step registry root (raw s) (raw t) := by
 rcases phase_edges step with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
 · exact GeneralDictionaryVersionedInitialStep233.step
 · exact GeneralDictionaryVersionedPointStage233.step
 · exact GeneralDictionaryVersionedSecondStep233.step

theorem mixed_realized {s t : Stage} (step : Step s t) :
 GeneralNominalVersionedMixedKernel234.Step registry root (raw s) (raw t) := GeneralNominalVersionedMixedKernel234.old_step (realized step)

theorem trace_realized (startAt : Stage) (inputs : List Event) (finish : Stage)
 (run : replay startAt inputs = some finish) :
 B4Target.Steps (GeneralNominalVersionedKernel232.Step registry root) (raw startAt) (raw finish) := by
 induction inputs generalizing startAt with
 | nil =>
   cases Option.some.inj run
   exact .refl
 | cons input rest ih =>
   cases found : next startAt input with
   | none => simp [replay,found,Option.bind] at run
   | some intermediate =>
     have restRun : replay intermediate rest = some finish := by simpa [replay,found,Option.bind] using run
     have head := realized ⟨input,found⟩
     have tail := ih intermediate restRun
     exact GeneralRebaseWeakTerminal268.append (.tail .refl head) tail

theorem old_bindings : GeneralDictionaryOptionalInstall229.packet.bindings = firstBindings :=
 GeneralDictionaryOptionalInstall229.bindings_exact

theorem new_bindings : GeneralDictionaryVersionedSecondInstall233.plan.packet.bindings = pointBindings :=
 GeneralDictionaryVersionedPoint233.bindings_exact _ _ _

theorem genuine_route :
 replay .source [.install owner GeneralDictionaryOptionalInstall229.packet.bindings 2,
   .observe owner GeneralDictionaryVersionedSecondInstall233.plan.packet.bindings 2,.service owner] = some .terminal := by
 rw [old_bindings,new_bindings]
 rfl

theorem public_agrees (stage : Stage) (boundary : Assignment) :
 Public stage boundary ↔ GeneralRebaseCompoundRowsMeaning273.Public (raw stage) boundary := by
 cases stage
 · exact (GeneralRebaseTerminalMachine274.initial boundary).trans (GeneralRebaseTerminalRows274.before_public boundary).symm
 · exact (GeneralRebaseTerminalMachine274.after_install (by decide) boundary).trans (GeneralRebaseTerminalRows274.first_public boundary).symm
 · exact (GeneralRebaseTerminalMachine274.after_install (by decide) boundary).trans (GeneralRebaseTerminalRows274.point_public boundary).symm
 · exact (GeneralRebaseTerminalMachine274.after_install (by decide) boundary).trans (GeneralRebaseTerminalRows274.terminal_public boundary).symm

theorem terminal_evidence (boundary : Assignment) (can : Public .terminal boundary) :
 ∃ m, Agrees m boundary ∧ Models (raw .terminal) m ∧ HasLeaf m :=
 (GeneralRebaseTerminalRows274.terminal_leaf_exact boundary).mpr
  ((GeneralRebaseTerminalMachine274.after_install (by decide) boundary).mp can)

end Yulang.GeneralRebaseTerminalBridge274
