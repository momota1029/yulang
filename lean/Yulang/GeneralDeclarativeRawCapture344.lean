import Yulang.GeneralDeclarativeCommitCoverage344
import Yulang.GeneralDeclarativeLedger344
import Yulang.GeneralWhereOriginSupport318

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRawCapture344
open GeneralNominalCenters (Plan)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations (Registry)
open GeneralNominalVersionedExpressionFrame236 (variableSource variable_value)
open GeneralNominalVersionedFrame231 (capture binder)
open GeneralWhereVersionSemantics317 (Holds)
open GeneralDeclarativeCommitPosition344 (current_stamp)
open GeneralDeclarativeCommitPort344 (OperandMatch)
open GeneralDeclarativeCommitCoverage344 (batch_available)
open GeneralDeclarativeHead320 (State byMode)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeClauseBatch327 (prepare exact_projection)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralWhereVersionInstall317 (Journal Models InstallStep install)
open GeneralWhereOriginSupport318 (journalSources journal_models)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonNominalFullCarrier (Subtype subtype_refl)

def rawCap (p : Plan rs) (name : Nat) : Capture :=
  ⟨variableSource p .lower name,variableSource p .actual name,variableSource p .upper name⟩

theorem by_mode (p : Plan rs) (mode : GeneralNominalMaterialization.Mode) (n : Nat) :
    byMode (rawCap p n) mode = variableSource p mode n := by cases mode <;> rfl

theorem operands (p : Plan rs) (m : Assignment) (mode) (e) : OperandMatch p m (rawCap p) mode e := by
  intro key _
  rw [GeneralDeclarativeHead320.variables_eq,by_mode,variable_value]
  exact eqv_refl _

def inputLinks (p : Plan rs) (name : Nat) : List (Nat × Nat) :=
  [((rawCap p name).lower,(rawCap p name).center),((rawCap p name).center,(rawCap p name).upper)]

/-- Only the literal raw binder positions and their proved bounds. No
authored or completed-output row is fabricated in this base view. -/
def base (p : Plan rs) : State :=
  ⟨⟨[],p.packet.declaration.inputNames.flatMap (inputLinks p)⟩,[]⟩

theorem input_bounds (p : Plan rs) (name : Nat)
    (used : name ∈ p.packet.declaration.inputNames) : Bounds (base p) (rawCap p name) :=
  ⟨.interval (List.mem_flatMap.mpr ⟨name,used,List.mem_cons_self⟩),
   .interval (List.mem_flatMap.mpr ⟨name,used,List.mem_cons_of_mem _ List.mem_cons_self⟩)⟩

theorem intervals (p : Plan rs) (m : Assignment) (valid : Holds p m) (name : Nat)
    (used : name ∈ p.packet.declaration.inputNames) :
    Subtype (m (rawCap p name).lower).1 (m (rawCap p name).center).1 ∧
      Subtype (m (rawCap p name).center).1 (m (rawCap p name).upper).1 := by
  by_cases output : name ∈ p.packet.declaration.outputNames
  · simp only [rawCap,variableSource,output,ite_true]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · have promised := valid.captures name (.inl used)
    simp only [rawCap,variableSource,output,ite_false]
    exact promised

theorem modeled (p : Plan rs) (m : Assignment) (valid : Holds p m) :
    GeneralDeclarativeHead320.Models (base p) m := by
  refine ⟨⟨(by intro _ h; cases h),?_⟩,(by intro _ h; cases h)⟩
  intro bounds appears
  obtain ⟨name,used,which⟩ := List.mem_flatMap.mp appears
  obtain ⟨low,upper⟩ := intervals p m valid name used
  rcases List.mem_cons.mp which with same|rest
  · rw [same]
    exact low
  · rw [List.mem_singleton.mp rest]
    exact upper

noncomputable def keep (p : Plan rs) (j : Journal rs) (more : List Nat) :=
  (stateNames (base p) ++ journalSources j) ++ more

/-- Actual current install and any of its post-models produce a real
normalized input batch on the literal raw capture table. Fresh
ordinary names preserve the entire journal and all caller-protected
names. No overall source selection is asserted here. -/
theorem replay (r : Registry) (before : Journal rs) (ctx : GeneralNominalCandidates.Context)
    (p : Plan rs) (step : InstallStep r before (install before ctx p))
    (m : Assignment) (fit : Models (install before ctx p) m) (more : List Nat) :
    ∃ s ports n,
      prepare p.packet.registry.constructors p.packet.context.interpretation
        (keep p (install before ctx p) more) (rawCap p) (base p)
        p.packet.declaration.requirements = some (s,ports) ∧
      GeneralDeclarativeHead320.Models s n ∧ Models (install before ctx p) n ∧
      (∀ k ∈ journalSources (install before ctx p), n k = m k) ∧
      (∀ k ∈ more, n k = m k) := by
  have certified := current_stamp r before ctx p step m fit
  obtain ⟨s,ports,ran⟩ := batch_available p m certified.typed (base p)
    (keep p (install before ctx p) more) (rawCap p)
  have fact := exact_projection (protect := journalSources (install before ctx p) ++ more)
    p.packet.checked (fun _ h => h) (input_bounds p) (by simpa only [keep,List.append_assoc] using ran) m
  obtain ⟨n,valid,agrees⟩ := fact.mp (modeled p m certified.typed)
  have rawName : ∀ k ∈ journalSources (install before ctx p), n k = m k :=
    fun _ h => agrees _ (List.mem_append_right _ (List.mem_append_left _ h))
  have model : Models (install before ctx p) n :=
    (journal_models _ (fun k h => (rawName k h).symm)).mp fit
  exact ⟨s,ports,n,ran,valid,model,rawName,fun _ h => agrees _ (List.mem_append_right _ (List.mem_append_right _ h))⟩

end Yulang.GeneralDeclarativeRawCapture344
