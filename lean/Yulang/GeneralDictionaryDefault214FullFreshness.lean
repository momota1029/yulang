import Yulang.GeneralDictionaryDefault214ActualFullSources
import Yulang.GeneralDictionaryDefaultCandidateActual214

/-! Full original213 journal support detects historical invocation. Current
nonpoint head actual reads transport through that producer, without assuming
candidate head equations or replacing total packet meanings. -/
namespace Yulang.GeneralDictionaryDefault214FullFreshness
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionaryDefaultDepth208 (InstalledDepthBound)
open GeneralDictionaryDefaultEvidenceSplit212 (HistoricalInvocation)
open GeneralNominalMaterialization (Use)
open GeneralNominalOriginTerms (Same)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem support_historical
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (member : fresh context.state.seed focus.identity key 8 owner position ∈
      GeneralDictionaryDefaultJournalSupport213.journalSources state) :
    HistoricalInvocation state focus key := by
  obtain ⟨plan,registered,name,equal⟩ := GeneralDictionaryDefault214ActualFullSources.full_support_binder source bound path member
  have identity := GeneralDictionaryDefaultFreshActual214.binder_identity source bound path plan registered name equal
  exact ⟨plan,registered,identity.2.2.1,identity.2.2.2.1⟩

theorem fresh_support_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (unrecorded : ¬ HistoricalInvocation state focus key) :
    fresh context.state.seed focus.identity key 8 owner position ∉
      GeneralDictionaryDefaultJournalSupport213.journalSources state :=
  fun member => unrecorded (support_historical source bound path member)

theorem candidate_overlap (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (entry : Use) (present : entry ∈ candidate.headSchema.variables) (actual : entry.mode = .actual)
    (notOutput : entry.name ∉ candidate.packet.declaration.outputNames)
    (nonpoint : ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).1 ≠
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs entry.name).2)
    (overlap : candidate.binder entry.name ∈ GeneralDictionaryDefaultJournalSupport213.journalSources state)
    (valid : Models state model) : Same model entry.origin (.source (candidate.binder entry.name)) := by
  have seed := (congrArg (fun c : GeneralNominalCandidates.Context => c.state.seed) frame.context_eq).trans
    (GeneralDictionaryDefaultConfiguration209.seed (GeneralDictionaryDefaultTrace208.built_trace path))
  have allocated := GeneralNominalBinderIdentity181.binder_fresh candidate entry.name notOutput nonpoint
  rw [seed] at allocated
  rw [allocated] at overlap
  obtain ⟨historical,registered,name,equal⟩ := GeneralDictionaryDefault214ActualFullSources.full_support_binder source bound path overlap
  obtain ⟨nameEq,_,identity,decl,_,oldNonpoint⟩ :=
    GeneralDictionaryDefaultFreshActual214.binder_identity source bound path historical registered name equal
  subst name
  have declaration := GeneralDictionaryEmissionPlans.declaration_key_unique registry checked
    candidate.packet.declaration historical.packet.declaration frame.visible
    (GeneralDictionaryDefaultChoice214.visible_packets path historical.packet
      (GeneralDictionaryDefault214ActualSupport.registered_packets path historical registered)) decl.symm
  exact GeneralDictionaryDefaultCandidateActual214.candidate_nonpoint checked path historical candidate
    registered frame identity.symm declaration entry present actual notOutput nonpoint oldNonpoint valid
end Yulang.GeneralDictionaryDefault214FullFreshness
