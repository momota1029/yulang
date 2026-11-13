import Yulang.GeneralDictionary172CheckerExact
import Yulang.GeneralDictionary171CheckedSpine

/-! The executable named-spine checker decides exactly the previously exposed
closed/point/physical-slot test obligations, not general semantic evidence. -/
namespace Yulang.GeneralDictionary172CheckedSpineExact
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionary171SpineDiscovery (Input RequestsFinished)
variable {roles : Roles.RoleDecls}

theorem check_iff (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (input : Input context root declaration) :
    GeneralDictionary171CheckedSpine.check registry context root declaration checked input = true ↔
      RequestsFinished registry context root declaration checked input := by
  simpa only [GeneralDictionary171CheckedSpine.check,
    GeneralDictionary171CheckedSpine.requests, RequestsFinished,
    GeneralDictionary172CheckerExact.At] using
    GeneralDictionary172CheckerExact.checkRequests_iff context.state context.interpretation
      (GeneralDictionary171CheckedSpine.requests registry context root declaration checked input)

theorem discover_iff (registry : Registry) (state : GeneralNominalSupport.Tracked roles)
    (root : Occurrence roles) (declaration : Declaration)
    (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (input : Input state.current.context root declaration) :
    (∃ node, GeneralDictionary171CheckedSpine.discover registry state root declaration visible checked input = some node) ↔
      RequestsFinished registry state.current.context root declaration checked input :=
  (GeneralDictionary171CheckedSpine.discover_success_iff registry state root declaration visible checked input).trans
    (check_iff registry state.current.context root declaration checked input)

/-- Failure denies only the sufficient finite certificate, not language acceptance. -/
theorem check_false_iff (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (input : Input context root declaration) :
    GeneralDictionary171CheckedSpine.check registry context root declaration checked input = false ↔
      ¬ RequestsFinished registry context root declaration checked input := by
  rw [← check_iff]
  cases GeneralDictionary171CheckedSpine.check registry context root declaration checked input <;> decide

end Yulang.GeneralDictionary172CheckedSpineExact
