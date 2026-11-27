import Yulang.GeneralDeclarativeI65I74InstalledGrammarEvidence462

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InstalledProtocolSum462
open Yulang.GeneralDeclarativeI65
open EligibleFieldStart461 WrittenPattern460
open Checker408 (Problem)
open GeneralDeclarations (Declaration)
open RoutedNominalMixed456 (actualQueryDecoder)
open RoutedMixed456 (endsAtField)
open InlineStructuralPolicy458 (policy liftCycle)


private theorem plain_pack_same_report (p : Problem) (d : Declaration)
    (h : RoutedReadyHeader457.AuthoredHeader p (actualQueryDecoder p.state.core) d)
    (w : RoutedInlineStructural458.FieldWire) :
    (RoutedInlineStructural458.packRead p d h w).map RoutedInlineStructural458.FieldDerivation.report = originalField (fromReady h) w.cursor := by
  unfold RoutedInlineStructural458.packRead originalField
  change _ = (AuthenticatedHop458.readCycle p.state.core.current.ordinary (policy p.state.core)
    h.arg.lower h.query (liftCycle p.state.core w.cursor)).bind _
  split
  · rename_i path n found
    conv => rhs; rw [found]
    split <;> rename_i last <;>
      simp [Option.bind,last,RoutedInlineStructural458.FieldDerivation.report,exactReport,fromReady,EligibleStart.anchor]
  · rename_i found
    conv => rhs; rw [found]
    rfl

theorem plain_original_report_projection (p : Problem) (w : RoutedInlineStructural458.FieldWire) :
    (RoutedInlineStructural458.readField p w).map RoutedInlineStructural458.FieldDerivation.report =
      (readActualHeader (provider p .plain) w.emptyKey).bind (fun a => originalField a w.cursor) := by
  unfold RoutedInlineStructural458.readField readActualHeader
  split
  · rename_i d only
    split
    · rename_i candidate seen
      have equal := List.singleton_inj.mp (seen.symm.trans only)
      subst candidate
      change (((RoutedReadyHeader457.readReadyHeader p (actualQueryDecoder p.state.core) d only w.emptyKey).bind _).map _) =
        ((RoutedReadyHeader457.readReadyHeader p (actualQueryDecoder p.state.core) d only w.emptyKey).map (fun h => fromReady h)).bind _
      cases actual : RoutedReadyHeader457.readReadyHeader p (actualQueryDecoder p.state.core) d only w.emptyKey with
      | none => rfl
      | some h => exact plain_pack_same_report p d h w
    · rename_i impossible
      exact (impossible _ only).elim
  · rename_i impossible
    split
    · rename_i d seen
      exact (impossible _ seen).elim
    · rfl


private theorem projected_pack_same_report (p : Problem) (d : Declaration)
    (h : ProjectedReadyHeader459.AuthoredHeader p (actualQueryDecoder p.state.core) d)
    (w : ProjectedClosedEntry459.FieldWire) :
    (ProjectedClosedEntry459.packRead p d h w).map ProjectedClosedEntry459.FieldDerivation.report = originalField (fromProjected h) w.cursor := by
  unfold ProjectedClosedEntry459.packRead originalField
  change _ = (AuthenticatedHop458.readCycle p.state.core.current.ordinary (policy p.state.core)
    h.arg.lower h.query (liftCycle p.state.core w.cursor)).bind _
  split
  · rename_i path n found
    conv => rhs; rw [found]
    split <;> rename_i last <;>
      simp [Option.bind,last,ProjectedClosedEntry459.FieldDerivation.report,exactReport,fromProjected,EligibleStart.anchor]
  · rename_i found
    conv => rhs; rw [found]
    rfl

theorem projected_original_report_projection (p : Problem) (w : ProjectedClosedEntry459.FieldWire) :
    (ProjectedClosedEntry459.readField p w).map ProjectedClosedEntry459.FieldDerivation.report =
      (readActualHeader (provider p .projected) w.emptyKey).bind (fun a => originalField a w.cursor) := by
  unfold ProjectedClosedEntry459.readField readActualHeader
  split
  · rename_i d only
    split
    · rename_i candidate seen
      have equal := List.singleton_inj.mp (seen.symm.trans only)
      subst candidate
      change (((ProjectedReadyHeader459.readReadyHeader p (actualQueryDecoder p.state.core) d only w.emptyKey).bind _).map _) =
        ((ProjectedReadyHeader459.readReadyHeader p (actualQueryDecoder p.state.core) d only w.emptyKey).map (fun h => fromProjected h)).bind _
      cases actual : ProjectedReadyHeader459.readReadyHeader p (actualQueryDecoder p.state.core) d only w.emptyKey with
      | none => rfl
      | some h => exact projected_pack_same_report p d h w
    · rename_i impossible
      exact (impossible _ only).elim
  · rename_i impossible
    split
    · rename_i d seen
      exact (impossible _ seen).elim
    · rfl


private theorem homogeneous_pack_same_report (p : Problem) (d : Declaration)
    (h : HomogeneousReadyHeader459.AuthoredHeader p (actualQueryDecoder p.state.core) d)
    (w : HomogeneousClosedEntry459.FieldWire) :
    (HomogeneousClosedEntry459.packRead p d h w).map HomogeneousClosedEntry459.FieldDerivation.report = originalField (fromHomogeneous h) w.cursor := by
  unfold HomogeneousClosedEntry459.packRead originalField
  change _ = (AuthenticatedHop458.readCycle p.state.core.current.ordinary (policy p.state.core)
    h.arg.lower h.query (liftCycle p.state.core w.cursor)).bind _
  split
  · rename_i path n found
    conv => rhs; rw [found]
    split <;> rename_i last <;>
      simp [Option.bind,last,HomogeneousClosedEntry459.FieldDerivation.report,exactReport,fromHomogeneous,EligibleStart.anchor]
  · rename_i found
    conv => rhs; rw [found]
    rfl

theorem homogeneous_original_report_projection (p : Problem) (w : HomogeneousClosedEntry459.FieldWire) :
    (HomogeneousClosedEntry459.readField p w).map HomogeneousClosedEntry459.FieldDerivation.report =
      (readActualHeader (provider p .homogeneous) w.emptyKey).bind (fun a => originalField a w.cursor) := by
  unfold HomogeneousClosedEntry459.readField readActualHeader
  split
  · rename_i d only
    split
    · rename_i candidate seen
      have equal := List.singleton_inj.mp (seen.symm.trans only)
      subst candidate
      change (((HomogeneousReadyHeader459.readReadyHeader p (actualQueryDecoder p.state.core) d only w.emptyKey).bind _).map _) =
        ((HomogeneousReadyHeader459.readReadyHeader p (actualQueryDecoder p.state.core) d only w.emptyKey).map (fun h => fromHomogeneous h)).bind _
      cases actual : HomogeneousReadyHeader459.readReadyHeader p (actualQueryDecoder p.state.core) d only w.emptyKey with
      | none => rfl
      | some h => exact homogeneous_pack_same_report p d h w
    · rename_i impossible
      exact (impossible _ only).elim
  · rename_i impossible
    split
    · rename_i d seen
      exact (impossible _ seen).elim
    · rfl

end Yulang.GeneralDeclarativeI65.I72.InstalledProtocolSum462
