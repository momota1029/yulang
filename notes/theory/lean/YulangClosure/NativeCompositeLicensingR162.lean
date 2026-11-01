import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.SourceSignatureConstruction
import YulangClosure.NativeProfileRestriction

/-!
R162 stopping evidence: the frozen graph does not encode composite semantics.

Selected source: source-signature-incidence-construction (2026-10-08) §3.4,
especially Alt's actual branch/result map, before its §4.2 DeclaredPort rule.
The graph's Node.alternative has an arbitrary result Catalogue and two graph
edges. It has no typed relation between that catalogue and either child.

This diagnostic graph is NOT a resolved/typed source construction and is NOT
a counterexample to the selected paper grammar, P, A, or source soundness.
It witnesses why the absent typed formation data cannot be reconstructed from
the frozen graph fields. We stop before defining a smaller DeclContribution
or postulating the missing projection. All source cases remain open.
-/
namespace YulangClosure.NativeCompositeLicensingR162

open SourceSignatureConstruction

set_option autoImplicit false

/-- A complete diagnostic leaf packet and independent license are inhabited. -/
def antecedentCatalogue : Catalogue Unit :=
  { Port := Unit, Packet := fun _ _ => Unit, scope := [], sharedSlot := fun _ => 0 }

/-- A supported result schema need not have any semantic packet. -/
def resultCatalogue : Catalogue Unit :=
  { Port := Unit, Packet := fun _ _ => Empty, scope := [], sharedSlot := fun _ => 0 }

def originalIntroduction : Introduction Unit :=
  { owner := 7, occurrence := 11, kind := .primitive,
    catalogue := antecedentCatalogue, License := fun _ _ _ => Unit }

/-- This is permitted by the frozen Graph datatype alone. No claim that its
arbitrary result catalogue was constructed by the selected IF builder. -/
def diagnosticGraph : Graph Unit :=
  { nodes := [.primitive originalIntroduction,
      .alternative 13 0 0 resultCatalogue],
    registration := fun _ => 17,
    substitution := fun _ row => row }

def originalLeaf : LeafLicensedField diagnosticGraph 0 () :=
  { occurrence := ⟨originalIntroduction, [],
      .introduction rfl (by simp [Node.introductions])⟩,
    port := (), packet := (), license := () }

/-- Even the non-leaf contextual provenance exists; it remains the original
leaf packet. It supplies no result packet at resultCatalogue. -/
def contextualLeaf : LeafLicensedField diagnosticGraph 1 () :=
  { occurrence := contextual rfl SourceEdge.alternativeLeft originalLeaf.occurrence,
    port := (), packet := (), license := () }

theorem original_leaf_license : Nonempty (LeafLicensedField diagnosticGraph 0 ()) :=
  ⟨originalLeaf⟩

theorem contextual_leaf_license : Nonempty (LeafLicensedField diagnosticGraph 1 ()) :=
  ⟨contextualLeaf⟩

theorem selected_branch_edge :
    SourceEdge (.alternative 13 0 0 resultCatalogue) (.alternative 13 false) 0 :=
  .alternativeLeft

theorem result_support : Nonempty (BuiltSupport diagnosticGraph 1) :=
  ⟨compileSupport ⟨.alternative 13 0 0 resultCatalogue, rfl, ()⟩⟩

theorem result_packet_empty (port : resultCatalogue.Port) :
    ¬ Nonempty (resultCatalogue.Packet () port) := by
  rintro ⟨packet⟩
  exact Empty.elim packet

/-- No total dependent packet injection is recoverable from these graph
fields. The selected Alt rule needs the actual branch/result relation and
its typed field correspondence, which are absent from Node.alternative. -/
theorem no_graph_only_branch_result_map :
    ¬ Nonempty ((port : antecedentCatalogue.Port) →
      antecedentCatalogue.Packet () port →
      Sigma (resultCatalogue.Packet ())) := by
  rintro ⟨transport⟩
  obtain ⟨port, packet⟩ := transport () ()
  exact result_packet_empty port ⟨packet⟩

theorem contextual_origin_unchanged :
    contextualLeaf.occurrence.owner = originalLeaf.occurrence.owner ∧
    contextualLeaf.occurrence.inherited = true := by
  exact ⟨rfl, rfl⟩

end YulangClosure.NativeCompositeLicensingR162

set_option pp.fullNames true
set_option pp.universes false
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.NativeCompositeLicensingR162.original_leaf_license with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.NativeCompositeLicensingR162.original_leaf_license is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.NativeCompositeLicensingR162.original_leaf_license"
#check @YulangClosure.NativeCompositeLicensingR162.original_leaf_license
#print axioms YulangClosure.NativeCompositeLicensingR162.original_leaf_license
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.NativeCompositeLicensingR162.original_leaf_license
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.NativeCompositeLicensingR162.original_leaf_license"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.NativeCompositeLicensingR162.contextual_leaf_license with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.NativeCompositeLicensingR162.contextual_leaf_license is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.NativeCompositeLicensingR162.contextual_leaf_license"
#check @YulangClosure.NativeCompositeLicensingR162.contextual_leaf_license
#print axioms YulangClosure.NativeCompositeLicensingR162.contextual_leaf_license
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.NativeCompositeLicensingR162.contextual_leaf_license
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.NativeCompositeLicensingR162.contextual_leaf_license"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.NativeCompositeLicensingR162.selected_branch_edge with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.NativeCompositeLicensingR162.selected_branch_edge is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.NativeCompositeLicensingR162.selected_branch_edge"
#check @YulangClosure.NativeCompositeLicensingR162.selected_branch_edge
#print axioms YulangClosure.NativeCompositeLicensingR162.selected_branch_edge
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.NativeCompositeLicensingR162.selected_branch_edge
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.NativeCompositeLicensingR162.selected_branch_edge"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.NativeCompositeLicensingR162.result_support with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.NativeCompositeLicensingR162.result_support is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.NativeCompositeLicensingR162.result_support"
#check @YulangClosure.NativeCompositeLicensingR162.result_support
#print axioms YulangClosure.NativeCompositeLicensingR162.result_support
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.NativeCompositeLicensingR162.result_support
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.NativeCompositeLicensingR162.result_support"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.NativeCompositeLicensingR162.result_packet_empty with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.NativeCompositeLicensingR162.result_packet_empty is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.NativeCompositeLicensingR162.result_packet_empty"
#check @YulangClosure.NativeCompositeLicensingR162.result_packet_empty
#print axioms YulangClosure.NativeCompositeLicensingR162.result_packet_empty
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.NativeCompositeLicensingR162.result_packet_empty
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.NativeCompositeLicensingR162.result_packet_empty"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.NativeCompositeLicensingR162.no_graph_only_branch_result_map with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.NativeCompositeLicensingR162.no_graph_only_branch_result_map is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.NativeCompositeLicensingR162.no_graph_only_branch_result_map"
#check @YulangClosure.NativeCompositeLicensingR162.no_graph_only_branch_result_map
#print axioms YulangClosure.NativeCompositeLicensingR162.no_graph_only_branch_result_map
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.NativeCompositeLicensingR162.no_graph_only_branch_result_map
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.NativeCompositeLicensingR162.no_graph_only_branch_result_map"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.NativeCompositeLicensingR162.contextual_origin_unchanged with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.NativeCompositeLicensingR162.contextual_origin_unchanged is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.NativeCompositeLicensingR162.contextual_origin_unchanged"
#check @YulangClosure.NativeCompositeLicensingR162.contextual_origin_unchanged
#print axioms YulangClosure.NativeCompositeLicensingR162.contextual_origin_unchanged
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.NativeCompositeLicensingR162.contextual_origin_unchanged
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.NativeCompositeLicensingR162.contextual_origin_unchanged"
