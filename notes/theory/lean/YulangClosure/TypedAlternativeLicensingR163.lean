import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.SourceContributionConstruction

/-!
R163 source-owner stop receipt, not a constructed typed Alt licensing case.

Selected native construction §3.4 requires the original selected branch/result
relation and dependent governed-field correspondence at the same whole tuple.
The existing SourceContributionConstruction already supplies conditional finite
Alt derivations, selected projection domains, and exact declared readback.
Its Relations.alternative is an independent local semantic input; its projection
recursor retains the selected child's licensed leaf fields. It neither derives
that relation from actual typed source-clause formation nor proves that those
leaf fields are the original result's governed fields. No such supplier or
dependent field diagram is present in the inspected existing interface.

The assigned R163 stop condition forbids supplying the desired diagram as a new
hypothesis. This module therefore adds NO theorem, relation, license or semantic
instance. It freshly checks the existing precise consumer types and audits the
reusable conditional results rather than duplicating their grammar. Original
P/A, source/native identification and production remain open. See the leased
R163 note/handoff for source sections, exact owner and next evidence.
-/

set_option pp.fullNames true
set_option pp.universes false
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.SourceContributionConstruction.selected_left_projection_domain with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.SourceContributionConstruction.selected_left_projection_domain is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.SourceContributionConstruction.selected_left_projection_domain"
#check @YulangClosure.SourceContributionConstruction.selected_left_projection_domain
#print axioms YulangClosure.SourceContributionConstruction.selected_left_projection_domain
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.SourceContributionConstruction.selected_left_projection_domain
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.SourceContributionConstruction.selected_left_projection_domain"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.SourceContributionConstruction.selected_right_projection_domain with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.SourceContributionConstruction.selected_right_projection_domain is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.SourceContributionConstruction.selected_right_projection_domain"
#check @YulangClosure.SourceContributionConstruction.selected_right_projection_domain
#print axioms YulangClosure.SourceContributionConstruction.selected_right_projection_domain
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.SourceContributionConstruction.selected_right_projection_domain
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.SourceContributionConstruction.selected_right_projection_domain"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.SourceContributionConstruction.alternative_keeps_other_partition with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.SourceContributionConstruction.alternative_keeps_other_partition is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.SourceContributionConstruction.alternative_keeps_other_partition"
#check @YulangClosure.SourceContributionConstruction.alternative_keeps_other_partition
#print axioms YulangClosure.SourceContributionConstruction.alternative_keeps_other_partition
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.SourceContributionConstruction.alternative_keeps_other_partition
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.SourceContributionConstruction.alternative_keeps_other_partition"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.SourceContributionConstruction.attachment_preserves_complete_field with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.SourceContributionConstruction.attachment_preserves_complete_field is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.SourceContributionConstruction.attachment_preserves_complete_field"
#check @YulangClosure.SourceContributionConstruction.attachment_preserves_complete_field
#print axioms YulangClosure.SourceContributionConstruction.attachment_preserves_complete_field
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.SourceContributionConstruction.attachment_preserves_complete_field
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.SourceContributionConstruction.attachment_preserves_complete_field"

-- These are existing input/consumer declarations, not new proof results.
#check @YulangClosure.SourceContributionConstruction.Relations.alternative
#check @YulangClosure.SourceContributionConstruction.DeclContribution.alternativeLeft
#check @YulangClosure.SourceContributionConstruction.DeclContribution.alternativeRight
