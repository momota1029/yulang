import Yulang.GeneralDeclarativeI65I72SupportedChoice404

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (All₂ Dictionary Result Summarizes Tree)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

/-- The existing concrete authored branch is preserved. The new
selected branch cannot close without the actual SupportForest in
the SourceTrace constructor, even though it has a typed output and
post-selection equalities. The old negative cases are unchanged. -/
def supportedVariableSource404 : SourcePrimitives where
  elected := fun s q e needs =>
    variableWithNativeK2403.elected s q e needs ∨
      (Nonempty (SupportedEvent404 needs e) ∧
        (RetainedVariableOutputs403 e ∨ RetainedTypedValueRows403 e))
  other := variableWithNativeK2403.other

theorem supported_rules_keep_exact_rows404 : KeepsFixedOutputs404 supportedVariableSource404 :=
  fun _ _ _ _ via => via.elim (fun old => old.2.2) (fun new => new.2)

/-- An already genuine C403 derivation can supply the base producer
with the same State, diagnostic, event and exact original receipts. -/
noncomputable def preserve_c403_derivation404 {s q t event} (trace : SourceTrace variableWithNativeK2403 s q t event) :
    SourceTrace supportedVariableSource404 s q t event :=
  SourceTrace.rec (R := variableWithNativeK2403) (s := s)
    (motive_1 := fun q t e _ => SourceTrace supportedVariableSource404 s q t e)
    (motive_2 := fun qs ts _ => WhereForest supportedVariableSource404 s qs ts)
    (motive_3 := fun needs _ => SupportForest supportedVariableSource404 s needs)
    (fun cycle => .rootK2 cycle)
    (fun verdict safe old _ child => .other verdict safe old child)
    (fun e safe rule _ _ support kids => .selected e safe (.inl rule) support kids)
    .nil
    (fun _ _ first rest => .cons first rest)
    .nil
    (fun _ completed typed _ source rest => .cons source completed typed rest)
    trace

theorem preserve_c403_classifies404 {s q verdict} (original : Classifies variableWithNativeK2403 s q verdict) :
    Classifies supportedVariableSource404 s q verdict := by
  obtain ⟨t,e,⟨trace⟩,summary⟩ := original
  exact ⟨t,e,⟨preserve_c403_derivation404 trace⟩,summary⟩

/-- Recover authentic readiness from the trace actually built by
Classifies, not from arbitrary requests or from a separately selected
producer for the same name. In the output case, the producer is
literally read at the required index of the nested support field. -/
theorem actual_classifies_input404 {s q t e}
    (trace : SourceTrace supportedVariableSource404 s q t (some e))
    (a : Capture) (atArg : a ∈ q.demand.arguments) :
    Nonempty (ReadyInput404 supportedVariableSource404 s a) := by
  cases trace with
  | selected event safe localRule forest children =>
    rcases localRule with old|new
    · obtain ⟨read⟩ := old.2.1
      exact ⟨.authored (read.elected.scope.ready a atArg)⟩
    · obtain ⟨read⟩ := new.1
      exact ⟨recover_original_input404 supported_rules_keep_exact_rows404 forest
        (read.choice.input a atArg)⟩

private theorem supported_where_children404 {s qs ds}
    (children : All₂ (fun q d => Classifies supportedVariableSource404 s q (.selected d)) qs ds) :
    ∃ ts, Nonempty (WhereForest supportedVariableSource404 s qs ts) ∧
      All₂ Summarizes ts (ds.map Result.selected) := by
  induction children with
  | nil => exact ⟨[],⟨.nil⟩,.nil⟩
  | cons first rest ih =>
    obtain ⟨t,_,⟨trace⟩,one⟩ := first
    obtain ⟨ts,⟨tail⟩,many⟩ := ih
    exact ⟨t::ts,⟨.cons trace tail⟩,.cons one many⟩

/-- Actual selection and ordered children in the same fixed State.
The producer forest is a strict child of this exact new derivation.
B6 is looked up at the selected authored row (which is not inferred
from the producer, RHS, receipt, or fitted model). -/
theorem select_with_completed_inputs404 {s q d ds needs}
    (choice : SupportedChoice404 s q d needs)
    (safe : ¬RootCycle s q)
    (forest : SupportForest supportedVariableSource404 s needs)
    (retained : SupportedCenters404 choice)
    (clauses : LiteralVariableWhere403 d)
    (declared : DeclaredOriginalOutputs400 s.core q)
    (typed : ∀ origin : SelectedHeadOrigin395 (row := d) (supportedTape404 choice retained),
      NamedInputAtStoredHead401 s.b6 (supportedFrame404 origin))
    (fixed : ∀ origin : SelectedHeadOrigin395 (row := d) (supportedTape404 choice retained),
      RetainedOutputSources403 (s := s) (supportedFrame404 origin) ∨
        TypedRowsAtOriginalInput403 (s := s) (supportedFrame404 origin))
    (whereSelected : ∀ origin : SelectedHeadOrigin395 (row := d) (supportedTape404 choice retained),
      All₂ (fun child dict => Classifies supportedVariableSource404 s child (.selected dict))
        (frameWhereKids400 (supportedFrame404 origin)) ds) :
    Classifies supportedVariableSource404 s q (.selected (.node d.id ds)) := by
  obtain ⟨origin⟩ := selected_head_original_origin395 (actual_supported_tape404 choice safe retained)
  obtain ⟨out,_,_,_⟩ := stored_head_emits_exact_ordered_mixed_values401
    origin unusedPlacement403 (fun _ => emptyCapture403) choice.checked declared s.b6 (typed origin)
  let event : Event s q := ⟨supportedFrame404 origin,origin.pick.head,out⟩
  have read : SupportedEvent404 needs event := ⟨choice,retained,origin,rfl,rfl,clauses⟩
  have literal : RetainedVariableOutputs403 event ∨ RetainedTypedValueRows403 event :=
    (fixed origin).elim (fun alias => .inl (addressed_sources_give_real_output_rows403 event alias))
      (fun kinded => .inr (fun i => kinded i (out i)))
  obtain ⟨ts,⟨kids⟩,rows⟩ := supported_where_children404 (whereSelected origin)
  exact ⟨.selected d.id ts,some event,
    ⟨.selected event safe (.inr ⟨⟨read⟩,literal⟩) forest kids⟩,.selected rows (.selected rfl)⟩

/-- Root K2 does not read the list of eligible dependency proofs, nor
require that the pending producer can make a support forest. -/
theorem raw_k2_before_completed_inputs404 {s q} (raw : RootCycle s q) :
    Classifies supportedVariableSource404 s q .rejected ∧
      ∀ d, ¬ Classifies supportedVariableSource404 s q (.selected d) :=
  ⟨root_k2_is_rejected_for_every_primitive_system raw,fun _ => root_k2_never_selects raw⟩

end Yulang.GeneralDeclarativeI65.I72
