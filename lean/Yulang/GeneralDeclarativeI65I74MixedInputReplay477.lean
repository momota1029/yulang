import Yulang.GeneralDeclarativeI65I74MixedFieldReport477

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open LiteralVisits473 (Checkpoint StepWire terminalIsField)
open ObservationAlternatives473 (Positions)
open ObservationSyntax471 (confirmedAddress)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)

theorem exact_independent_inline_seed_replays477
    {r : BeforeCapture (p := p) a gd w} {fixed : FixedFieldChoice476 r}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer atField : Checkpoint n}
    (seed : MixedInlineSeed477 fixed table rel outer atField) :
    readMixedInlineSeed477 fixed table rel outer atField = some seed := by
  rcases seed with ⟨pin,safe,ordinal,path,addr,anchor,stored,bit,checked⟩
  have op := (exact_named_cell_test476 ..).mpr pin
  simp only [readMixedInlineSeed477,op,dite_true]
  split
  · split
    · rename_i other named
      rw [addr] at named
      cases named
    · rename_i old route literal
      have both := ObservationSyntax471.Address.inline.inj (literal.symm.trans addr)
      obtain ⟨rfl,rfl⟩ := both
      simp only [anchor,dite_true]
      split
      · rename_i missing
        rw [stored] at missing
        contradiction
      · rename_i actual found
        have same := Option.some.inj (found.symm.trans stored)
        subst actual
        simp only [(eq_expr ..).mpr rfl,dite_true]
        split
        · rename_i missing
          rw [checked] at missing
          contradiction
        · rename_i value answer
          have same := Option.some.inj (answer.symm.trans checked)
          subst value
          rfl
  · rename_i failed
    exact (failed safe).elim

theorem inline_start_of_mixed_input_replays_its_literal_receipt477
    {r : BeforeCapture (p := p) a gd w} {fixed : FixedFieldChoice476 r}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer atField : Checkpoint n}
    (proof : MixedInlineSeed477 fixed table rel outer atField) :
    ∃ seed, readMixedInputSeed477 fixed table rel outer atField = some seed ∧
      seed.start = proof.point := by
  simp [readMixedInputSeed477,proof.addr,exact_independent_inline_seed_replays477 proof]

theorem named_start_of_mixed_input_replays_its_literal_receipt477
    {r : BeforeCapture (p := p) a gd w} {fixed : FixedFieldChoice476 r}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer atField : Checkpoint n} {i name}
    (addr : confirmedAddress fixed.original = .named name)
    (proof : NamedFieldQuotient476 fixed ⟨fixed.label,fixed.path,i⟩ table rel outer atField) :
    ∃ seed, readMixedInputSeed477 fixed table rel outer atField = some seed ∧
      seed.start = mixedPointFromChosenNamed477 (firstNamedCheckpoint477 proof) := by
  have anchored := exact_named_quotient_needs_no_supplied_ordinal477 fixed proof
    (exact_named_quotient_receipt_replays476 proof)
  simp [readMixedInputSeed477,addr,anchored]

theorem independent_mixed_source_and_full_trail_replay_exact_report477
    {r : BeforeCapture (p := p) a gd w} {fixed : FixedFieldChoice476 r}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer atField : Checkpoint n}
    {route : List (StepWire × Checkpoint n)} {trace : LocatedCapture476 w.offered}
    {chosen : MixedInputSeed477 fixed table rel outer atField} {finish : MixedPoint477 r table rel}
    (tail : terminalIsField ⟨atField,route⟩ = true)
    (capture : readLocatedAtHead476 r = some trace)
    (root : readMixedInputSeed477 fixed table rel outer atField = some chosen)
    (proof : MixedTrail477 trace chosen.start route finish) :
    ∃ report, readMixedFieldReport477 fixed table rel outer atField route = some report ∧
      report.result = finish ∧ report.captured = trace ∧ report.seed = chosen := by
  have routeRead := verified_mixed_trail_replays_to_same_exact_finish477 capture proof
  simp only [readMixedFieldReport477,tail,dite_true]
  split
  · rename_i no
    rw [capture] at no
    contradiction
  · rename_i seen checked
    have eq := Option.some.inj (checked.symm.trans capture)
    subst seen
    simp [root,routeRead]



theorem independent_original_inline_field_and_mix_reify_exact_finite_report477
    {r : BeforeCapture (p := p) a gd w} {fixed : FixedFieldChoice476 r}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer atField : Checkpoint n}
    {route : List (StepWire × Checkpoint n)} {trace : LocatedCapture476 w.offered}
    (seed : MixedInlineSeed477 fixed table rel outer atField)
    {finish : MixedPoint477 r table rel}
    (tail : terminalIsField ⟨atField,route⟩ = true)
    (capture : readLocatedAtHead476 r = some trace)
    (proof : MixedTrail477 trace seed.point route finish) :
    ∃ report, readMixedFieldReport477 fixed table rel outer atField route = some report ∧
      report.result = finish ∧ report.captured = trace := by
  obtain ⟨chosen,root,base⟩ := inline_start_of_mixed_input_replays_its_literal_receipt477 seed
  have same : MixedTrail477 trace chosen.start route finish := base.symm ▸ proof
  obtain ⟨report,read,ends,took,_⟩ :=
    independent_mixed_source_and_full_trail_replay_exact_report477 tail capture root same
  exact ⟨report,read,ends,took⟩

theorem independent_original_named_field_and_mix_reify_exact_finite_report477
    {r : BeforeCapture (p := p) a gd w} {fixed : FixedFieldChoice476 r}
    {table : Positions n} {rel : List (Fin n × Fin n)} {outer atField : Checkpoint n}
    {route : List (StepWire × Checkpoint n)} {trace : LocatedCapture476 w.offered}
    {i name}
    (addr : confirmedAddress fixed.original = .named name)
    (seed : NamedFieldQuotient476 fixed ⟨fixed.label,fixed.path,i⟩ table rel outer atField)
    {finish : MixedPoint477 r table rel}
    (tail : terminalIsField ⟨atField,route⟩ = true)
    (capture : readLocatedAtHead476 r = some trace)
    (proof : MixedTrail477 trace (mixedPointFromChosenNamed477 (firstNamedCheckpoint477 seed)) route finish) :
    ∃ report, readMixedFieldReport477 fixed table rel outer atField route = some report ∧
      report.result = finish ∧ report.captured = trace := by
  obtain ⟨chosen,root,base⟩ := named_start_of_mixed_input_replays_its_literal_receipt477 addr seed
  have same : MixedTrail477 trace chosen.start route finish := base.symm ▸ proof
  obtain ⟨report,read,ends,took,_⟩ :=
    independent_mixed_source_and_full_trail_replay_exact_report477 tail capture root same
  exact ⟨report,read,ends,took⟩

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475

