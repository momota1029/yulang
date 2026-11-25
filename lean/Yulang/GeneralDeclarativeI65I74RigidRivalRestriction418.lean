import Yulang.GeneralDeclarativeI65I74RigidRivalPriority418

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RigidRival418
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Tree)
open Checker408 (Result)

-- Old-only paths must also keep earlier eligibility in every finite
-- ordered where child and in every completed output producer.
def OldTrace418 {s q t e} (tape : SourceTrace R10 s q t e) : Prop :=
  SourceTrace.rec (R := R10) (s := s)
    (motive_1 := fun _ _ _ _ => Prop) (motive_2 := fun _ _ _ => Prop)
    (motive_3 := fun _ _ => Prop)
    (fun _ => True) (fun _ _ _ _ producers => producers)
    (fun {q} {needs} {_trees} event _ _ _ _ producers children =>
      X6Ambiguous417.R9.elected s q event needs ∧ producers ∧ children)
    True (fun _ _ a b => a ∧ b)
    True (fun _ _ _ _ a b => a ∧ b) tape

def OldForest418 {s qs ts} (tape : WhereForest R10 s qs ts) : Prop :=
  WhereForest.rec (R := R10) (s := s)
    (motive_1 := fun _ _ _ _ => Prop) (motive_2 := fun _ _ _ => Prop)
    (motive_3 := fun _ _ => Prop)
    (fun _ => True) (fun _ _ _ _ producers => producers)
    (fun {q} {needs} {_trees} event _ _ _ _ producers children =>
      X6Ambiguous417.R9.elected s q event needs ∧ producers ∧ children)
    True (fun _ _ a b => a ∧ b)
    True (fun _ _ _ _ a b => a ∧ b) tape

def OldSupport418 {s ns} (tape : SupportForest R10 s ns) : Prop :=
  SupportForest.rec (R := R10) (s := s)
    (motive_1 := fun _ _ _ _ => Prop) (motive_2 := fun _ _ _ => Prop)
    (motive_3 := fun _ _ => Prop)
    (fun _ => True) (fun _ _ _ _ producers => producers)
    (fun {q} {needs} {_trees} event _ _ _ _ producers children =>
      X6Ambiguous417.R9.elected s q event needs ∧ producers ∧ children)
    True (fun _ _ a b => a ∧ b)
    True (fun _ _ _ _ a b => a ∧ b) tape

/-- A new local choice cannot silently change an old derivation. Keeping
the actual R9 eligibility throughout the *whole* finite dependency tree
lets us recover the same trace indices and exact ordered writes. -/
noncomputable def restrictOldTrace418 {s q t e} (now : SourceTrace R10 s q t e)
    (onlyEarlier : OldTrace418 now) :
    {prior : SourceTrace X6Ambiguous417.R9 s q t e //
      X6Ambiguous417.writes prior = writes now} := by
  exact SourceTrace.rec (R := R10) (s := s)
    (motive_1 := fun q t e now => OldTrace418 now →
      {prior : SourceTrace X6Ambiguous417.R9 s q t e //
        X6Ambiguous417.writes prior = writes now})
    (motive_2 := fun qs ts now => OldForest418 now →
      {prior : WhereForest X6Ambiguous417.R9 s qs ts //
        X6Ambiguous417.forestWrites prior = forestWrites now})
    (motive_3 := fun ns now => OldSupport418 now →
      SupportForest X6Ambiguous417.R9 s ns)
    (fun cycle _ => ⟨.rootK2 cycle,rfl⟩)
    (fun verdict cycle rule _ ask earlier =>
      ⟨.other verdict cycle rule (ask earlier),rfl⟩)
    (fun {q} {ns} {trees} event cycle _ supporters below priorNeeded priorChildren old => by
      change X6Ambiguous417.R9.elected s q event ns ∧
        OldSupport418 supporters ∧ OldForest418 below at old
      let kids := priorChildren old.2.2
      refine ⟨.selected event cycle old.1 (priorNeeded old.2.1) kids.val,?_⟩
      change Check408.encodedEventWrites event ++ X6Ambiguous417.forestWrites kids.val =
        Check408.encodedEventWrites event ++ forestWrites below
      rw [kids.property])
    (fun _ => ⟨.nil,rfl⟩)
    (fun before afterwards first rest old => by
      change OldTrace418 before ∧ OldForest418 afterwards at old
      let a := first old.1
      let b := rest old.2
      refine ⟨.cons a.val b.val,?_⟩
      change X6Ambiguous417.writes a.val ++ X6Ambiguous417.forestWrites b.val =
        writes before ++ forestWrites afterwards
      rw [a.property,b.property])
    (fun _ => .nil)
    (fun before elected exactRow after prelim later old => by
      change OldTrace418 before ∧ OldSupport418 after at old
      exact .cons (prelim old.1).val elected exactRow (later old.2))
    now onlyEarlier

theorem report_with_only_prior_source_rules_preserves_exact_bytes418
    {s q} {r : Result} {e}
    (now : SourceTrace R10 s q r.tree e)
    (same : CommonRoleOutermostResolver.Summarizes r.tree r.verdict)
    (exactWrites : r.writes = writes now) (old : OldTrace418 now) :
    X6Ambiguous417.ClassifiedAs s q r := by
  let former := restrictOldTrace418 now old
  exact ⟨e,former.val,same,exactWrites.trans former.property.symm⟩

theorem genuinely_new_report_must_use_a_new_local_choice418
    {s q} {r : Result} (new : ClassifiedAs s q r)
    (notBefore : ¬ X6Ambiguous417.ClassifiedAs s q r) :
    ∃ e, ∃ now : SourceTrace R10 s q r.tree e,
      ¬ OldTrace418 now ∧ CommonRoleOutermostResolver.Summarizes r.tree r.verdict ∧
      r.writes = writes now := by
  obtain ⟨e,now,verdict,receipts⟩ := new
  refine ⟨e,now,?_,verdict,receipts⟩
  intro older
  exact notBefore (report_with_only_prior_source_rules_preserves_exact_bytes418 now verdict receipts older)

theorem exact_rigid_scope_had_no_former_source_report418
    {s q} (actual : Winner s q) (r : Result) : ¬ X6Ambiguous417.ClassifiedAs s q r := by
  rintro ⟨e,trace,_,_⟩
  generalize r.tree = tree at trace
  cases trace with
  | rootK2 cyclic => exact X6Ambiguous417.root_safe417 actual.inspections cyclic
  | other _ _ prior _ => exact R9_diagnostics_excluded_by_actual_rigid_rival418 actual prior
  | selected event _ prior _ _ => exact no_old_election_on_rigid_rival418 actual event prior

theorem actual_C10_selected_report_strictly_extends_prior_classification418
    {p : Checker408.Problem} (a : Winner p.state p.root) :
    ClassifiedAs p.state p.root (Check408.nullaryReport a.winner.candidate.decl) ∧
    ¬ X6Ambiguous417.ClassifiedAs p.state p.root (Check408.nullaryReport a.winner.candidate.decl) := by
  exact ⟨exact_plain_merge_has_selected_report418 a,
    exact_rigid_scope_had_no_former_source_report418 a _⟩

end Yulang.GeneralDeclarativeI65.I72.RigidRival418
