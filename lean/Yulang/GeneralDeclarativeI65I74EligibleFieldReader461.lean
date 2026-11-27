import Yulang.GeneralDeclarativeI65I74EligibleFieldStart461

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
open WrittenPattern460
open Checker408 (Problem)
open RetainedFull445 (FullProblem)
open RoutedReadyMixed457 (ReportAtField)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed)
open RoutedMixed456 (endsAtField)

structure ReadyRead (p : Problem) where
  Ticket : Type
  authority : EligibleStart p → Prop
  read : Ticket → Option (EligibleStart p)
  exact : ∀ a, (∃ t, read t = some a) ↔ authority a

structure EligibleWire {p : Problem} (h : ReadyRead p) where
  start : h.Ticket
  along : CompilerFieldWire p.state.core

def readEligibleField {p : Problem} (h : ReadyRead p) (w : EligibleWire h) :
    Option ReportAtField := do
  let a ← h.read w.start
  let (as,n,_) ← readAlreadyCompiledField p.state.core a.argument.lower
    (normalized (readTerm a.original)) a.query w.along
  return exactReport a.anchor as n

def EligibleScoped {p : Problem} (h : ReadyRead p) (r : ReportAtField) : Prop :=
  ∃ (a : EligibleStart p) (last : Term) (used : Bool),
    h.authority a ∧
    ScopedRaw p.state.core a.argument.lower (normalized (readTerm a.original))
      a.query r.path r.terminal last used ∧
    endsAtField r.path r.terminal = true ∧
    AliasCycle p.state.core.current.ordinary (observed p.state.core.current.ordinary) r.terminal ∧
    exactReport a.anchor r.path r.terminal = r

theorem exact_eligible_scope_iff_independent_finite_route {p : Problem} (h : ReadyRead p) (r : ReportAtField) :
    (∃ w, readEligibleField h w = some r) ↔ EligibleScoped h r := by
  constructor
  · rintro ⟨w,yes⟩
    cases hd : h.read w.start with
    | none => simp [readEligibleField,hd,Option.bind] at yes
    | some a =>
      cases go : readAlreadyCompiledField p.state.core a.argument.lower
          (normalized (readTerm a.original)) a.query w.along with
      | none => simp [readEligibleField,hd,go,Option.bind] at yes
      | some v =>
        obtain ⟨as,n,last⟩ := v
        have original : exactReport a.anchor as n = r := by
          simpa [readEligibleField,hd,go,Option.bind] using yes
        subst r
        obtain ⟨⟨used,scope⟩,atField,cycle⟩ :=
          (any_finite_scoped_field_has_exactly_its_structural_wire
            (anchor_compiles_the_normalized_original a.anchor)).mp ⟨w.along,go⟩
        exact ⟨a,last,used,(h.exact a).mp ⟨w.start,hd⟩,scope,atField,cycle,rfl⟩
  · rintro ⟨a,last,used,authority,scope,terminal,cycle,exactReport⟩
    obtain ⟨header,read⟩ := (h.exact a).mpr authority
    obtain ⟨trail,word⟩ := (any_finite_scoped_field_has_exactly_its_structural_wire
      (anchor_compiles_the_normalized_original a.anchor)).mpr ⟨⟨used,scope⟩,terminal,cycle⟩
    change readAlreadyCompiledField p.state.core a.argument.lower
      (normalized (readTerm a.original)) a.query trail = some (r.path,r.terminal,last) at word
    exact ⟨⟨header,trail⟩,by simp [readEligibleField,read,word,exactReport,Option.bind]⟩

theorem eligible_field_is_not_raw_parent_root {p : Problem} {h : ReadyRead p} {r : ReportAtField}
    (actual : EligibleScoped h r) : ¬ RootCycle p.state p.root := by
  obtain ⟨a,_,used,_,path,field,cyc,_⟩ := actual
  have term := exact_scope_reifies_full_trace_by_descent
    (anchor_compiles_the_normalized_original a.anchor) path
  have safe := (no_payload_can_stand_in_for_a_selected_field ⟨⟨used,term⟩,field,cyc⟩).2.1
  rintro ⟨input,found,yes⟩
  rw [a.originalArguments] at found
  cases List.mem_singleton.mp found
  exact safe yes

theorem exact_eligible_scope_has_same_fit_original_evidence {p : FullProblem}
    {h : ReadyRead p.old} {r : ReportAtField} (actual : EligibleScoped h r)
    (m : I72.Model) (fit : I72.FitsFull p.state m) :
    ∃ (a : EligibleStart p.old) (last : Term) (used : Bool),
      exactReport a.anchor r.path r.terminal = r ∧
      RoutedInlineStructural458.ModelTrail p.state.base.core m a.argument.lower a.query
        r.path r.terminal used ∧
      CoordinateWalk (fun _ => queryKeys p.state.base.core) a.argument.lower
        (normalized (readTerm a.original)) r.path r.terminal last ∧
      AliasCycle p.state.base.core.current.ordinary
        (observed p.state.base.core.current.ordinary) r.terminal := by
  obtain ⟨a,_,used,_,path,field,cyc,id⟩ := actual
  have t := exact_scope_reifies_full_trace_by_descent
    (anchor_compiles_the_normalized_original a.anchor) path
  obtain ⟨u,mh,wh,c⟩ := compiled_field_keeps_same_fit (s := p.state) ⟨⟨used,t⟩,field,cyc⟩ m fit
  exact ⟨a,_,u,id,mh,wh,c⟩

end Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
