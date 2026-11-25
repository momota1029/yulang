import Yulang.GeneralDeclarativeI65I74WhereListCoherence411

namespace Yulang.GeneralDeclarativeI65.I72.WhereCycle411.CertificateBoundary
open GeneralDeclarativeI65 (B6OccurrenceAtlas401 visible)
open List410 (ListWire invariantValue410 listPoint410 checkExactEscape)
open GeneralDeclarativeWitnessSparseVariance357 (Source compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataRows291 (Row)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeDemand320 (Demand)
open CommonNominalFullCarrier (Ty Subtype Equivalent nominal variant)
open PresenceNormalForm (Atom)
open Checker408 (Problem Result)

def bodies : Source 0 0 0 := ⟨[],Fin.elim0,Fin.elim0⟩
def implShowList : Declaration := ⟨88,7,[.app 90 [.var 3]],[⟨4,7,[.var 3],[]⟩],[],[]⟩
def surface : InputBundle :=
  let rows : List Row := [⟨90,some ⟨[.type],90⟩,.invariant⟩]
  ⟨⟨.absent,rows⟩,⟨.absent,rows⟩,⟨0,[⟨7,1,[]⟩]⟩,[implShowList]⟩

def rootRow : Equation := ⟨0,.nominal 90 [.variable 1]⟩
def loopRow : Equation := ⟨1,.variant 8 (.variable 1)⟩
def atom : Atom Nat := .tyLe (.var 1) (.var 1)
def ordinary : GeneralDeclarativeHead320.State := ⟨⟨[atom],[]⟩,[rootRow,loopRow]⟩
def request : Demand := ⟨7,[⟨0,0,0⟩],[]⟩
def payloadRequest : Demand := ⟨7,[⟨1,1,1⟩],[]⟩

def problem : Option Problem := do
  let graph ← compile bodies
  let resolved ← GeneralSourceMetadataBareBundle291.compile surface
  let environment : Environment := ⟨0,0,0,bodies,graph,resolved⟩
  let state : GeneralDeclarativeI65.State :=
    ⟨⟨environment,ordinary,[]⟩,List.replicate 90 [] ++ [[invariantValue410]],
      [⟨0,[42],listPoint410 90 1⟩],[]⟩
  let b6 : B6OccurrenceAtlas401 state := ⟨fun _ _ _ _ => none⟩
  pure ⟨⟨state,b6⟩,⟨[27],request⟩⟩

def expected : Result := expected411 implShowList
def parentWire : ListWire := ⟨0,⟨[0,1],[0,1]⟩⟩
def payloadCycleWire : GeneralDeclarativeWitnessCycle350.Wire :=
  ⟨0,⟨1,.same,1⟩,[],.same⟩

def wire : CycleWire := ⟨parentWire,payloadCycleWire⟩

def test (p : Option Problem := problem) (r : Result := expected)
    (tag : Witness := .whereChild wire) : Bool :=
  (p.map fun data => check data r tag).getD false

def rewriteOrdinary (p : Problem) (raw : GeneralDeclarativeHead320.State) : Problem :=
  let state := {p.state.core with current := {p.state.core.current with ordinary := raw}}
  let atlas : B6OccurrenceAtlas401 state := ⟨fun _ _ _ _ => none⟩
  ⟨⟨state,atlas⟩,p.root⟩

theorem x9_exact_tree_check_returns_true411 : test = true := by decide +kernel

end Yulang.GeneralDeclarativeI65.I72.WhereCycle411.CertificateBoundary

namespace Yulang.GeneralDeclarativeI65.I72.WhereCycle411.CertificateBoundary.MixedCutProbe
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeK2Graph321 (Descends Path)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed structural)
open GeneralDeclarativeWitnessRank350 (rank)

open CommonNominalFullCarrier (Ty Equivalent nominal)
open List410 (colour ExactEscapeWire checkExactEscape exactShapeEscape aliasRanks exact_escape_tracks_original_edge410
  exact_escape_preserves_alias_side410 aliasRanks_eq_on_original_alias410 listPoint410)
open GeneralDeclarativeI65
def nuNomState : CommonNominalSyntax.State Common.Row :=
  .block [.nominal 90 [.inl (.inl 0)]] 0

def nuNom : Ty := .nominal 90 [.inl nuNomState]

theorem nu_named_observations411 (depth : Nat) :
    CommonNominalFullCarrier.observeTy depth nuNom =
      CommonNominalFullCarrier.observeTy depth (nominal 90 [.inl nuNom]) := by
  cases depth <;> rfl

theorem nu_named_unfold_equivalent411 : Equivalent nuNom (nominal 90 [.inl nuNom]) := by
  constructor <;> intro depth <;> rw [←nu_named_observations411 depth] <;>
    exact CommonNominalFullDemand.producerLe_refl _

def nestedModel : I72.Model :=
  ⟨fun n => ((if n = 0 then nominal 90 [.inl nuNom] else nuNom),Common.rowEmpty),
    fun _ => none,fun n => if n = 0 then some (listPoint410 90 1) else none⟩

def listRow : Equation := ⟨0,.nominal 90 [.variable 1]⟩
def loopRow : Equation := ⟨1,.nominal 90 [.variable 1]⟩
def equalityRow : Equation := ⟨1,.variable 2⟩

/-- A mixed cycle in the *ordering restrictions* is not necessarily
an alias in the actual graph: Bounds do not read flat equations. -/
def split : GeneralDeclarativeHead320.State :=
  ⟨⟨[CertificateBoundary.atom],[(0,1),(2,0)]⟩,[listRow,loopRow,equalityRow]⟩

def order : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | k+3 => k+3

theorem order_one_exact411 (n : Nat) : order n = 1 ↔ n = 0 := by
  cases n with
  | zero => simp [order]
  | succ n =>
    cases n with
    | zero => simp [order]
    | succ n =>
      cases n with
      | zero => simp [order]
      | succ n => simp [order]

theorem actual_bound_respects_order411 {a b} (fact : Bound split.normal a b) :
    order a ≤ order b := by
  induction fact with
  | interval exact =>
    simp only [split,List.mem_cons,List.not_mem_nil,or_false] at exact
    rcases exact with h|h <;> obtain ⟨rfl,rfl⟩ := Prod.mk.inj h <;> decide
  | constraint atomAt =>
    have got := List.mem_singleton.mp atomAt
    simp [CertificateBoundary.atom] at got
    obtain ⟨rfl,rfl⟩ := got
    exact Nat.le_refl _
  | refl => exact Nat.le_refl _
  | trans _ _ a b => exact Nat.le_trans a b

theorem flat_actual_eq411 {a b} (inEq : (⟨a,.variable b⟩ : Equation) ∈ split.equations) :
    a = 1 ∧ b = 2 := by
  simpa [split,listRow,loopRow,equalityRow] using inEq

theorem aliases_preserve_zero411 {a b} (rel : GeneralDeclarativeLowerKnown321.Alias split a b) : a = 0 ↔ b = 0 := by
  induction rel with
  | bounds lo hi =>
    have same := Nat.le_antisymm (actual_bound_respects_order411 lo) (actual_bound_respects_order411 hi)
    exact (order_one_exact411 _).symm.trans (same ▸ order_one_exact411 _)
  | forward row => obtain ⟨rfl,rfl⟩ := flat_actual_eq411 row; decide
  | backward row => obtain ⟨rfl,rfl⟩ := flat_actual_eq411 row; decide
  | trans _ _ a b => exact a.trans b

theorem all_actual_children_are_one411 {a b}
    (here : Descends (structural split) a b) : b = 1 := by
  obtain ⟨shape,raw,child⟩ := here
  obtain ⟨owner,_,expr,found,decoded⟩ := raw
  have choice : (⟨owner,expr⟩ : Equation) = listRow ∨ (⟨owner,expr⟩ : Equation) = loopRow ∨
      (⟨owner,expr⟩ : Equation) = equalityRow := by
    simpa only [split,List.mem_cons,List.not_mem_nil,or_false] using found
  rcases choice with eq|eq|eq
  · have rhs := congrArg Equation.right eq
    change expr = listRow.right at rhs
    rw [rhs] at decoded
    have coded : some (GeneralDeclarativeK2Graph321.Shape.nominal 90 [1]) = some shape := decoded
    cases Option.some.inj coded
    exact List.mem_singleton.mp child
  · have rhs := congrArg Equation.right eq
    change expr = loopRow.right at rhs
    rw [rhs] at decoded
    have coded : some (GeneralDeclarativeK2Graph321.Shape.nominal 90 [1]) = some shape := decoded
    cases Option.some.inj coded
    exact List.mem_singleton.mp child
  · have rhs := congrArg Equation.right eq
    change expr = equalityRow.right at rhs
    rw [rhs] at decoded
    cases decoded

theorem any_actual_tail_stays_one411 {a b} (tail : Path (structural split) a b) (starts : a = 1) :
    b = 1 := by
  induction tail with
  | refl => exact starts
  | next first _ ih => exact ih (all_actual_children_are_one411 first)

theorem no_actual_return411 : ¬AliasCycle split (observed split) 0 := by
  rintro ⟨first,last,step,next,alias⟩
  have payload := any_actual_tail_stays_one411 next (all_actual_children_are_one411 step)
  have zero := (aliases_preserve_zero411 alias).mpr rfl
  omega

theorem necessary_rank_merge411 (w : ExactEscapeWire) :
    checkExactEscape split 0 w = false := by
  cases tested : checkExactEscape split 0 w with
  | false => rfl
  | true =>
    exfalso
    have policy : aliasRanks split (rank w.ranks) = true :=
      ((Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp tested).1).1)
    have intervals := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp policy).1).2
    have f : rank w.ranks 0 ≤ rank w.ranks 1 :=
      of_decide_eq_true (List.all_eq_true.mp intervals (0,1) (by decide))
    have g : rank w.ranks 2 ≤ rank w.ranks 0 :=
      of_decide_eq_true (List.all_eq_true.mp intervals (2,0) (by decide))
    have identical := aliasRanks_eq_on_original_alias410 policy
      (GeneralDeclarativeLowerKnown321.Alias.forward (a := 1) (b := 2) (by simp [split,equalityRow]))
    have rankSame : rank w.ranks 0 = rank w.ranks 1 := by omega
    have sideSame : w.side 0 = w.side 1 := congrArg (colour w.palette) rankSame
    have z : w.side 0 = 0 := of_decide_eq_true ((Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp tested).1).2)
    have realEdge : Descends (structural split) 0 1 :=
      ⟨.nominal 90 [1],GeneralDeclarativeGraphRows321.literal_head (exp := listRow.right) (by simp [split,listRow])
        rfl,List.mem_cons_self⟩
    have after := exact_escape_tracks_original_edge410 tested (by simp [z]) realEdge
    omega

#print axioms no_actual_return411
#print axioms necessary_rank_merge411


open Checker408 (Problem)
open CommonNominalFullCarrier (subtype_refl)

theorem mixed_raw_boundary_has_real_fitting_model411 {p : Problem} (got : problem = some p) :
    I72.Fits (rewriteOrdinary p split).state nestedModel := by
  unfold problem at got
  cases sparse : GeneralDeclarativeWitnessSparseVariance357.compile bodies with
  | none => simp [sparse] at got
  | some sem =>
    cases authored : GeneralSourceMetadataBareBundle291.compile surface with
    | none => simp [sparse,authored] at got
    | some tbl =>
      simp only [sparse,authored,Option.pure_def] at got
      cases got
      refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
      · intro a mem
        have equal : a = atom := List.mem_singleton.mp mem
        cases equal
        exact subtype_refl _
      · intro pair landed
        change pair ∈ [(0,1),(2,0)] at landed
        have exactPair : pair = (0,1) ∨ pair = (2,0) := by
          simpa only [List.mem_cons,List.not_mem_nil,or_false] using landed
        rcases exactPair with rfl|rfl
        · exact nu_named_unfold_equivalent411.2
        · exact nu_named_unfold_equivalent411.1
      · intro e atRow
        change e ∈ [listRow,loopRow,equalityRow] at atRow
        have options : e = listRow ∨ e = loopRow ∨ e = equalityRow := by
          simpa only [List.mem_cons,List.not_mem_nil,or_false] using atRow
        rcases options with rfl|rfl|rfl
        · exact ⟨subtype_refl _,subtype_refl _⟩
        · exact nu_named_unfold_equivalent411
        · exact ⟨subtype_refl _,subtype_refl _⟩
      · intro _ empty; cases empty
      · intro item seen
        have eq : item = (⟨0,[42],listPoint410 90 1⟩ : GeneralDeclarativeI65.Origin) :=
          List.mem_singleton.mp seen
        cases eq
        rfl

#print axioms mixed_raw_boundary_has_real_fitting_model411

open GeneralDeclarations (Declaration)
open PresenceNormalForm (Atom)

theorem original_x9_demand411 {p : Problem} (got : problem = some p) :
    p.root.demand.arguments = [⟨0,0,0⟩] ∧
    p.state.core.current.ordinary.normal.ordinary = [CertificateBoundary.atom] ∧
    p.state.core.origins = [⟨0,[42],listPoint410 90 1⟩] := by
  unfold problem at got
  cases sparse : GeneralDeclarativeWitnessSparseVariance357.compile bodies with
  | none => simp [sparse] at got
  | some sem =>
    cases authored : GeneralSourceMetadataBareBundle291.compile surface with
    | none => simp [sparse,authored] at got
    | some tbl =>
      simp only [sparse,authored,Option.pure_def] at got
      cases got
      exact ⟨rfl,rfl,rfl⟩

def whereOnBiggerRaw {p : Problem} {d : Declaration}
    (data : WhereListHead p.state p.root d) (raw : GeneralDeclarativeHead320.State)
    (keep : ∀ a ∈ p.state.core.current.ordinary.normal.ordinary, a ∈ raw.normal.ordinary) :
    WhereListHead (rewriteOrdinary p raw).state (rewriteOrdinary p raw).root d :=
  ⟨data.only,data.authoredRole,data.validRoles,data.checked,data.covered,
    data.arg,data.asked,data.key,data.binder,data.named,data.origin,data.authored,
    data.lower,data.center,data.upper,data.payload,data.endpoint,data.use,data.mode,data.table,
    keep _ data.atom,data.clause,data.exactWhere,data.whereRole,data.whereArgs,data.whereOutputs,data.noOutputs⟩

theorem mixed_scope_rejects_every_official_where_wire411 {p : Problem}
    (got : problem = some p) (w : CycleWire) (reported : Check408.Result) :
    check (rewriteOrdinary p split) reported (.whereChild w) = false := by
  let new := rewriteOrdinary p split
  cases visited : check new reported (.whereChild w) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨d,_,packet,replayed,_,_⟩ := accepted_where_wire_reflects_actual_child411 new reported w visited
    have args : new.root.demand.arguments = [⟨0,0,0⟩] := (original_x9_demand411 got).1
    have impossible : checkExactEscape new.state.core.current.ordinary 0 w.parent.escape = false :=
      necessary_rank_merge411 w.parent.escape
    simp only [replayWhereList411] at replayed
    split at replayed <;> try contradiction
    split at replayed <;> try contradiction
    split at replayed
    · rename_i key binder arg clause named actual _
      have same := (List.cons.inj (actual.symm.trans args)).1
      cases same
      split at replayed <;> try contradiction
      split at replayed <;> try contradiction
      simp [impossible] at replayed
    · contradiction

/-- The old branches also cannot produce a report for this snapshot:
the newly introduced R3 parent is distinct and no raw root / prior
candidate-local veto exists there. This is only a coverage boundary. -/
theorem no_earlier_where_exception411 {p : Problem} {d : Declaration}
    (read : VerifiedWhereList p d) (reported : Check408.Result) :
    ∀ old, check p reported (.previous old) = false := by
  intro w
  cases run : check p reported (.previous w) with
  | false => rfl
  | true =>
    exfalso
    have yes : List410.check p reported w = true := run
    obtain ⟨e,t,_,_⟩ := (List410.check_sound p reported w yes).1
    generalize reported.tree = shape at t
    cases t with
    | rootK2 root => exact read.rawSafe root
    | other _ _ rule _ => exact invariant_list_keeps_actual_inspection_priority411 read.known rule
    | selected event _ rule _ _ =>
      exact no_prior_R2_election_of_actual_where_parent411 read.known event rule

theorem actual_mixed_where_gap_is_nonvacuous411 :
    ∃ p, problem = some p ∧
      let new := rewriteOrdinary p split
      ClassifiedAs new.state new.root expected ∧
      I72.Fits new.state nestedModel ∧
      ReportEvidence new.state nestedModel new.root expected ∧
      ∀ w, check new expected w = false := by
  have accepted := x9_exact_tree_check_returns_true411
  unfold test at accepted
  cases got : problem with
  | none => simp [got] at accepted
  | some p =>
    have exactOld : check p expected (.whereChild wire) = true := by simpa [got] using accepted
    obtain ⟨d,_,packet,_,_,older⟩ := accepted_where_wire_reflects_actual_child411 p expected wire exactOld
    let new := rewriteOrdinary p split
    let source := whereOnBiggerRaw packet.known split (by
      intro a used
      rw [(original_x9_demand411 got).2.1] at used
      exact used)
    have safe : ¬RootCycle new.state new.root := by
      rintro ⟨arg,reached,cycle⟩
      have args : new.root.demand.arguments = [⟨0,0,0⟩] := (original_x9_demand411 got).1
      rw [args] at reached
      cases List.mem_singleton.mp reached
      exact no_actual_return411 cycle
    have childCycle : RootCycle new.state source.child := by
      have payload : source.payload = 1 := by
        have originalOrigins := (original_x9_demand411 got).2.2
        have mem := packet.known.authored
        rw [originalOrigins] at mem
        have endpoint := packet.known.endpoint
        rw [List.mem_singleton.mp mem] at endpoint
        change listPoint410 90 1 = listPoint410 packet.known.key packet.known.payload at endpoint
        injection endpoint with _ span
        injection span with one _
        injection one with pt
        injection pt with o
        injection o with v
        injection v with n
        exact n.symm
      have payloadLoop : GeneralDeclarativePriority321.RootRecurs split source.child.demand := by
        have exactArgs : source.child.demand.arguments = [⟨1,1,1⟩] := by
          change [GeneralDeclarativeWitnessDeclaredState357.point source.payload] = _
          rw [payload]
          rfl
        apply GeneralDeclarativeWitnessCycle350.rooted (w := payloadCycleWire)
        unfold GeneralDeclarativeWitnessCycle350.check
        rw [exactArgs]
        decide +kernel
      exact payloadLoop
    have cls : ClassifiedAs new.state new.root expected :=
      older.symm ▸ selected_where_child_K2_has_exact_report411 (⟨source,safe⟩ : VerifiedWhereList new d) childCycle
    have fit := mixed_raw_boundary_has_real_fitting_model411 got
    have meaning : ReportEvidence new.state nestedModel new.root expected := by
      obtain ⟨e,trace,summary,out⟩ := cls
      exact ⟨e,trace,summary,out,mixed_R3_trace_model_meaning411 trace nestedModel fit⟩
    refine ⟨p,rfl,cls,fit,meaning,?_⟩
    intro w
    cases w with
    | previous prev => exact no_earlier_where_exception411 (⟨source,safe⟩ : VerifiedWhereList new d) expected prev
    | unsupported => rfl
    | whereChild cert => exact mixed_scope_rejects_every_official_where_wire411 got cert expected

#print axioms no_earlier_where_exception411
#print axioms mixed_scope_rejects_every_official_where_wire411
#print axioms actual_mixed_where_gap_is_nonvacuous411
end Yulang.GeneralDeclarativeI65.I72.WhereCycle411.CertificateBoundary.MixedCutProbe
