import Yulang.GeneralDeclarativeWitnessCutDecl334

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDeclarativeWitnessCutBody334
open GeneralDeclarativeWitnessCutDecl334
open GeneralDeclarativeNestedExample332 (interpretation)
open GeneralDeclarationExamples (constructors)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeOrigins321 (Supported Origin restriction from_source backed_iff)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeNestedBody332 (compileBody compiler_exact)
open GeneralDeclarativeStableAssemble329 (merged MergeFacts)
open GeneralDeclarativeStableCompiler329 (Frame)
open GeneralDeclarativeStableReads329 (Heads)
open GeneralDeclarativeEntailment320 (appendFacts model_append)
open GeneralDeclarativeOpaqueNominal328 (point point_bounded)
open GeneralDeclarativeExampleSource320 (int)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonNominalFullCarrier (record exactEmpty)
open GeneralDeclarations (Clause)

abbrev raw : Expr := .record 7 (.variable 3) (.variable 4)
abbrev lo : Equation := ⟨0,raw⟩
abbrev opaqueCenter : Equation := ⟨1,raw⟩
abbrev hi : Equation := ⟨2,raw⟩
abbrev scalar : Equation := ⟨3,.primitive (.scalar .int) []⟩
abbrev tailRow : Equation := ⟨4,.primitive .exactEmpty []⟩
abbrev knownRows : List Equation := [lo,hi,scalar,tailRow]
abbrev initial : State := ⟨⟨[],[(0,1),(1,2)]⟩,knownRows ++ [opaqueCenter]⟩
abbrev keep := [5]
abbrev spans : List (Nat × Capture) := [(0,point 3),(1,point 4)]
def fallback (_ : Nat) := point 3
def targets (_ : Clause) (_ : Nat) := 5
abbrev assembled := (merged initial keep spans fallback).state
abbrev lastWrite : Equation := ⟨5,.variable 3⟩
abbrev final := appendFacts assembled [lastWrite]

theorem bounds : Bounds initial arg :=
  ⟨.interval List.mem_cons_self,.interval (List.mem_cons_of_mem _ List.mem_cons_self)⟩

theorem ordinary_walk : Heads initial constructors interpretation root.arguments impl.head spans := by
  exact .cons (first := spans) (rest := []) ⟨bounds,wanted,raw,normal,
    .row (List.mem_append_right _ List.mem_cons_self),.record (.capture) (.capture)⟩ .nil

theorem literal_write :
    compileBody registry interpretation root impl initial spans keep fallback targets =
      some (final,[]) := rfl

theorem built : Nonempty (Frame final registry interpretation root impl []) := by
  obtain ⟨out,kids,frame,ran,_,_,_,_,_,_⟩ :=
    compiler_exact checked covered List.mem_cons_self rfl declared keep fallback targets ordinary_walk
      (fun a used => by
        rcases List.mem_cons.mp used with rfl|rest
        · exact point_bounded _ _
        · cases List.mem_singleton.mp rest
          exact point_bounded _ _)
  cases Option.some.inj (ran.symm.trans literal_write)
  exact ⟨frame⟩

theorem final_rows : final.equations = knownRows ++ [opaqueCenter,lastWrite] := rfl

def support : Supported final (fun _ => False) where
  derivesFrom := fun e o => (e ∈ knownRows ∧ o = .source) ∨ (e = opaqueCenter ∧ o = .output 100)
  ordinary := by
    rintro e o (one|other)
    · rw [final_rows]
      exact List.mem_append_left _ one.1
    · cases other.1
      rw [final_rows]
      exact List.mem_append_right _ List.mem_cons_self

theorem exact_supported {eq : Equation} :
    eq ∈ (restriction support).equations ↔ eq ∈ knownRows := by
  rw [backed_iff]
  constructor
  · rintro ⟨origin,why,now⟩
    rcases why with original|delayed
    · exact original.1
    · rw [delayed.2] at now
      cases now with
      | completed no => exact no.elim
  · intro used
    exact ⟨.source,.inl ⟨used,rfl⟩,.source⟩

theorem only_pending_center : support.derivesFrom opaqueCenter (.output 100) :=
  .inr ⟨rfl,rfl⟩

def model : Assignment := fun n =>
  (if n < 3 then record 7 int exactEmpty else if n = 4 then exactEmpty else int,Common.rowEmpty)

theorem initial_model : Models initial model := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro a e
    change a ∈ [(0,1),(1,2)] at e
    rcases List.mem_cons.mp e with rfl|rest
    · exact CommonNominalFullCarrier.subtype_refl _
    · cases List.mem_singleton.mp rest
      exact CommonNominalFullCarrier.subtype_refl _
  · intro e used
    change e ∈ [lo,hi,scalar,tailRow,opaqueCenter] at used
    simp only [List.mem_cons,List.not_mem_nil,or_false] at used
    rcases used with a|b|c|d|f <;> cases ‹_› <;> exact eqv_refl _

theorem folded : MergeFacts initial keep spans fallback := by
  apply GeneralDeclarativeStableAssemble329.assemble
  intro a used
  rcases List.mem_cons.mp used with rfl|rest
  · exact point_bounded _ _
  · cases List.mem_singleton.mp rest
    exact point_bounded _ _

theorem has_model : ∃ m, Models final m := by
  obtain ⟨m,fit,unchanged⟩ := folded.preserve.lifts model initial_model
  refine ⟨m,(model_append _).mpr ⟨fit,?_⟩⟩
  intro row emitted
  cases List.mem_singleton.mp emitted
  change CommonNominalFullCarrier.Equivalent (m 5).1 (m 3).1
  rw [unchanged 5 (by decide +kernel),unchanged 3 (by decide +kernel)]
  exact eqv_refl _

end Yulang.GeneralDeclarativeWitnessCutBody334
