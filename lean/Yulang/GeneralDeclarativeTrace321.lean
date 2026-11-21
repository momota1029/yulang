import Yulang.GeneralDeclarativeAliasMeaning321
import Yulang.GeneralDeclarativeCenterEntails321

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 9000
set_option maxHeartbeats 2500000
namespace Yulang.GeneralDeclarativeTrace321
open GeneralDeclarativeHead320 (State Equation Models environment byMode variables_eq)
open GeneralDeclarativeAliasMeaning321 (alias_sound)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeEntailment320 (Entails Holds)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralNominalCenteredHeadMatExpressions (Expr value values)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans record_congr variant_congr union_congr)
open GeneralNominalCenteredHeadMatCompilerSemantics (primitive_congr nominal_congr)
open GeneralNominalMaterialization (Mode)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalMatchedAssembly (Aligned)

structure Occurrence where
  binder : Nat
  mode : Mode
  argument : Nat

mutual
/-- A source constructor match records concrete logical-name occurrences
independently of the capture chosen for each source binder. -/
inductive Trace (s : State) : Mode → Nat → Expr → List Occurrence → Prop where
  | capture : Trace s mode name (.variable binder) [⟨binder,mode,name⟩]
  | primitive : Alias s name source →
    (⟨source,.primitive tag (args.map Expr.variable)⟩ : Equation) ∈ s.equations →
    TraceArgs s mode args targets seen → Trace s mode name (.primitive tag targets) seen
  | nominal : Alias s name source →
    (⟨source,.nominal tag (args.map Expr.variable)⟩ : Equation) ∈ s.equations →
    TraceArgs s .actual args targets seen → Trace s mode name (.nominal tag targets) seen
  | record : Alias s name source →
    (⟨source,.record label (.variable a) (.variable b)⟩ : Equation) ∈ s.equations →
    Trace s mode a one xs → Trace s mode b two ys →
    Trace s mode name (.record label one two) (xs ++ ys)
  | variant : Alias s name source →
    (⟨source,.variant label (.variable a)⟩ : Equation) ∈ s.equations →
    Trace s mode a exp seen → Trace s mode name (.variant label exp) seen
  | join : Alias s name source →
    (⟨source,.join (.variable a) (.variable b)⟩ : Equation) ∈ s.equations →
    Trace s mode a one xs → Trace s mode b two ys →
    Trace s mode name (.join one two) (xs ++ ys)

inductive TraceArgs (s : State) : Mode → List Nat → List Expr → List Occurrence → Prop where
  | nil : TraceArgs s mode [] [] []
  | cons : Trace s mode arg target first → TraceArgs s mode args targets tail →
    TraceArgs s mode (arg :: args) (target :: targets) (first ++ tail)
end

def Links (s : State) (capture : Nat → Capture) (seen : List Occurrence) : Prop :=
  ∀ o ∈ seen, Alias s o.argument (byMode (capture o.binder) o.mode)

theorem links_append {s capture one many} (links : Links s capture (one ++ many)) :
    Links s capture one ∧ Links s capture many :=
  ⟨fun o h => links o (List.mem_append_left _ h),fun o h => links o (List.mem_append_right _ h)⟩

theorem constants_mode (m : GeneralNominalCommonBridge.Assignment) (mode : Mode) (args : List Nat) :
    values (environment m) mode (args.map Expr.variable) =
      values (environment m) .actual (args.map Expr.variable) := by
  induction args with
  | nil => rfl
  | cons one rest ih =>
    simp only [List.map_cons,values,value,environment,ih]

theorem trace_model {s : State} (m) (valid : Models s m) (capture : Nat → Capture)
    (read : Trace s mode name expression seen) (links : Links s capture seen) :
    Equivalent (m name).1 (value (variables capture m) mode expression) := by
  exact Trace.rec
    (motive_1 := fun mode name code seen _ => Links s capture seen →
      Equivalent (m name).1 (value (variables capture m) mode code))
    (motive_2 := fun mode args code seen _ => Links s capture seen →
      Aligned Equivalent (values (environment m) mode (args.map Expr.variable))
        (values (variables capture m) mode code))
    (by
      intro mode name binder aliases
      simp only [value,variables_eq]
      exact alias_sound (aliases _ List.mem_cons_self) m valid)
    (by
      intro name source tag mode args targets seen equal found _ children aliases
      have one := alias_sound equal m valid
      have two := valid.2 _ found
      have aligned := children aliases
      rw [constants_mode] at aligned
      exact eqv_trans one (eqv_trans two (primitive_congr _ aligned)))
    (by
      intro name source tag args targets seen mode equal found _ children aliases
      have one := alias_sound equal m valid
      have two := valid.2 _ found
      exact eqv_trans one (eqv_trans two (nominal_congr _ (children aliases))))
    (by
      intro name source label a b mode one xs two ys equal found _ _ hx hy aliases
      exact eqv_trans (alias_sound equal m valid) (eqv_trans (valid.2 _ found)
        (record_congr _ (hx (links_append aliases).1) (hy (links_append aliases).2))))
    (by
      intro name source label a mode exp seen equal found _ child aliases
      exact eqv_trans (alias_sound equal m valid) (eqv_trans (valid.2 _ found)
        (variant_congr _ (child aliases))))
    (by
      intro name source a b mode one xs two ys equal found _ _ hx hy aliases
      exact eqv_trans (alias_sound equal m valid) (eqv_trans (valid.2 _ found)
        (union_congr (hx (links_append aliases).1) (hy (links_append aliases).2))))
    (by intro _ _; exact .nil)
    (by
      intro mode arg target first args targets tail _ _ ih jh aliases
      exact .cons (ih (links_append aliases).1) (jh (links_append aliases).2))
    read links

theorem trace_equation {s : State} (read : Trace s mode name expression seen)
    (links : Links s capture seen) :
    Entails s ⟨name,logical capture mode expression⟩ := by
  intro m valid
  simp only [Holds,logical_value]
  exact trace_model m valid capture read links

end Yulang.GeneralDeclarativeTrace321
