import Yulang.GeneralDeclarativeI65I72VariableWhere403

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonDeclaredNominalInspection (Kind)
open GeneralDeclarationPatterns (Pattern)
open CommonNominalFullCarrier (Ty Row)
open GeneralNominalCenteredHeadMatExpressions (Expr value values)
open GeneralDeclarativeHead320 (environment)

/- These are only denotation representatives used for an exactly
   retained ordinary equation. The authoritative RHS is still the
   typed tree; no constructor mode, endpoint, occurrence or type
   annotation is changed. The Expr carrier cannot insert a row-valued
   nominal argument. That case gives no representative, not a failed
   Yulang source/classification rule. -/
mutual
def fixedValueCode403 {s slots c p} :
    NamedMixedTree401 s slots c p → Option Expr
  | .binder _ cap => some (.variable cap.val.center)
  | .record l a b => do
    pure (.record l (← fixedValueCode403 a) (← fixedValueCode403 b))
  | .variant l a => (fixedValueCode403 a).map (.variant l)
  | .join a b => do pure (.join (← fixedValueCode403 a) (← fixedValueCode403 b))
  | .declaredApp n _ _ _ args => (fixedValueArgsCode403 args).map (.nominal n)
  | .scalar _ base _ _ => some (.primitive (.scalar base) [])
  | .emptyRecord _ _ _ => some (.primitive .emptyRecord [])
  | .exactEmpty _ _ _ => some (.primitive .exactEmpty [])
  | .pair _ _ _ a b => do
    pure (.primitive .pair [← fixedValueCode403 a, ← fixedValueCode403 b])

def fixedValueArgCode403 {s slots c param p} :
    MixedArg401 s (NamedSlot401 slots) c param p → Option Expr
  | .valuePoint _ _ _ cap | .valueInterval _ _ _ cap => some (.variable cap.val.center)
  | .rowPoint .. | .rowInterval .. => none
  | .valueTree _ _ tree => fixedValueCode403 tree

def fixedValueArgsCode403 {s slots c params ps} :
    MixedArgs401 s (NamedSlot401 slots) c params ps → Option (List Expr)
  | .nil => some []
  | .cons a b => do pure ((← fixedValueArgCode403 a) :: (← fixedValueArgsCode403 b))
end

/-- The original mixed typed tree, even inside record/join and nested
declared nominal heads, agrees with the value-only equation syntax in
the same actual model when this syntactic representation exists. No
legacy ordinary pattern compiler or invariant fallback is called. -/
theorem fixed_value_code_same_model403 {s slots c p}
    (tree : NamedMixedTree401 s slots c p) (m : Model) :
    ∀ e, fixedValueCode403 tree = some e →
      evaluateMixedRhs401 (actualNamedMixedRead401 m) tree = some (value (environment m.assignment) .actual e) := by
  refine MixedRhs401.rec
    (motive_1 := fun _ _ tree => ∀ e, fixedValueCode403 tree = some e →
      evaluateMixedRhs401 (actualNamedMixedRead401 m) tree = some (value (environment m.assignment) .actual e))
    (motive_2 := fun _ _ _ arg => ∀ e, fixedValueArgCode403 arg = some e →
      evaluateMixedArg401 (actualNamedMixedRead401 m) arg =
        some (Sum.inl (value (environment m.assignment) .actual e)))
    (motive_3 := fun _ _ _ args => ∀ es, fixedValueArgsCode403 args = some es →
      evaluateMixedArgs401 (actualNamedMixedRead401 m) args =
        some ((values (environment m.assignment) .actual es).map Sum.inl))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ tree
  · intro c n cap e eq
    cases eq
    rfl
  · intro c a b lbl lhs rhs aIh bIh e eq
    cases ea : fixedValueCode403 lhs with
    | none => simp [fixedValueCode403,ea] at eq
    | some x =>
      cases eb : fixedValueCode403 rhs with
      | none => simp [fixedValueCode403,ea,eb] at eq
      | some y =>
        have equal : Expr.record lbl x y = e := by simpa [fixedValueCode403,ea,eb] using eq
        subst e
        simp [evaluateMixedRhs401,value,aIh x ea,bIh y eb]
  · intro c p lbl rhs ih e eq
    cases child : fixedValueCode403 rhs with
    | none => simp [fixedValueCode403,child] at eq
    | some x =>
      have equal : Expr.variant lbl x = e := by simpa [fixedValueCode403,child] using eq
      subst e
      simp [evaluateMixedRhs401,value,ih x child]
  · intro c a b lhs rhs aIh bIh e eq
    cases ea : fixedValueCode403 lhs with
    | none => simp [fixedValueCode403,ea] at eq
    | some x =>
      cases eb : fixedValueCode403 rhs with
      | none => simp [fixedValueCode403,ea,eb] at eq
      | some y =>
        have equal : Expr.join x y = e := by simpa [fixedValueCode403,ea,eb] using eq
        subst e
        simp [evaluateMixedRhs401,value,aIh x ea,bIh y eb]
  · intro ps c params n use tags table args ih e eq
    cases made : fixedValueArgsCode403 args with
    | none => simp [fixedValueCode403,made] at eq
    | some es =>
      have same : Expr.nominal n es = e := by simpa [fixedValueCode403,made] using eq
      subst e
      simp [evaluateMixedRhs401,value,ih es made]
  · intro c n base use actual e eq
    cases eq
    rfl
  · intro c n use actual e eq
    cases eq
    rfl
  · intro c n use actual e eq
    cases eq
    rfl
  · intro c a b n use actual lhs rhs aIh bIh e eq
    cases ea : fixedValueCode403 lhs with
    | none => simp [fixedValueCode403,ea] at eq
    | some x =>
      cases eb : fixedValueCode403 rhs with
      | none => simp [fixedValueCode403,ea,eb] at eq
      | some y =>
        have equal : Expr.primitive .pair [x,y] = e := by simpa [fixedValueCode403,ea,eb] using eq
        subst e
        simp [evaluateMixedRhs401,value,values,aIh x ea,bIh y eb]
  · intro c param n kind mode cap e eq
    cases eq
    rfl
  · intro c param n kind mode cap e eq
    cases eq
    rfl
  · intro c param n kind mode cap e eq
    cases eq
  · intro c param n kind mode cap e eq
    cases eq
  · intro params p c kind treeBit tree ih e eq
    simp only [fixedValueArgCode403] at eq
    simp [evaluateMixedArg401,ih e eq]
  · intro c es eq
    cases eq
    rfl
  · intro c a ps p pats first rest fIh rIh es eq
    cases ec : fixedValueArgCode403 first with
    | none => simp [fixedValueArgsCode403,ec] at eq
    | some x =>
      cases ed : fixedValueArgsCode403 rest with
      | none => simp [fixedValueArgsCode403,ec,ed] at eq
      | some xs =>
        have same : x::xs = es := by simpa [fixedValueArgsCode403,ec,ed] using eq
        subst es
        simp [evaluateMixedArgs401,values,fIh x ec,rIh xs ed]

/-- Original typed B6 event plus the exact retained row at the
original request's fixed target. This proposition is not proved from
the fact that the RHS can denote a value. -/
def RetainedTypedValueRows403 {s q} (e : Event s q) : Prop :=
  ∀ i : Fin q.demand.outputs.length, ∃ rhs,
    fixedValueCode403 (e.outputs i).rhs = some rhs ∧
      ⟨q.demand.outputs[i].target,rhs⟩ ∈ s.core.current.ordinary.equations

theorem retained_typed_rows_satisfy_fixed_targets403 {s q} {e : Event s q}
    (actual : RetainedTypedValueRows403 e) (m : Model) (fit : Fits s m) :
    FixedTargets m e := by
  intro i
  obtain ⟨rhs,lower,retained⟩ := actual i
  have same := fixed_value_code_same_model403 (e.outputs i).rhs m rhs lower
  refine ⟨value (environment m.assignment) .actual rhs,?_,fit.1.1.2 _ retained⟩
  simp only [NamedMixedReceipt401.actualEquation,NamedMixedOutput401.receipt,same,Option.map_some]

end Yulang.GeneralDeclarativeI65.I72
