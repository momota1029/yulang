import Yulang.GeneralDeclarativeArityNominal330
import Yulang.GeneralDeclarativeOpaquePlan328

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeArityPlan330
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeTrace321 (Trace TraceArgs)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeGrowth327 (Extends derives)
open GeneralDeclarativeOpaqueIntervals328 (Ends low high)
open GeneralDeclarativePairCenters326 (pair)
open GeneralDeclarativePairProbe326 (components)
open GeneralDeclarativeOpaqueTrace328 (ordinary_over_support)
open GeneralDeclarativeOpaqueVariantNames328 (variant_trace)
open GeneralNominalCenteredHeadMatExpressions (Expr)

mutual
inductive Shape : Expr → Prop where
  | capture : Shape (.variable key)
  | pair : Shape a → Shape b → Shape (pair a b)
  | tagged : Shape a → Shape (.variant tag a)
  | nominal : Shapes args → Shape (.nominal tag args)
inductive Shapes : List Expr → Prop where
  | nil : Shapes []
  | cons : Shape a → Shapes rest → Shapes (a :: rest)
end

mutual
inductive Plan where
  | capture (key : Nat)
  | pair (bounds : Ends) (a b : Plan)
  | tagged (tag low high : Nat) (payload : Plan)
  | nominal (tag : Nat) (high : List Nat) (fields : Plans)
inductive Plans where
  | nil
  | cons (name : Nat) (entry : Plan) (rest : Plans)
end

mutual
def Plan.code : Plan → Expr
  | .capture n => .variable n
  | .pair _ a b => pair a.code b.code
  | .tagged tag _ _ one => .variant tag one.code
  | .nominal tag _ entries => .nominal tag entries.codes
def Plans.codes : Plans → List Expr
  | .nil => []
  | .cons _ a rest => a.code :: rest.codes
end

def Plans.names : Plans → List Nat
  | .nil => []
  | .cons n _ rest => n :: rest.names

mutual
inductive Reads (s : State) : Nat → Nat → Plan → Prop where
  | capture : Reads s lo hi (.capture key)
  | pair : Derives s (.variable lo) (low ends) → Derives s (.variable hi) (high ends) →
    Reads s ends.firstLo ends.firstHi a → Reads s ends.secondLo ends.secondHi b →
    Reads s lo hi (.pair ends a b)
  | tagged : Derives s (.variable lo) (.variant tag (.variable a)) →
    Derives s (.variable hi) (.variant tag (.variable b)) →
    Reads s a b body → Reads s lo hi (.tagged tag a b body)
  | nominal : Derives s (.variable lo) (GeneralDeclarativeArityNominal330.code tag fields.names) →
    Derives s (.variable hi) (GeneralDeclarativeArityNominal330.code tag upper) →
    ReadsFields s fields → Reads s lo hi (.nominal tag upper fields)
inductive ReadsFields (s : State) : Plans → Prop where
  | nil : ReadsFields s .nil
  | cons : Reads s n n a → ReadsFields s rest → ReadsFields s (.cons n a rest)
end

theorem grow {s t : State} (h : Extends s t) (r : Reads s a b p) : Reads t a b p :=
  Reads.rec
    (motive_1 := fun a b plan _ => Reads t a b plan)
    (motive_2 := fun plan _ => ReadsFields t plan)
    .capture
    (fun lo hi _ _ first last => .pair (derives h lo) (derives h hi) first last)
    (fun lo hi _ both => .tagged (derives h lo) (derives h hi) both)
    (fun lo hi _ fields => .nominal (derives h lo) (derives h hi) fields)
    .nil
    (fun _ _ one tail => .cons one tail) r

theorem growFields {s t : State} (h : Extends s t) (r : ReadsFields s p) : ReadsFields t p :=
  ReadsFields.rec
    (motive_1 := fun a b plan _ => Reads t a b plan)
    (motive_2 := fun plan _ => ReadsFields t plan)
    .capture
    (fun lo hi _ _ first last => .pair (derives h lo) (derives h hi) first last)
    (fun lo hi _ both => .tagged (derives h lo) (derives h hi) both)
    (fun lo hi _ fields => .nominal (derives h lo) (derives h hi) fields)
    .nil
    (fun _ _ one tail => .cons one tail) r

/-- Every opaque invariant branch uses the ordered actual parameter
reads from the lower trace. The upper trace supplies the comparison
row, but its names are not substituted for the actual occurrences. -/
theorem extract {s : State} {p : Supported s done} (patternShape : Shape code)
    (lo : Trace (restriction p) mode loName code loUsed)
    (hi : Trace (restriction p) other hiName code hiUsed) :
    ∃ plan, plan.code = code ∧ Reads s loName hiName plan := by
  induction patternShape using Shape.rec
    (motive_2 := fun codes _ => ∀ {args used}, TraceArgs (restriction p) .actual args codes used →
      ∃ binds : Plans, binds.codes = codes ∧ binds.names = args ∧ ReadsFields s binds)
    generalizing mode other loName hiName loUsed hiUsed with
  | capture => exact ⟨.capture _,rfl,.capture⟩
  | pair l r ih jh =>
    obtain ⟨ll,lr,_,_,loRow,loL,loR,_⟩ := components lo
    obtain ⟨hl,hr,_,_,hiRow,hiL,hiR,_⟩ := components hi
    obtain ⟨x,printX,readX⟩ := ih loL hiL
    obtain ⟨y,printY,readY⟩ := jh loR hiR
    let ends : Ends := ⟨ll,hl,lr,hr⟩
    exact ⟨.pair ends x y,by simp [Plan.code,printX,printY],
      .pair (GeneralDeclarativeOrdinaryIncrease325.derives (ordinary_over_support p) loRow)
        (GeneralDeclarativeOrdinaryIncrease325.derives (ordinary_over_support p) hiRow) readX readY⟩
  | tagged a ih =>
    obtain ⟨l,lRow,first⟩ := variant_trace lo
    obtain ⟨h,hRow,last⟩ := variant_trace hi
    obtain ⟨work,printed,seen⟩ := ih first last
    exact ⟨.tagged _ l h work,by simp [Plan.code,printed],.tagged lRow hRow seen⟩
  | nominal args ih =>
    obtain ⟨l,lowRow,fields⟩ := GeneralDeclarativeArityNominal330.traced lo
    obtain ⟨h,highRow,_⟩ := GeneralDeclarativeArityNominal330.traced hi
    obtain ⟨entries,syntaxEq,namesEq,reads⟩ := ih fields
    exact ⟨.nominal _ h entries,by simp [Plan.code,syntaxEq],.nominal (namesEq ▸ lowRow) highRow reads⟩
  | nil =>
    rename_i names used seen
    cases seen
    exact ⟨.nil,rfl,rfl,.nil⟩
  | cons a more ih jh =>
    rename_i names used source
    cases source with
    | cons head tail =>
      obtain ⟨x,codeX,readX⟩ := ih head head
      obtain ⟨y,codeY,namesY,readY⟩ := jh tail
      exact ⟨.cons _ x y,by simp [Plans.codes,codeX,codeY],by simp [Plans.names,namesY],.cons readX readY⟩

end Yulang.GeneralDeclarativeArityPlan330
