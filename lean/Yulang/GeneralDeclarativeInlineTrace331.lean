import Yulang.GeneralDeclarativeInlineSpine331
import Yulang.GeneralDeclarativeRecordMaterial330
import Yulang.GeneralDeclarativeTermOccurrences322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInlineTrace331
open GeneralDeclarativeHead320 (State Equation Models environment)
open GeneralDeclarativeOrigins321 (Supported restriction restrict_models)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeAliasMeaning321 (alias_sound)
open GeneralDeclarativeTermWalk322 (Occurrence Walk WalkMany)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeInlineSpine331 (Closed split)
open GeneralDeclarativeRecordMaterial330 (tailExpr)
open GeneralDeclarativeOrderedRecord326 (order)
open GeneralNominalCenteredHeadMatExpressions (Expr value values)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans record_congr variant_congr union_congr)
open GeneralNominalCenteredHeadMatCompilerSemantics (primitive_congr nominal_congr)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalMaterialization (Mode)
open GeneralNominalMatchedAssembly (Aligned)
open CommonNominalFullCarrier (Equivalent)
open CommonRoleCanonicalRows (Row normalize)

/-- All visible record keys are consumed at once. A variable tail
captures exactly the canonical remainder; closed patterns test the
remainder rather than treating an unknown one as empty. -/
inductive TailCode : Expr → Prop where
  | binder : TailCode (.variable n)
  | width : TailCode (.primitive .emptyRecord [])
  | exactEnd : TailCode (.primitive .exactEmpty [])

mutual
/-- Positive, finite *source* observation. A raw name can expose only
an authorized row. Inline children keep their exact term and mode;
binders never cause a lookup or consult a candidate's shared centre.
No ordinary reconstruction equation is promoted to an origin. -/
inductive Read (s : State) : Mode → Expr → Expr → List Occurrence → Prop where
  | capture : Read s mode raw (.variable binder) [⟨binder,mode,raw⟩]
  | expose : (∀ n, code ≠ .variable n) → Alias s n owner →
      (⟨owner,raw⟩ : Equation) ∈ s.equations → Read s mode raw code uses →
      Read s mode (.variable n) code uses
  | primitive : Args s mode raw codes uses →
      Read s mode (.primitive tag raw) (.primitive tag codes) uses
  | nominal : Args s .actual raw codes uses →
      Read s mode (.nominal tag raw) (.nominal tag codes) uses
  | variant : Read s mode raw code uses →
      Read s mode (.variant tag raw) (.variant tag code) uses
  | join : Read s mode left one first → Read s mode right two last →
      Read s mode (.join left right) (.join one two) (first++last)
  | record : Closed s input raw terminal → keys.Nodup → keys ≠ [] →
      order (normalize raw) keys = some selected → Fields s mode selected written first →
      TailCode tailCode → Read s mode (tailExpr raw keys terminal) tailCode last →
      Read s mode input (withTail written tailCode) (first++last)
inductive Args (s : State) : Mode → List Expr → List Expr → List Occurrence → Prop where
  | nil : Args s mode [] [] []
  | cons : Read s mode raw code here → Args s mode rest codes later →
      Args s mode (raw::rest) (code::codes) (here++later)
inductive Fields (s : State) : Mode → Row Expr → Row Expr → List Occurrence → Prop where
  | nil : Fields s mode [] [] []
  | cons : Read s mode raw code here → Fields s mode rest codes later →
      Fields s mode ((key,raw)::rest) ((key,code)::codes) (here++later)
end

def Prefix (m : Assignment) (src dst : Row Expr) : Prop :=
  ∀ a b, eqAt m a b → eqAt m (withTail src a) (withTail dst b)

def FieldWalk (mode : Mode) (src dst : Row Expr) (used : List Occurrence) : Prop :=
  ∀ a b last, Walk mode a b last → Walk mode (withTail src a) (withTail dst b) (used++last)

/-- The walk is supplied by the source proof before any satisfying
model is considered, and works in every model of the same state. -/
theorem realize {s : State} {p : Supported s done} (known : Read (restriction p) mode raw code seen)
    : ∃ rebuilt, (∀ m, Models s m → eqAt m raw rebuilt) ∧ Walk mode rebuilt code seen := by
  refine Read.rec
    (motive_1 := fun mode raw code seen _ =>
      ∃ rebuilt, (∀ m, Models s m → eqAt m raw rebuilt) ∧ Walk mode rebuilt code seen)
    (motive_2 := fun mode raw codes seen _ => ∃ rebuilt,
      (∀ m, Models s m → Aligned Equivalent (values (environment m) .actual raw) (values (environment m) .actual rebuilt)) ∧
      WalkMany mode rebuilt codes seen)
    (motive_3 := fun mode raw codes seen _ =>
      ∃ rebuilt, (∀ m, Models s m → Prefix m raw rebuilt) ∧ FieldWalk mode rebuilt codes seen)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ known
  · intro mode raw binder
    exact ⟨raw,fun _ _ => eqv_refl _,.capture⟩
  · intro code n owner raw uses mode _ link stored _ ih
    obtain ⟨rebuilt,h,w⟩ := ih
    exact ⟨rebuilt,fun m fit =>
      let view := restrict_models p m fit
      eqv_trans (alias_sound link m view) (eqv_trans (view.2 _ stored) (h m fit)),w⟩
  · intro mode raw codes uses tag _ ih
    obtain ⟨rebuilt,h,w⟩ := ih
    exact ⟨.primitive tag rebuilt,fun m fit => primitive_congr _ (h m fit),.primitive w⟩
  · intro raw codes uses mode tag _ ih
    obtain ⟨rebuilt,h,w⟩ := ih
    exact ⟨.nominal tag rebuilt,fun m fit => nominal_congr _ (h m fit),.nominal w⟩
  · intro mode raw code uses tag _ ih
    obtain ⟨rebuilt,h,w⟩ := ih
    exact ⟨.variant tag rebuilt,fun m fit => variant_congr _ (h m fit),.variant w⟩
  · intro mode left one first right two last _ _ hx hy
    obtain ⟨a,x,readX⟩ := hx
    obtain ⟨b,y,readY⟩ := hy
    exact ⟨.join a b,fun m f => union_congr (x m f) (y m f),.join readX readY⟩
  · intro input raw terminal keys selected mode written first tailCode last observation unique _ sorted _ _ _ ih jh
    obtain ⟨head,headEq,headWalk⟩ := ih
    obtain ⟨tail,tailEq,tailWalk⟩ := jh
    exact ⟨withTail head tail,fun m fit => eqv_trans (split observation unique sorted m fit) (headEq m fit _ _ (tailEq m fit)),
      headWalk _ _ _ tailWalk⟩
  · intro mode
    exact ⟨[],fun _ _ => .nil,.nil⟩
  · intro mode raw code here rest codes later _ _ hx hy
    obtain ⟨x,xEq,xw⟩ := hx
    obtain ⟨xs,xsEq,xsw⟩ := hy
    exact ⟨x::xs,fun m fit => .cons (xEq m fit) (xsEq m fit),.cons xw xsw⟩
  · intro mode
    exact ⟨[],(fun _ _ _ _ h => h),fun _ _ _ w => w⟩
  · intro mode raw code here rest codes later key _ _ hx hy
    obtain ⟨x,xEq,xw⟩ := hx
    obtain ⟨xs,xsEq,xsw⟩ := hy
    exact ⟨(key,x)::xs,(fun m fit a b h => record_congr key (xEq m fit) (xsEq m fit a b h)),fun a b last w => by
      simpa only [withTail,List.append_assoc] using Walk.record xw (xsw a b last w)⟩

end Yulang.GeneralDeclarativeInlineTrace331
