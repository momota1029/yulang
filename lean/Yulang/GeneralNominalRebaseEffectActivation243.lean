import Yulang.GeneralNominalRebaseEffectView243
import Yulang.GeneralNominalRebaseOriginActivation243
set_option backward.isDefEq.respectTransparency false
/-! Finite effect-expression support and checked activation preserving all
supplied output equations, live values and retained origin observations. -/
namespace Yulang.GeneralNominalRebaseEffectActivation243
open GeneralNominalRebaseEffectView243 (Expr Equation eval evals)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalFiniteEquationRealization236
open GeneralNominalRebaseEscapedProjection242
open GeneralNominalRebaseRawView243 (View)
open GeneralNominalRebaseLiveView243 (Site)
open GeneralNominalRebaseOriginView243 (Origin Observes)
open GeneralNominalRebaseViewActivation243 (Consumers ValuesAgree)

mutual
 def sources : Expr → List Nat
 | .source term => GeneralNominalState.typeSources term
 | .primitive _ arguments | .nominal _ arguments => sourcesMany arguments
 | .record _ payload tail | .join payload tail => sources payload ++ sources tail
 | .variant _ payload => sources payload
 def sourcesMany : List Expr → List Nat
 | [] => []
 | first :: rest => sources first ++ sourcesMany rest
end

mutual
 theorem eval_same (expression : Expr) {first last : Assignment}
 (same : Agree (sources expression) first last) : eval first expression = eval last expression := by
 cases expression with
 | source term => exact GeneralNominalCenteredModelExtension.type_eval_same term same
 | primitive constructor arguments =>
   simp only [eval,evals_same arguments same]
 | nominal name arguments =>
   simp only [eval,evals_same arguments same]
 | record label payload tail =>
   simp only [eval,eval_same payload (fun name member => same name (List.mem_append_left _ member)),
     eval_same tail (fun name member => same name (List.mem_append_right _ member))]
 | variant tag payload => simp only [eval,eval_same payload same]
 | join payload tail =>
   simp only [eval,eval_same payload (fun name member => same name (List.mem_append_left _ member)),
     eval_same tail (fun name member => same name (List.mem_append_right _ member))]
 theorem evals_same (expressions : List Expr) {first last : Assignment}
 (same : Agree (sourcesMany expressions) first last) : evals first expressions = evals last expressions := by
 cases expressions with
 | nil => rfl
 | cons expression rest =>
   simp only [evals,eval_same expression (fun name member => same name (List.mem_append_left _ member)),
     evals_same rest (fun name member => same name (List.mem_append_right _ member))]
end

def equationSources (equation : Equation) : List Nat :=
 GeneralNominalState.typeSources equation.target ++ sources equation.expression

theorem equation_iff (equation : Equation) {first last : Assignment}
 (same : Agree (equationSources equation) first last) :
 equation.Holds first ↔ equation.Holds last := by
 have target := GeneralNominalCenteredModelExtension.type_eval_same equation.target
   (fun name member => same name (List.mem_append_left _ member))
 have expression := eval_same equation.expression (fun name member => same name (List.mem_append_right _ member))
 unfold Equation.Holds
 rw [target,expression]

def reads (view : View) (atoms : List (PresenceNormalForm.Atom Nat)) (sites : List Site)
 (origins : List Origin) (equations : List Equation) : List Nat :=
 GeneralNominalRebaseOriginActivation243.reads view atoms sites origins ++ equations.flatMap equationSources

def Checked (entries : List Entry) (view : View) (atoms : List (PresenceNormalForm.Atom Nat))
 (sites : List Site) (origins : List Origin) (equations : List Equation) : Prop :=
 ∀ entry ∈ entries, entry.1 ∉ reads view atoms sites origins equations

def check (entries : List Entry) (view : View) (atoms : List (PresenceNormalForm.Atom Nat))
 (sites : List Site) (origins : List Origin) (equations : List Equation) : Bool :=
 entries.all (fun entry => !(reads view atoms sites origins equations).contains entry.1)

theorem check_iff (entries : List Entry) (view : View) (atoms : List (PresenceNormalForm.Atom Nat))
 (sites : List Site) (origins : List Origin) (equations : List Equation) :
 check entries view atoms sites origins equations = true ↔ Checked entries view atoms sites origins equations := by
 simp [check,Checked]

theorem equations_preserved (entries : List Entry) (view : View) (atoms : List (PresenceNormalForm.Atom Nat))
 (sites : List Site) (origins : List Origin) (equations : List Equation)
 (checked : Checked entries view atoms sites origins equations) {first last : Assignment}
 (kept : Preserves entries first last) :
 ∀ equation ∈ equations, equation.Holds first ↔ equation.Holds last := by
 intro equation member
 apply equation_iff
 intro name present
 apply kept.1 name
 intro entry included equal
 apply checked entry included
 rw [equal]
 exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨equation,member,present⟩)

theorem activate (entries : List Entry) (coherent : Coherent entries) (external : External entries)
 (view : View) (atoms : List (PresenceNormalForm.Atom Nat)) (sites : List Site)
 (origins : List Origin) (equations : List Equation)
 (checked : Checked entries view atoms sites origins equations) (model : Assignment)
 (valid : Consumers view atoms sites model) (outputs : ∀ equation ∈ equations, equation.Holds model) :
 Preserves entries (patch entries model) model ∧ Definitions entries (patch entries model) ∧
 Consumers view atoms sites (patch entries model) ∧ ValuesAgree sites (patch entries model) model ∧
 (∀ origin ∈ origins, ∀ value, Observes (patch entries model) origin value ↔ Observes model origin value) ∧
 (∀ equation ∈ equations, equation.Holds (patch entries model)) := by
 have localCheck : GeneralNominalRebaseOriginActivation243.Checked entries view atoms sites origins :=
   fun entry member present => checked entry member (List.mem_append_left _ present)
 obtain ⟨kept,definitions,consumers,values,observed⟩ :=
   GeneralNominalRebaseOriginActivation243.activate entries coherent external view atoms sites origins localCheck model valid
 exact ⟨kept,definitions,consumers,values,observed,fun equation member =>
   (equations_preserved entries view atoms sites origins equations checked kept equation member).mpr
     (outputs equation member)⟩
end Yulang.GeneralNominalRebaseEffectActivation243
