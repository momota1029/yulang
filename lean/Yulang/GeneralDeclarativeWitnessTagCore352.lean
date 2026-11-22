import Yulang.GeneralDeclarativeWitnessTagBranch352
import Yulang.GeneralDeclarativeWitnessClassify334

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTagCore352
open GeneralDeclarativeHead320 (State Models Equation environment)
open GeneralDeclarativeEntailment320 (Holds appendFacts)
open GeneralDeclarativeDemand320 (Demand HeadMeaning sourceValue bounds_sound)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeAssembly320 (Node Meaning)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open GeneralDeclarativeWitnessTagLocal351 (Route PatternData next spans context prepared)
open GeneralDeclarativeTaggedPatch340 (captured)
open GeneralDeclarativeTaggedWhole340 (clone copied clone_exact fullState)
open GeneralDeclarativeWitnessCompiler350 (Accepted)
open GeneralDeclarativeEndpointBody336 (Body calculate sound)
open GeneralDeclarativeStableReads329 (names_one)
open GeneralDeclarativeStableAssemble329 (tieState)
open GeneralDeclarativeStableTies329 (pairOf from_use)
open GeneralDeclarativeGrowth327 (facts trans restrict)
open GeneralDeclarativeCurrentReceipt330 (relays_models)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent Ty)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_symm eqv_trans variant_congr union_congr)
open GeneralNominalCenteredHeadMatCompilerSemantics (translate_value)
open GeneralDeclarations (Registry Declaration Checked)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarationPatterns (Constructors Pattern normalize)
open GeneralCandidateInspection (plainNames)
open GeneralNominalCenteredHeadMatExpressions (Expr translate value)
open CommonRoleOutermostResolver (All₂)

theorem assembled_payload (c : Constructors) (i : Interpretation) (p : Pattern)
    {ns : List Nat} {code : Expr} (used : plainNames p = some ns)
    (printedCode : translate c i p = some code) (v : Nat → Ty) (whole : Ty)
    (shared : ∀ n ∈ ns, Equivalent whole (v n)) :
    Equivalent whole (value (fun _ => v) .actual code) := by
  cases p with
  | var n =>
    cases Option.some.inj used
    cases Option.some.inj printedCode
    exact shared n List.mem_cons_self
  | join l r =>
    cases a : plainNames l with
    | none => simp [plainNames,a] at used
    | some xs =>
      cases b : plainNames r with
      | none => simp [plainNames,a,b] at used
      | some ys =>
        have n : xs ++ ys = ns := by simpa [plainNames,a,b] using used
        subst ns
        cases x : translate c i l with
        | none => simp [translate,x] at printedCode
        | some lg =>
          cases y : translate c i r with
          | none => simp [translate,x,y] at printedCode
          | some rg =>
            have eq : .join lg rg = code := by simpa [translate,x,y] using printedCode
            subst code
            exact eqv_trans (eqv_symm (GeneralDeclarativePlainCapture323.union_same whole))
              (union_congr (assembled_payload c i l a x v whole (fun _ h => shared _ (List.mem_append_left _ h)))
                (assembled_payload c i r b y v whole (fun _ h => shared _ (List.mem_append_right _ h))))
  | app | variant | record => cases used
termination_by sizeOf p

theorem actual_variable_environment (c : Constructors) (i : Interpretation) (pat : Pattern)
    {ns : List Nat} {code : Expr} (used : plainNames pat = some ns)
    (printedCode : translate c i pat = some code) (v : GeneralNominalMaterialization.Mode → Nat → Ty) :
    value v .actual code = value (fun _ => v .actual) .actual code := by
  cases pat with
  | var n => cases Option.some.inj printedCode; rfl
  | join l r =>
    cases a : plainNames l with
    | none => simp [plainNames,a] at used
    | some xs =>
      cases b : plainNames r with
      | none => simp [plainNames,a,b] at used
      | some ys =>
        cases x : translate c i l with
        | none => simp [translate,x] at printedCode
        | some lg =>
          cases y : translate c i r with
          | none => simp [translate,x,y] at printedCode
          | some rg =>
            have eq : .join lg rg = code := by simpa [translate,x,y] using printedCode
            subst code
            simp only [value,actual_variable_environment c i l a x v,
              actual_variable_environment c i r b y v]
  | app | variant | record => cases used
termination_by sizeOf pat

theorem literal_head {s : State} {t : Table} {a : Attached s t} {arg : Capture} {tag : Nat}
    {c : Constructors} {i : Interpretation} {pat : Pattern}
    (read : Route a arg tag) (pattern : PatternData c i pat tag) (keep : List Nat)
    (m : Assignment) (fit : Models (next read pattern keep) m) (cap : Nat → Capture)
    (links : ∀ x ∈ spans read pattern keep, Equivalent (m x.2.center).1 (m (cap x.1).center).1) :
    HeadMeaning c i cap m arg pat := by
  let slot := captured s arg tag read.low read.high keep
  have printed : translate c i (normalize pat) = some (.variant tag pattern.code) := by
    simp only [pattern.normal,translate,pattern.translated]
    rfl
  have visible : (⟨arg.center,.variant tag (clone (.variable slot.center) pattern.code)⟩ : Equation) ∈
      (next read pattern keep).equations := by
    exact List.mem_append_right _ List.mem_cons_self
  have root := fit.2 _ visible
  have rootAt : Equivalent (m arg.center).1 (CommonNominalFullCarrier.variant tag (m slot.center).1) :=
    eqv_trans root (variant_congr tag (clone_exact (.variable slot.center) pattern.code m))
  have payload := assembled_payload c i pattern.payload pattern.plain pattern.translated
    (variables cap m .actual) (m slot.center).1 (fun n used => links (n,slot) (List.mem_map_of_mem used))
  have actual := actual_variable_environment c i pattern.payload pattern.plain pattern.translated (variables cap m)
  rw [← actual] at payload
  obtain ⟨_,range,_⟩ := prepared read pattern keep
  refine ⟨?_,bounds_sound range.fits m fit⟩
  unfold sourceValue
  rw [← translate_value (variables := variables cap m) _ printed]
  exact eqv_trans rootAt (variant_congr tag payload)

/-- The tagged positive kernel yields the *old semantic conclusion* on
the same current model as C334, by its own checked source and real compiler
receipt. It does not assert a C334 classification for a C340 tagged read. -/
theorem literal_node {s : State} {t : Table} {a : Attached s t} {arg : Capture} {tag : Nat}
    {r : Registry} {i : Interpretation} {d : Demand} {impl : Declaration}
    (h : Route a arg tag) (x : PatternData r.constructors i pat tag)
    {keep fallback targets current wire}
    (compiled : Accepted (context d impl h x keep fallback targets) current wire)
    (well : Checked r) (covered : Coverage r i)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role) (declared : Declared r d)
    (args : d.arguments = [arg]) (head : impl.head = [pat])
    (m : Assignment) (fit : Models current m) :
    Node r i m d impl.id compiled.compiled.kids ∧
      (∀ child ∈ compiled.compiled.kids, Declared r child) := by
  obtain ⟨_,read,ranges⟩ := prepared h x keep
  have order : (spans h x keep).map Prod.fst = impl.inputNames := by
    rw [GeneralDeclarations.Declaration.inputNames,head]
    simpa only [GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.variablesArgs,
      List.append_nil] using names_one read
  obtain ⟨ordinary,kids,b,expected,_,names,_,_,growth⟩ :=
    calculate well covered visible role declared keep fallback targets order ranges
  have seen := GeneralDeclarativeWitnessCompiler350.actual compiled
  change GeneralDeclarativeNestedBody332.compileBody r i d impl (next h x keep)
    (spans h x keep) keep fallback targets = some (compiled.compiled.state,compiled.compiled.kids) at seen
  cases Option.some.inj (expected.symm.trans seen)
  have printed := relays_models (GeneralDeclarativeWitnessCompiler350.retained compiled) m fit
  have anchored := restrict (trans (facts (next h x keep) _) growth) m printed
  obtain ⟨meaning,children⟩ := sound b well covered visible role declared m printed
  have links : ∀ span ∈ spans h x keep, Equivalent (m span.2.center).1 (m (b.capture span.1).center).1 := by
    intro p requested
    have found : pairOf p ∈ b.spans.map pairOf := List.mem_map.mpr ⟨p,names.symm ▸ requested,rfl⟩
    have sound := from_use b.tied found m printed
    have written : p.1 ∈ impl.inputNames := by
      rw [← order]
      exact List.mem_map.mpr ⟨p,requested,rfl⟩
    unfold Body.capture GeneralDeclarativeFrameReadback325.sourceNames
    rw [GeneralDeclarativeProducedNames325.exact_input (well.2 impl visible) written]
    exact sound
  refine ⟨⟨impl,b.capture,rfl,⟨visible,role,meaning.captures,?_,meaning.children,meaning.outputs⟩⟩,children⟩
  rw [args,head]
  exact .cons (literal_head h x keep m anchored b.capture links) .nil

end Yulang.GeneralDeclarativeWitnessTagCore352
