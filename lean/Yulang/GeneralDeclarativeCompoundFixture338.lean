import Yulang.GeneralDeclarativeCompoundDictionary338
import Yulang.GeneralDeclarativeCompoundHeads338
import Yulang.GeneralDeclarativeRecordReplay330

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 23000
set_option maxHeartbeats 1500000
namespace Yulang.GeneralDeclarativeCompoundFixture338
open GeneralDeclarations (Registry Declaration Clause Checked DeclarationChecked)
open GeneralDeclarationExamples (roles)
open GeneralDeclarationPatterns (Pattern normalize normalizeArgs variablesArgs hide
  ArgsWellScoped WellScoped checkSmaller_exact ConservativeSmaller counted substArgs encodeArgs)
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation)
open GeneralDeclarativeRecordDecl326 (body)
open GeneralDeclarativePairDecl326 (clause produced)
open GeneralDeclarativeExampleSource320 (leaf int)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeLowerKnown321 (alias_refl)
open GeneralDeclarativeInlineSpine331 (Closed)
open GeneralDeclarativeCompoundTree338 (World fitsModel)
open GeneralDeclarativeCompoundSources338 (Source Anchors)
open GeneralDeclarativeCompoundInputs338 (Inputs input_exact)
open GeneralDeclarativeCompoundCompiler338 (body_ready)
open GeneralDeclarativeEndpointBody336 (Body)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeInlineEndpoint331 (Heads)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (record exactEmpty emptyRecord subtype_refl common_record_mono exactEmpty_below_width)

abbrev arg : Capture := ⟨0,1,2⟩
abbrev lowerEnd : Expr := .primitive .exactEmpty []
abbrev upperEnd : Expr := .primitive .emptyRecord []
abbrev lowPayload : Expr := .record 9 (.variable 3) lowerEnd
abbrev upPayload : Expr := .record 9 (.variable 3) upperEnd
abbrev low : Expr := .record 7 lowPayload lowerEnd
abbrev high : Expr := .record 7 upPayload upperEnd
abbrev eql : Equation := ⟨0,low⟩
abbrev eqh : Equation := ⟨2,high⟩
abbrev eqi : Equation := ⟨3,.primitive (.scalar .int) []⟩
abbrev initial : State := ⟨⟨[],[(0,1),(1,2)]⟩,[eql,eqh,eqi]⟩
def support : Supported initial (fun _ => False) :=
  ⟨fun e o => e ∈ initial.equations ∧ o = .source,And.left⟩
abbrev w0 : World (fun _ => False) := ⟨initial,support,[]⟩
abbrev keep : List Nat := [5,6]
abbrev inner : Pattern := .record 9 (.var 0) (.var 4)
abbrev pat : Pattern := .record 7 inner (.var 1)
abbrev decl : Declaration := ⟨97,1,[pat],[clause],[body],[produced]⟩
abbrev registry : Registry := ⟨catalogue,roles,[decl,leaf]⟩
abbrev root : Demand := ⟨1,[arg],[⟨0,6⟩]⟩
theorem loKnown : eql ∈ (restriction support).equations := from_source _ ⟨List.mem_cons_self,rfl⟩
theorem hiKnown : eqh ∈ (restriction support).equations := from_source _ ⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩
theorem scalarKnown : eqi ∈ (restriction support).equations :=
  from_source _ ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),rfl⟩
theorem bounds : Bounds initial arg :=
  ⟨.interval List.mem_cons_self,.interval (List.mem_cons_of_mem _ List.mem_cons_self)⟩
theorem anchors : Anchors (restriction support) arg low high :=
  ⟨⟨0,alias_refl _,loKnown⟩,⟨2,alias_refl _,hiKnown⟩⟩
theorem lowClose (s : State) : Closed s low [(7,lowPayload)] lowerEnd := .field (.terminal .exactEnd)
theorem highClose (s : State) : Closed s high [(7,upPayload)] upperEnd := .field (.terminal .width)
theorem payloadLo (s : State) : Closed s lowPayload [(9,.variable 3)] lowerEnd := .field (.terminal .exactEnd)
theorem payloadHi (s : State) : Closed s upPayload [(9,.variable 3)] upperEnd := .field (.terminal .width)

theorem inner_source (s : State) : Source s lowPayload upPayload inner := by
  refine .record (fs := [(9,.var 0)]) (tail := .var 4) rfl (by decide) (by decide)
    (payloadLo s) (payloadHi s) ?_ ?_ ?_ .binder
  · intro k seen; cases List.mem_singleton.mp seen; exact ⟨_,List.mem_cons_self⟩
  · intro k seen; cases List.mem_singleton.mp seen; exact ⟨_,List.mem_cons_self⟩
  · intro f seen; cases List.mem_singleton.mp seen; intros; exact .binder

theorem actual_source (s : State) : Source s low high pat := by
  refine .record (fs := [(7,inner)]) (tail := .var 1) rfl (by decide) (by decide)
    (lowClose s) (highClose s) ?_ ?_ ?_ .binder
  · intro k seen; cases List.mem_singleton.mp seen; exact ⟨_,List.mem_cons_self⟩
  · intro k seen; cases List.mem_singleton.mp seen; exact ⟨_,List.mem_cons_self⟩
  · intro f seen l u hadL hadU
    cases List.mem_singleton.mp seen
    cases List.mem_singleton.mp hadL
    cases List.mem_singleton.mp hadU
    exact inner_source s

theorem checked_decl : DeclarationChecked catalogue roles decl := by
  have previous := GeneralDeclarativeRecordDecl326.checked_decl
  constructor
  · exact previous.signature
  · exact previous.identified
  · exact previous.produced
  · simp [Declaration.OutputOnly,Declaration.outputNames,Pattern.variables,variablesArgs]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,
      Pattern.variables,variablesArgs,normalize,hide]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped]
  · intro req h; cases List.mem_singleton.mp h; exact ⟨rfl,rfl⟩
  · intro req h; cases List.mem_singleton.mp h; exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro req h; cases List.mem_singleton.mp h; unfold ConservativeSmaller; decide +kernel
  · intro req h cap
    cases List.mem_singleton.mp h
    constructor
    · simp [substArgs,Pattern.subst,normalize,normalizeArgs,counted,encodeArgs,Pattern.encode,
        Roles.argsSize,Roles.Term.size]
      omega
    · intro n
      simp [substArgs,Pattern.subst,normalize,normalizeArgs,counted,encodeArgs,Pattern.encode,
        Roles.argsOccurrences,Roles.Term.occurrences]
      omega

theorem checked : Checked registry := by
  constructor
  · decide +kernel
  · intro d appears
    rcases List.mem_cons.mp appears with rfl|tail
    · exact checked_decl
    · cases List.mem_singleton.mp tail
      exact GeneralDeclarativeRecordDecl326.checked.2 _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem covered : Coverage registry interpretation := by
  refine ⟨?_,GeneralDeclarativeRecordReplay330.covered.2⟩
  intro d appears
  rcases List.mem_cons.mp appears with rfl|tail
  · refine ⟨⟨⟨⟨trivial,trivial⟩,trivial⟩,trivial⟩,?_,?_⟩
    · intro c used; cases List.mem_singleton.mp used
      refine ⟨⟨trivial,trivial⟩,?_⟩
      intro e written; cases List.mem_singleton.mp written; trivial
    · intro e written; cases List.mem_singleton.mp written; trivial
  · cases List.mem_singleton.mp tail
    exact GeneralDeclarativeRecordReplay330.covered.1 _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem wanted : Declared registry root := GeneralDeclarativeRecordResolve326.declared

theorem source_compiles :
    ∃ v used, Inputs catalogue interpretation keep w0 root.arguments decl.head v used ∧
      used.map Prod.fst = [0,4,1] := by
  obtain ⟨v,used,witness,_,names,_⟩ := GeneralDeclarativeCompoundSources338.exact (w := w0) (arg := arg)
    (actual_source (restriction support)) keep anchors bounds
  refine ⟨v,used,?_,names⟩
  simpa only [List.append_nil] using Inputs.compound
    (c := catalogue) (i := interpretation) (p := pat) witness Inputs.nil

def before : Assignment := fun n =>
  (if n = 0 ∨ n = 1 then record 7 (record 9 int exactEmpty) exactEmpty else
    if n = 2 then record 7 (record 9 int emptyRecord) emptyRecord else
    if n = 6 then exactEmpty else int,Common.rowEmpty)

theorem source_valid : Models initial before := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro e used
    change e ∈ [(0,1),(1,2)] at used
    rcases List.mem_cons.mp used with rfl|tail
    · exact subtype_refl _
    · cases List.mem_singleton.mp tail
      exact common_record_mono 7 (common_record_mono 9 (subtype_refl _) exactEmpty_below_width)
        exactEmpty_below_width
  · intro row used
    change row ∈ [eql,eqh,eqi] at used
    simp only [List.mem_cons,List.not_mem_nil,or_false] at used
    rcases used with rfl|rfl|rfl <;> exact eqv_refl _

theorem center_not_read {term} : (⟨1,term⟩ : Equation) ∉ initial.equations := by
  intro here
  change (⟨1,term⟩ : Equation) ∈ [eql,eqh,eqi] at here
  simp only [List.mem_cons,List.not_mem_nil,or_false] at here
  rcases here with h|h|h <;> cases h

theorem matches_original : Heads (restriction support) catalogue interpretation root decl :=
  .cons (GeneralDeclarativeCompoundHeads338.positive (p := support) (pat := pat)
    (actual_source _) anchors bounds) .nil

def fallback (_ : Nat) : Capture := ⟨3,3,3⟩
def targets (_ : Clause) (_ : Nat) : Nat := 5

/-- The new traversal has an actual model on a checked declaration,
even though no original center equation exists. Its ordered
occurrence list reaches the unchanged body compiler. -/
theorem checked_compilation :
    ∃ (v : World (fun _ => False)), ∃ uses m ordinary children,
      fitsModel v m ∧ uses.map Prod.fst = [0,4,1] ∧
      compileBody registry interpretation root decl v.state uses keep fallback targets = some (ordinary,children) ∧
      ∃ b : @Body registry interpretation root decl ordinary children, b.targets = targets ∧ b.spans = uses := by
  obtain ⟨v,uses,seen,ordered⟩ := source_compiles
  obtain ⟨assignment,fit,_⟩ := (input_exact seen).1.2 before ⟨source_valid,fun _ h => False.elim (List.not_mem_nil h)⟩
  obtain ⟨state,kids,body,receipt,trace,fixed,_⟩ :=
    body_ready (d := root) (impl := decl) seen checked covered List.mem_cons_self rfl wanted fallback targets
  exact ⟨v,uses,assignment,state,kids,fit,ordered,receipt,body,fixed,trace⟩

end Yulang.GeneralDeclarativeCompoundFixture338
