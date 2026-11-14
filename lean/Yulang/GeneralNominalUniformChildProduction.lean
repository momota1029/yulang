import Yulang.GeneralNominalUniformCaptureProduction

/-! The source label fixes a unique finite query tree. Real child emission
therefore yields one tree for all models, rather than a separate existential
choice in each branch. -/
namespace Yulang.GeneralNominalUniformChildProduction
open GeneralDeclarationPatterns GeneralNominalOriginTerms GeneralNominalRecursiveInspection
open GeneralNominalCompoundReadback GeneralNominalOpenPatternLabels GeneralNominalFiniteMeaning
open GeneralNominalSaturationState GeneralNominalSharedCaptures GeneralNominalHoleElimination
open GeneralNominalGroundProduction GeneralNominalStructuralContainment

private theorem children_quote (one two : Fin count → Expr Nat)
    (equal : (List.ofFn fun i => quote (one i)) = (List.ofFn fun i => quote (two i)))
    (position : Fin count) : quote (one position) = quote (two position) := by
  have atPosition := congrArg (fun values => values[position.val]?) equal
  simpa [List.getElem?_ofFn,position.isLt] using atPosition

theorem quote_injective (first last : Expr Nat) (equal : quote first = quote last) : first = last := by
  induction first generalizing last with
  | leaf name =>
    cases last with
    | leaf other =>
      apply congrArg Expr.leaf
      simpa only [quote,GeneralNominalInspection.Query.variables.injEq,List.cons.injEq,and_true] using equal
    | node test children => cases test <;> cases equal
  | node test children ih =>
    cases last with
    | leaf name => cases test <;> cases equal
    | node other parts =>
      cases test with
      | scalar base =>
        cases other with
        | scalar other =>
          have same := GeneralNominalInspection.Query.scalar.inj equal
          subst other
          congr 1
          exact funext fun index => Fin.elim0 index
        | structural | nominal => cases equal
      | structural shape =>
        cases other with
        | scalar | nominal => cases equal
        | structural other =>
          have partsEqual := GeneralNominalInspection.Query.node.inj equal
          obtain ⟨rfl,queries⟩ := partsEqual
          congr 1
          exact funext fun index => ih index _ (children_quote children parts queries index)
      | nominal name count =>
        cases other with
        | scalar | structural => cases equal
        | nominal other arity =>
          have partsEqual := GeneralNominalInspection.Query.nominal.inj equal
          obtain ⟨rfl,queries⟩ := partsEqual
          have lengths := congrArg List.length queries
          simp only [List.length_ofFn] at lengths
          change count = arity at lengths
          subst arity
          congr 1
          exact funext fun index => ih index _ (children_quote children parts queries index)

theorem label_unique (one : Label context pattern first) (two : Label context pattern last) : first = last :=
  quote_injective first last (one.2.1.symm.trans two.2.1)

variable {roles : Roles.RoleDecls}
variable {models : GeneralNominalCommonBridge.Assignment → Prop}
variable {values : GeneralNominalCommonBridge.Assignment → Nat → CommonNominalFullCarrier.Ty}

/-- Positively supplied actual capture meanings are sufficient. The proof
never infers pending from a missing provenance certificate. -/
theorem child_uniform (state : State roles) (packet : Packet roles)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state packet)
    (constructors : packet.context.state.constructors = context.state.constructors)
    (interpretation : packet.context.interpretation = context.interpretation)
    (generation : GenerationGuard tracked packet) (inhabited : ∃ model, models model)
    (replacement : Nat → Expr Nat) (remaining : List Nat)
    (images : ∀ name, Label context (capture name) (replacement name))
    (imagesClosed : ∀ name, Needed packet name → Closed remaining (replacement name))
    (meanings : ∀ model, models model → ∀ name, Needed packet name →
      CaptureValue packet model name (denote (values model) (replacement name)))
    (clause : GeneralDeclarations.Clause) (present : clause ∈ packet.declaration.requirements)
    (signature : clause.Signature roles) (index : Fin (roles clause.role).arity) :
    ∃ term, Label context
      (normalize ((normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt))).subst capture)) term ∧
      Closed remaining term ∧ ∀ model, models model → ArgumentValue packet model clause signature index (denote (values model) term) := by
  obtain ⟨model,valid⟩ := inhabited
  obtain ⟨term,label,_,closed⟩ := GeneralNominalOpenChildProduction.child_argument state packet enabled constructors interpretation generation
    (values model) replacement remaining images imagesClosed (meanings model valid) clause present signature index
  refine ⟨term,label,closed,?_⟩
  intro other holds
  obtain ⟨result,otherLabel,meaning,_⟩ := GeneralNominalOpenChildProduction.child_argument state packet enabled constructors interpretation generation
    (values other) replacement remaining images imagesClosed (meanings other holds) clause present signature index
  exact label_unique label otherLabel ▸ meaning

/-- Every positively retained emitted child origin receives a uniform
source-labelled readback over the original surviving holes. -/
theorem child_readback (state : State roles) (packet : Packet roles)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state packet)
    (constructors : packet.context.state.constructors = context.state.constructors)
    (interpretation : packet.context.interpretation = context.interpretation)
    (generation : GenerationGuard tracked packet) (inhabited : ∃ model, models model)
    (coherence : InputCoherence packet) (branch : ∀ model, models model → packet.Holds model)
    (replacement : Nat → Expr Nat) (remaining : List Nat)
    (images : ∀ name, Label context (capture name) (replacement name))
    (imagesClosed : ∀ name, Needed packet name → Closed remaining (replacement name))
    (meanings : ∀ model, models model → ∀ name, Needed packet name →
      CaptureValue packet model name (denote (values model) (replacement name)))
    (leafValues : ∀ model, models model → ∀ name ∈ remaining, At model .actual (origins name) (values model name))
    (clause : GeneralDeclarations.Clause) (present : clause ∈ packet.declaration.requirements)
    (signature : clause.Signature roles) (index : Fin (roles clause.role).arity)
    (recorded : (GeneralNominalSharedEmission.childSite packet (GeneralNominalFeedbackSites.clauseChild packet clause signature)).inputs[index.val]? = some (some origin)) :
    ∃ term, GeneralNominalUniformHoleLabels.Labelled models context origins remaining origin
      (normalize ((normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt))).subst capture)) term := by
  obtain ⟨term,label,closed,meaning⟩ := child_uniform state packet enabled constructors interpretation generation inhabited replacement remaining
    images imagesClosed meanings clause present signature index
  refine ⟨term,label,?_,closed⟩
  intro model valid
  apply GeneralNominalUniformCaptureProduction.meaning_holds term label.2.2
    (argument_retained packet coherence model (branch model valid) clause present signature index (meaning model valid) recorded)
  intro name member
  exact leafValues model valid name (closed name member)

end Yulang.GeneralNominalUniformChildProduction
