import Yulang.GeneralDeclarativeI65CompletionRead383

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (Dictionary)
open GeneralDeclarativeWitnessDeclaredState357 (AuthoredNominal Seen authoredRegistry)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDictionaryAssociatedProvenance (Supplies)

/-- Exact source identity for the existing explicit tagged unary
covariant output form. The tag, constructor and binder are read from
the supplied associated equation, and the payload is the actual
capture center. A row with the same logical target is not enough.
This is a declarative written-body fragment, not compiler admission
or an assertion that all typed output forms have this shape. -/
def TaggedUnarySourceAt383 (s : State) (q : Request) (decl : Declaration)
    (capture : Nat → Capture) (ordinal : Nat) (row : AuthoredNominal) : Prop :=
  ∃ out, q.demand.outputs[ordinal]? = some out ∧
    ∃ body tag box binder,
      Supplies (authoredRegistry s.current).roles decl out.name (.explicit body) ∧
      body.rhs = .variant tag (.app box [.var binder]) ∧
      binder ∈ decl.inputNames ∧
      s.modes[box]? = some [⟨.value,.covariant⟩] ∧
      row = ⟨out.target,tag,box,[.value (.var (capture binder).center)]⟩

abbrev ChosenTaggedBinding383 :=
  State → Request → Dictionary → Declaration → (Nat → Capture) → Prop

/-- The exact tagged row uses a declaration and binding supplied by the
actual independent source selection judgment, not reconstructed from
the dictionary key, row equality, compiler output or model values. -/
def LogicalTaggedUnaryOutput383 (chosen : ChosenTaggedBinding383)
    (s : State) (q : Request) (d : Dictionary) (ordinal : Nat) (row : AuthoredNominal) : Prop :=
  ∃ decl capture, chosen s q d decl capture ∧ TaggedUnarySourceAt383 s q decl capture ordinal row

abbrev DirectNominal383 := State → AuthoredNominal → Prop

/-- No old typed release packet, author identity or effective version:
a generated row is readable only with a finite proof of the exact
logical producer and its actual output at the original ordinal. -/
inductive TaggedNominalRead383 (rules : SelectedSourceRule383)
    (direct : DirectNominal383) (chosen : ChosenTaggedBinding383)
    (s : State) : AuthoredNominal → Type where
  | written {row : AuthoredNominal} : direct s row → row ∈ s.current.visible →
      TaggedNominalRead383 rules direct chosen s row
  | output {row : AuthoredNominal} (q : Request) (d : Dictionary) (ordinal : Nat) :
      SelectedSourceProof383 rules s q d →
      LogicalTaggedUnaryOutput383 chosen s q d ordinal row →
      row ∈ s.current.visible → TaggedNominalRead383 rules direct chosen s row

/-- Every model fitting the same state sees the precise tagged written
value. This gives an authored-value observation, not a NativeSyntax
comparison, candidate election or a cross-carrier coercion. -/
theorem tagged_nominal_read_seen_in_same_model383
    {rules : SelectedSourceRule383} {direct : DirectNominal383}
    {chosen : ChosenTaggedBinding383} {s : State} {row : AuthoredNominal}
    (read : TaggedNominalRead383 rules direct chosen s row) (m : Model) (fit : Fits s m) :
    Seen m.assignment m.authoredValues row := by
  cases read with
  | written _ present => exact fit.1.2 _ present
  | output _ _ _ _ _ present => exact fit.1.2 _ present

theorem tagged_output_read_recovers_literal_target383
    {rules : SelectedSourceRule383} {direct : DirectNominal383}
    {chosen : ChosenTaggedBinding383} {s : State} {row : AuthoredNominal}
    (read : TaggedNominalRead383 rules direct chosen s row) (notWritten : ¬direct s row) :
    ∃ q d ordinal out, Nonempty (SelectedSourceProof383 rules s q d) ∧
      LogicalTaggedUnaryOutput383 chosen s q d ordinal row ∧
      q.demand.outputs[ordinal]? = some out ∧ row.place = out.target := by
  cases read with
  | written directProof _ => exact (notWritten directProof).elim
  | output q d ordinal proof eq _ =>
    have inner := eq
    obtain ⟨_,_,_,out,atOrdinal,_,_,_,_,_,_,_,_,rowExact⟩ := inner
    exact ⟨q,d,ordinal,out,⟨proof⟩,eq,atOrdinal,congrArg AuthoredNominal.place rowExact⟩

/-- From the scoped logical body and its selected producer, get both
the supported observation and the actual model-valued captured center
at the fixed target. In particular no endpoint is substituted for the
center, and the conclusion holds for every model of the same state. -/
theorem completed_tagged_unary_body_observes_actual_center383
    {rules : SelectedSourceRule383} {direct : DirectNominal383}
    {chosen : ChosenTaggedBinding383} {s : State} {q : Request} {d : Dictionary}
    {decl : Declaration} {capture : Nat → Capture} {ordinal : Nat} {row : AuthoredNominal}
    (proof : SelectedSourceProof383 rules s q d)
    (selected : chosen s q d decl capture)
    (body : TaggedUnarySourceAt383 s q decl capture ordinal row)
    (present : row ∈ s.current.visible) :
    Nonempty (TaggedNominalRead383 rules direct chosen s row) ∧
    ∃ out tag box binder, q.demand.outputs[ordinal]? = some out ∧
      ∀ m, Fits s m →
        ∃ v, m.authoredValues out.target = some v ∧ v.tag = tag ∧ v.name = box ∧
          v.arguments = [.inl (m.assignment (capture binder).center).1] := by
  let read : TaggedNominalRead383 rules direct chosen s row :=
    .output q d ordinal proof ⟨decl,capture,selected,body⟩ present
  refine ⟨⟨read⟩,?_⟩
  obtain ⟨out,h,_,tag,box,binder,_,_,_,_,rfl⟩ := body
  refine ⟨out,tag,box,binder,h,?_⟩
  intro m fit
  exact tagged_nominal_read_seen_in_same_model383 read m fit

end Yulang.GeneralDeclarativeI65
