import Yulang.GeneralDeclarativeI65B6TapePreoutput399
import Yulang.GeneralDeclarativeI65B6OrdinarySource398

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (All₂)
open GeneralDeclarations (Declaration Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEmissionForest322 (Placement)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDictionaryAssociatedProvenance (Body Supplies lookup lookup_exact)

/-- Positional scoping of the actual original role defaults. This is
an independent source-input condition, not derived from lookup success
or declared-name coverage. It does not change the language. -/
def OriginalDefaultPositions399 (s : State) : Prop :=
  ∀ (role name : Nat) (rhs : Roles.Term),
    ((authoredRegistry s.current).roles role).assoc name = some (some rhs) →
    ∀ n ∈ (normalize (bodyPattern (.default role name rhs))).variables,
      n < ((authoredRegistry s.current).roles role).arity

private theorem ordered_args_length399 {s capture args head}
    (observed : All₂ (DeepHead s capture) args head) :
    args.length = head.length := by
  induction observed with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem observed_preoutput_demand_head_lengths399 {s q row}
    (head : SourceHead s q row) :
    q.demand.arguments.length = row.head.length := by
  cases head with
  | ordered input observed => exact ordered_args_length399 observed
  | joined j => rw [j.demanded,j.head]; rfl

theorem original_frame_slot_coverage399 {s q}
    (f : AuthoredBodyFrame393 s q)
    (checked : GeneralDeclarations.Checked (authoredRegistry s.current))
    (length : q.demand.arguments.length = f.decl.head.length)
    (defaults : OriginalDefaultPositions399 s)
    {name source}
    (supplied : Supplies (authoredRegistry s.current).roles f.decl name source) :
    ∀ n ∈ (normalize (bodyPattern source)).variables, (f.slots source n).isSome = true := by
  cases supplied with
  | explicit written attached _ => exact explicit_B4_slots_total398 f checked attached
  | default rhs _ declared =>
    intro n uses
    have shape := (checked.2 f.decl (List.mem_of_getElem? f.authored)).signature.1
    have atRole := defaults f.decl.role name rhs declared n uses
    have actual : n < q.demand.arguments.length := by rw [length,shape]; exact atRole
    simp [AuthoredBodyFrame393.slots,List.getElem?_eq_getElem actual]

theorem ordinary_source_writes_original_literal399 {s q}
    (f : AuthoredBodyFrame393 s q) (atlas : B6OrdinaryAtlas398 s)
    (i : Fin q.demand.outputs.length)
    (unique : (f.decl.associated.map Equation.name).Nodup)
    {b : Body}
    (supplied : Supplies (authoredRegistry s.current).roles f.decl q.demand.outputs[i].name b)
    (typed : B6OrdinarySource398 s b) (read : atlas.read f.ordinal b = some typed)
    (slots : ∀ n ∈ (normalize (bodyPattern b)).variables, (f.slots b n).isSome = true) :
    ∃ out : AuthoredOutput393 f i,
      ordinary_role_output_from_B6398 f atlas i unique = some out ∧ out.body = b ∧
      ∃ equation : GeneralDeclarativeHead320.Equation, out.write = .ordinary equation ∧
        equation.left = q.demand.outputs[i].target ∧
        equation.right = GeneralDeclarativeSubstitution320.logical
          (GeneralDeclarativeOutputs320.bodyCapture q.demand f.names.input b) .actual typed.term := by
  let equation : GeneralDeclarativeHead320.Equation :=
    ⟨q.demand.outputs[i].target,GeneralDeclarativeSubstitution320.logical
      (GeneralDeclarativeOutputs320.bodyCapture q.demand f.names.input b) .actual typed.term⟩
  let out : AuthoredOutput393 f i := ⟨b,supplied,.ordinary equation,.ordinary slots typed.authored⟩
  refine ⟨out,?_,rfl,equation,rfl,rfl,rfl⟩
  have hit : lookup (authoredRegistry s.current).roles f.decl q.demand.outputs[i].name = some b :=
    (lookup_exact _ _ unique _ _).mpr supplied
  have tested := List.all_eq_true.mpr slots
  unfold ordinary_role_output_from_B6398
  dsimp only
  split
  next notFound => rw [hit] at notFound; contradiction
  next selected found =>
    rw [hit] at found
    injection found with same
    subst selected
    simp [read,tested,out,equation]

/-- This is the ordinary existing-wire slice. All literal receipts
are constructed at the original positive tape before any receipt is
provided. Role-default scoping and B6 ordinary translation coverage
are explicit source inputs. We do not assert that this structural
event has an all-state local selection guard. -/
theorem positive_tape_constructs_ordinary_literal_event399 {s q row}
    {t : CandidateTape s q (visible s q)} (only : TapedMatch s q t row)
    (checked : GeneralDeclarations.Checked (authoredRegistry s.current))
    (place : Placement) (outside : Nat → Capture)
    (atlas : B6OrdinaryAtlas398 s)
    (declared : ∀ i : Fin q.demand.outputs.length,
      ∃ value, ((authoredRegistry s.current).roles q.demand.role).assoc
        q.demand.outputs[i].name = some value)
    (defaults : OriginalDefaultPositions399 s)
    (b6 : ∀ (origin : SelectedHeadOrigin395 (row := row) t)
      (i : Fin q.demand.outputs.length) (body : Body),
      Supplies (authoredRegistry s.current).roles row q.demand.outputs[i].name body →
      ∃ input : B6OrdinarySource398 s body, atlas.read origin.rawOrdinal body = some input) :
    ∃ (origin : SelectedHeadOrigin395 (row := row) t)
      (each : ∀ i, AuthoredOutput393 (preoutputFrameOfOrigin399 origin place outside) i),
      let f := preoutputFrameOfOrigin399 origin place outside
      let event := emittedEvent393 f each
      SamePreoutputFrame399 event f ∧
      StoredAt395 t origin.pick origin.visibleOrdinal ∧
      event.declaration = row ∧ event.declarationOrdinal = origin.rawOrdinal ∧
      ∀ i : Fin q.demand.outputs.length,
        (∃ unique : (row.associated.map Equation.name).Nodup,
          ordinary_role_output_from_B6398 f atlas i unique = some (each i)) ∧
        event.receipts[i.val]? = some (each i).receipt ∧
        SameEventRhs393 event f.names.input (each i).receipt ∧
        ∃ equation : GeneralDeclarativeHead320.Equation, (each i).write = .ordinary equation ∧
          equation.left = q.demand.outputs[i].target := by
  classical
  obtain ⟨origin⟩ := selected_head_original_origin395 only
  let f := preoutputFrameOfOrigin399 origin place outside
  let registry := authoredRegistry s.current
  have rowChecked := checked.2 row (List.mem_of_getElem? origin.authored)
  have roleEq := (visible_exact s q row).mp origin.pick.inScope |>.2
  have unique := rowChecked.identified.2.2.1
  have actualLength : q.demand.arguments.length = f.decl.head.length :=
    observed_preoutput_demand_head_lengths399 origin.pick.head
  have produced : ∀ i : Fin q.demand.outputs.length, ∃ out : AuthoredOutput393 f i,
      ordinary_role_output_from_B6398 f atlas i unique = some out ∧
      ∃ equation : GeneralDeclarativeHead320.Equation, out.write = .ordinary equation ∧
        equation.left = q.demand.outputs[i].target := by
    intro i
    obtain ⟨source,supplied⟩ := GeneralDictionaryAssociatedProvenance.declared_covered
      registry.roles row rowChecked.signature q.demand.outputs[i].name (roleEq ▸ declared i)
    obtain ⟨input,read⟩ := b6 origin i source supplied
    obtain ⟨out,output,_,eq,ordinary,target,_⟩ :=
      ordinary_source_writes_original_literal399 f atlas i unique supplied input read
        (original_frame_slot_coverage399 f checked actualLength defaults supplied)
    exact ⟨out,output,eq,ordinary,target⟩
  let each : ∀ i, AuthoredOutput393 f i := fun i => Classical.choose (produced i)
  refine ⟨origin,each,⟨rfl,rfl,rfl⟩,origin.stored,rfl,rfl,?_⟩
  intro i
  exact ⟨⟨unique,(Classical.choose_spec (produced i)).1⟩,
    emitted_original_sequence393 f each i,generated_original_rhs393 f each i,
    (Classical.choose_spec (produced i)).2⟩

end Yulang.GeneralDeclarativeI65
