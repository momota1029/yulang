import Yulang.GeneralDeclarativeI65B6ExactProjections399

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarations (Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDictionaryAssociatedProvenance (Body Supplies)
open CommonRoleOutermostResolver (Dictionary)

/-- I-71's alternate output payload. Structural RHS nodes remain part
of the typed tree; no old nominal-argument-vector encoding is a field. -/
inductive LiteralTreeWrite400 where
  | ordinary (row : GeneralDeclarativeHead320.Equation)
  | typed (target : Nat) (rhs : SourceRhsCode394)

def LiteralTreeWrite400.target : LiteralTreeWrite400 → Nat
  | .ordinary row => row.left
  | .typed target _ => target

/-- Independent original-body production in the same scope. This is
about source syntax, not model satisfaction, selection, or retention.
The existing ordinary branch keeps its exact written equation. -/
inductive SourceWritesTree400 {s q} (f : AuthoredBodyFrame393 s q)
    (body : Body) (target : Nat) : LiteralTreeWrite400 → Type where
  | ordinary {row} : BodyWrite393 f body target (.ordinary row) →
      SourceWritesTree400 f body target (.ordinary row)
  | typed
      (plan : B6ValuePlan398 s false (normalize (bodyPattern body)))
      (instantiated : ExactRoleRhs398 (normalize (bodyPattern body))) :
      instantiateB6Value398 (f.slots body) plan = some instantiated →
      B6UsesFit398 s (f.slots body) plan.needs →
      CompoundSourceRhs394 s (f.slots body) false (normalize (bodyPattern body)) instantiated.val →
      SourceWritesTree400 f body target (.typed target instantiated.val)

structure TreeOutput400 {s q} (f : AuthoredBodyFrame393 s q)
    (i : Fin q.demand.outputs.length) where
  body : Body
  supplied : Supplies (authoredRegistry s.current).roles f.decl q.demand.outputs[i].name body
  write : LiteralTreeWrite400
  source : SourceWritesTree400 f body q.demand.outputs[i].target write

structure TreeReceipt400 where
  occurrence : List Nat
  ordinal : Nat
  requested : GeneralSourceState.Output
  originalBody : Body
  written : LiteralTreeWrite400

def TreeOutput400.receipt {s q f i} (o : TreeOutput400 (s := s) (q := q) f i) : TreeReceipt400 :=
  ⟨q.occurrence,i.val,q.demand.outputs[i],o.body,o.write⟩

theorem tree_output_preserves_actual_request400 {s q f i}
    (o : TreeOutput400 (s := s) (q := q) f i) :
    o.receipt.occurrence = q.occurrence ∧ o.receipt.ordinal = i.val ∧
      q.demand.outputs[i.val]? = some o.receipt.requested ∧
      o.receipt.written.target = q.demand.outputs[i].target ∧
      Supplies (authoredRegistry s.current).roles f.decl
        o.receipt.requested.name o.receipt.originalBody := by
  refine ⟨rfl,rfl,List.getElem?_eq_getElem i.isLt,?_,o.supplied⟩
  cases o with
  | mk body supplier written derived =>
    cases derived with
    | ordinary old => cases old; rfl
    | typed _ _ _ _ _ => rfl

theorem tree_receipt_reads_exact_original_rhs400 {s q f i}
    (o : TreeOutput400 (s := s) (q := q) f i) :
    match o.receipt.written with
    | .ordinary row => BodyWrite393 f o.receipt.originalBody q.demand.outputs[i].target (.ordinary row)
    | .typed target rhs => target = q.demand.outputs[i].target ∧
        rhs.source = normalize (bodyPattern o.receipt.originalBody) ∧
        CompoundSourceRhs394 s (f.slots o.receipt.originalBody) false
          (normalize (bodyPattern o.receipt.originalBody)) rhs := by
  cases o with
  | mk body supplier written derived =>
    cases derived with
    | ordinary old => exact old
    | typed _ _ _ _ yes => exact ⟨rfl,compound_source_preserves_syntax394 yes,yes⟩

/-- The exact original symbolic B6 tree survives as data, not
something later recovered through proof irrelevance or re-inference. -/
def TreeOutput400.originalPlan {s q f i} (o : TreeOutput400 (s := s) (q := q) f i) :
    Option (B6ValuePlan398 s false (normalize (bodyPattern o.body))) :=
  by
    cases o with
    | mk body supplied written source =>
      cases source with
      | ordinary original => exact none
      | typed plan instantiated run kind meaning => exact some plan

/-- Compatibility of the existing ordinary path, not a condition for
the new typed path. No conversion from arbitrary trees is attempted. -/
def TreeOutput400.fromOrdinary400 {s q f i}
    {out : AuthoredOutput393 (s := s) (q := q) f i}
    {row : GeneralDeclarativeHead320.Equation} (ordinary : out.write = .ordinary row) :
    TreeOutput400 f i :=
  ⟨out.body,out.supplied,.ordinary row,.ordinary (ordinary ▸ out.builds)⟩

theorem typed_output_from_B6_without_old_receipt400 {s q}
    (f : AuthoredBodyFrame393 s q) (atlas : B6SymbolicAtlas398 s)
    (i : Fin q.demand.outputs.length) (unique : (f.decl.associated.map Equation.name).Nodup)
    {b : Body}
    (supplier : Supplies (authoredRegistry s.current).roles f.decl q.demand.outputs[i].name b)
    {plan : B6ValuePlan398 s false (normalize (bodyPattern b))}
    (typed : atlas.read f.ordinal b = some plan)
    (compatible : B6UsesFit398 s (f.slots b) plan.needs) :
    ∃ (retained : TreeOutput400 f i) (out : LogicalRoleOutput398 f i),
      logicalOutputAt398 f atlas i unique = some out ∧
      retained.body = b ∧ HEq retained.originalPlan (some plan) ∧
        retained.receipt.written = .typed q.demand.outputs[i].target out.equation.rhs := by
  obtain ⟨out,made,source,_,meaning⟩ :=
    supplied_symbolic_body_produces_exact_logical_output398 f atlas i unique supplier typed compatible
  obtain ⟨inst,run,real⟩ := symbolic_replay_meaning_with_supplied_capture_kinds398 plan compatible
  have same := compound_source_rhs_functional394 real _ meaning
  exact ⟨⟨b,supplier,.typed q.demand.outputs[i].target inst.val,.typed plan inst run compatible real⟩,
    out,made,rfl,by rfl,by
      change LiteralTreeWrite400.typed q.demand.outputs[i].target inst.val = _
      rw [same]⟩

/-- The new record is built from genuine pre-output data. In particular
it does not ask for an old event with one old-style receipt per output. -/
structure TreeLocalEvent400 (s : State) (q : Request) where
  frame : AuthoredBodyFrame393 s q
  outputs : ∀ i : Fin q.demand.outputs.length, TreeOutput400 frame i

def TreeLocalEvent400.receipts {s q} (e : TreeLocalEvent400 s q) : List TreeReceipt400 :=
  List.ofFn fun i => (e.outputs i).receipt

def TreeLocalEvent400.kids {s q} (e : TreeLocalEvent400 s q) : List Request :=
  children q (e.frame.clauses.map LiteralWhereEntry.demand)

theorem tree_event_original_order400 {s q} (event : TreeLocalEvent400 s q)
    (i : Fin q.demand.outputs.length) :
    event.receipts.length = q.demand.outputs.length ∧
      event.receipts[i.val]? = some (event.outputs i).receipt := by
  simp [TreeLocalEvent400.receipts,i.isLt]

def DeclaredOriginalOutputs400 (s : State) (q : Request) : Prop :=
  ∀ i : Fin q.demand.outputs.length,
    ∃ v, ((authoredRegistry s.current).roles q.demand.role).assoc q.demand.outputs[i].name = some v

def FrameB6SourceInput400 {s q} (f : AuthoredBodyFrame393 s q)
    (atlas : B6SymbolicAtlas398 s) : Prop :=
  ∀ (i : Fin q.demand.outputs.length) (body : Body),
    Supplies (authoredRegistry s.current).roles f.decl q.demand.outputs[i].name body →
    ∃ plan : B6ValuePlan398 s false (normalize (bodyPattern body)),
      atlas.read f.ordinal body = some plan ∧
      B6UsesFit398 s (f.slots body) plan.needs

/-- Every selected original source output gets a typed RHS directly
from B6, at its old occurrence/ordinal/target. This accepts no new
language cases, and assumes no proof of the theorem's meaning. -/
theorem exact_preoutput_frame_produces_tree_event400 {s q}
    (f : AuthoredBodyFrame393 s q)
    (checked : GeneralDeclarations.Checked (authoredRegistry s.current))
    (names : DeclaredOriginalOutputs400 s q)
    (atlas : B6SymbolicAtlas398 s) (provided : FrameB6SourceInput400 f atlas) :
    ∃ e : TreeLocalEvent400 s q, e.frame = f ∧
      e.kids = children q (f.clauses.map LiteralWhereEntry.demand) ∧
      ∀ i : Fin q.demand.outputs.length,
        ∃ (out : LogicalRoleOutput398 f i)
          (unique : (f.decl.associated.map Equation.name).Nodup),
          logicalOutputAt398 f atlas i unique = some out ∧
          (e.outputs i).receipt.written = .typed q.demand.outputs[i].target out.equation.rhs := by
  classical
  let r := authoredRegistry s.current
  have checkedRow := checked.2 f.decl (List.mem_of_getElem? f.authored)
  have roleEq := (visible_exact s q f.decl).mp f.inScope |>.2
  have unique := checkedRow.identified.2.2.1
  have build (i : Fin q.demand.outputs.length) :
      ∃ (retained : TreeOutput400 f i) (out : LogicalRoleOutput398 f i),
        logicalOutputAt398 f atlas i unique = some out ∧
        retained.receipt.written = .typed q.demand.outputs[i].target out.equation.rhs := by
    obtain ⟨body,supplied⟩ := GeneralDictionaryAssociatedProvenance.declared_covered r.roles
      f.decl checkedRow.signature q.demand.outputs[i].name (roleEq ▸ names i)
    obtain ⟨plan,typed,fit⟩ := provided i body supplied
    obtain ⟨retained,out,exact,_,_,writes⟩ :=
      typed_output_from_B6_without_old_receipt400 f atlas i unique supplied typed fit
    exact ⟨retained,out,exact,writes⟩
  let event : TreeLocalEvent400 s q := ⟨f,fun i => Classical.choose (build i)⟩
  refine ⟨event,rfl,rfl,?_⟩
  intro i
  obtain ⟨out,run,writes⟩ := Classical.choose_spec (build i)
  exact ⟨out,unique,run,writes⟩

end Yulang.GeneralDeclarativeI65
