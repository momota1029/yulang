import Yulang.GeneralDeclarativeI65PreparedMixedWhere401

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarations (Checked)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeSourceEmission322 (inputs useOutput demand)
open GeneralDictionaryAssociatedProvenance (lookup lookup_exact)
open CommonRoleOutermostResolver (Dictionary)
open CommonNominalFullCarrier (Ty)

def AuthoredRequestSignature401 (s : State) (q : Request) : Prop :=
  q.demand.arguments.length = ((authoredRegistry s.current).roles q.demand.role).arity ∧
    DeclaredOriginalOutputs400 s q

private theorem source_input_length401 (names : GeneralDeclarativeSourceEmission322.Names)
    (compound : Nat → GeneralDeclarativeWhere319.Capture) (first : Nat)
    (ps : List GeneralDeclarationPatterns.Pattern) :
    (inputs names compound first ps).length = ps.length := by
  induction ps generalizing first with
  | nil => rfl
  | cons p rest ih => simp [inputs,ih]

/-- Real generated where requests inherit the genuine role arity and
declared associated output names from the written clause signature.
No per-child copy of the input check or assumption of unique names
is needed. This is independent of the B6 result data. -/
theorem exact_where_requests_have_authored_signature401 {s q}
    (f : AuthoredBodyFrame393 s q) (checked : Checked (authoredRegistry s.current)) :
    ∀ child ∈ frameWhereKids400 f, AuthoredRequestSignature401 s child := by
  intro child occurs
  have well := checked.2 f.decl (List.mem_of_getElem? f.authored)
  unfold frameWhereKids400 children at occurs
  obtain ⟨⟨need,i⟩,atIndex,eq⟩ := List.mem_map.mp occurs
  subst child
  obtain ⟨_,limit,same⟩ := List.mem_zipIdx atIndex
  simp only [Nat.zero_add,Nat.sub_zero] at limit same
  have literal : need ∈ f.clauses.map LiteralWhereEntry.demand := by
    rw [same]
    exact List.getElem_mem limit
  obtain ⟨entry,listed,isDemand⟩ := List.mem_map.mp literal
  subst need
  obtain ⟨clause,source,which⟩ := List.mem_map.mp
    (show entry ∈ f.decl.requirements.map f.whereFor from listed)
  subst entry
  have declared := well.signature.2.2.2 clause source
  change AuthoredRequestSignature401 s ⟨q.occurrence ++ [i],(f.whereFor clause).demand⟩
  constructor
  · exact (source_input_length401 f.names (f.placement.compound clause) 0 clause.arguments).trans declared.1
  · intro j
    have inside : j.val < clause.outputs.length := by
      simpa [AuthoredBodyFrame393.whereFor,demand] using j.isLt
    let eqn := clause.outputs[j.val]'inside
    have inSource := declared.2 eqn (List.getElem_mem inside)
    change ∃ v, ((authoredRegistry s.current).roles clause.role).assoc
      ((clause.outputs.map (useOutput f.decl f.names (f.placement.targets clause)))[j.val]'(by simpa only [List.length_map] using inside)).name = some v
    simpa only [List.getElem_map,useOutput,GeneralDeclarations.Declared,eqn] using inSource

/-- Use the role signature only once, at the root. A checked selected
declaration has the same role; actual output names and default slot
availability at this node are then sourced, not passed as a family
of extra endpoint obligations. -/
theorem signed_request_mixed_output_from_original_source401 {s q}
    (f : AuthoredBodyFrame393 s q) (checked : Checked (authoredRegistry s.current))
    (signed : AuthoredRequestSignature401 s q) (atlas : B6OccurrenceAtlas401 s)
    (typing : NamedInputAtStoredHead401 atlas f) (i : Fin q.demand.outputs.length) :
    Nonempty (NamedMixedOutput401 atlas f i) := by
  have localDecl := checked.2 f.decl (List.mem_of_getElem? f.authored)
  have role := (visible_exact s q f.decl).mp f.inScope |>.2
  have headLen : q.demand.arguments.length = f.decl.head.length :=
    signed.1.trans ((congrArg (fun r => ((authoredRegistry s.current).roles r).arity) role).symm.trans
      localDecl.signature.1.symm)
  obtain ⟨b,provided⟩ := GeneralDictionaryAssociatedProvenance.declared_covered
    (authoredRegistry s.current).roles f.decl localDecl.signature q.demand.outputs[i].name
    (role ▸ signed.2 i)
  obtain ⟨plan,read⟩ := typing i b provided
  have covered := original_frame_slot_coverage399 f checked headLen
    (default_positions_from_authored_role_decl399 s) provided
  obtain ⟨rhs,formed⟩ := exact_mixed_names_are_substitutable401 (f.slots b) plan covered
  exact ⟨⟨b,provided,plan,read,rhs,formed⟩⟩

mutual
inductive NamedReceiptsAtTree401 {source : FrameChoice400} {s : State} (atlas : B6OccurrenceAtlas401 s) :
    {q : Request} → {d : Dictionary} → GuardedFrameTree400 source s q d → Type where
  | node {q ds} {f : AuthoredBodyFrame393 s q} {guard : source s q f}
      {kids : GuardedFrameForest400 source s (frameWhereKids400 f) ds} :
      (∀ i : Fin q.demand.outputs.length, NamedMixedOutput401 atlas f i) →
      NamedReceiptsAtForest401 atlas kids →
      NamedReceiptsAtTree401 atlas (.node f guard kids)

inductive NamedReceiptsAtForest401 {source : FrameChoice400} {s : State} (atlas : B6OccurrenceAtlas401 s) :
    {qs : List Request} → {ds : List Dictionary} → GuardedFrameForest400 source s qs ds → Type where
  | nil : NamedReceiptsAtForest401 atlas .nil
  | cons : NamedReceiptsAtTree401 atlas first → NamedReceiptsAtForest401 atlas rest →
      NamedReceiptsAtForest401 atlas (.cons first rest)
end

/-- Inhabiting this exact receipt tree requires no per-child
Declaration/arity premise and no per-model or structural row-read
premise for the lexical names. Independent gates and genuine B6
input at the original body still belong to the source inference. -/
theorem source_tree_needs_only_root_signature_and_B6_input401 {source s q d}
    (tree : GuardedFrameTree400 source s q d) (checked : Checked (authoredRegistry s.current))
    (atlas : B6OccurrenceAtlas401 s)
    (b6 : ∀ q (f : AuthoredBodyFrame393 s q), source s q f → NamedInputAtStoredHead401 atlas f)
    (root : AuthoredRequestSignature401 s q) :
    Nonempty (NamedReceiptsAtTree401 atlas tree) := by
  classical
  exact GuardedFrameTree400.rec
    (motive_1 := fun q _ tree => AuthoredRequestSignature401 s q →
      Nonempty (NamedReceiptsAtTree401 atlas tree))
    (motive_2 := fun qs _ trees => (∀ q ∈ qs, AuthoredRequestSignature401 s q) →
      Nonempty (NamedReceiptsAtForest401 atlas trees))
    (fun f guard _ sons signed => by
      obtain ⟨converted⟩ := sons (exact_where_requests_have_authored_signature401 f checked)
      exact ⟨.node (fun i => Classical.choice (signed_request_mixed_output_from_original_source401
        f checked signed atlas (b6 _ f guard) i)) converted⟩)
    (fun _ => ⟨.nil⟩)
    (fun _ _ left right localSigs => by
      obtain ⟨a⟩ := left (localSigs _ List.mem_cons_self)
      obtain ⟨b⟩ := right (fun q has => localSigs q (List.mem_cons_of_mem _ has))
      exact ⟨.cons a b⟩)
    tree root


def ExactNamedOutputMeaning401 {s q atlas f i} (m : Model)
    (out : NamedMixedOutput401 (s := s) (q := q) atlas f i) : Prop :=
  out.receipt.occurrence = q.occurrence ∧ out.receipt.outputOrdinal = i.val ∧
    out.receipt.original = q.demand.outputs[i] ∧
    lookup (authoredRegistry s.current).roles f.decl q.demand.outputs[i].name = some out.body ∧
    atlas.read q f.ordinal i out.body = some out.plan ∧
    ∃ value : Ty, out.receipt.actualEquation m = some (q.demand.outputs[i].target,value) ∧
      evaluateMixedRhs401 (sourceRead401 m (f.slots out.body)) out.plan = some value

theorem original_named_mixed_output_meaning401 {s q atlas f i} (m : Model)
    (out : NamedMixedOutput401 (s := s) (q := q) atlas f i)
    (checked : Checked (authoredRegistry s.current)) :
    ExactNamedOutputMeaning401 m out := by
  have row := checked.2 f.decl (List.mem_of_getElem? f.authored)
  exact ⟨rfl,rfl,rfl,(lookup_exact _ _ row.identified.2.2.1 _ _).mpr out.supplied,
    out.originalTyped,named_mixed_output_is_fixed_equation401 out m⟩

mutual
def ExactNamedTreeMeaning401 (m : Model) {source s q d atlas}
    {tree : GuardedFrameTree400 source s q d} : NamedReceiptsAtTree401 atlas tree → Prop
  | .node out rest => (∀ i, ExactNamedOutputMeaning401 m (out i)) ∧ ExactNamedForestMeaning401 m rest

def ExactNamedForestMeaning401 (m : Model) {source s qs ds atlas}
    {forest : GuardedFrameForest400 source s qs ds} : NamedReceiptsAtForest401 atlas forest → Prop
  | .nil => True
  | .cons a b => ExactNamedTreeMeaning401 m a ∧ ExactNamedForestMeaning401 m b
end

theorem original_named_forest_uses_one_model401 {source s q d atlas}
    {tree : GuardedFrameTree400 source s q d} (receipts : NamedReceiptsAtTree401 atlas tree)
    (checked : Checked (authoredRegistry s.current)) (m : Model) :
    ExactNamedTreeMeaning401 m receipts := by
  exact NamedReceiptsAtTree401.rec
    (motive_1 := fun {_ _} _ out => ExactNamedTreeMeaning401 m out)
    (motive_2 := fun {_ _} _ out => ExactNamedForestMeaning401 m out)
    (fun out _ rest => by
      rw [ExactNamedTreeMeaning401]
      exact ⟨fun i => original_named_mixed_output_meaning401 m (out i) checked,rest⟩)
    (by simp only [ExactNamedForestMeaning401])
    (fun a b ha hb => by
      rw [ExactNamedForestMeaning401]
      exact ⟨ha,hb⟩)
    receipts

/-- One genuine independent guarded source tree and B6 annotations
at the original addressed bodies suffice for exact same-model
source values at all leaf and internal occurrences, with only the
root request signature. Where signatures and named output slots
are discharged inside the proof from authored source. -/
theorem original_guarded_tree_produces_mixed_source_values401 {source s q d}
    (tree : GuardedFrameTree400 source s q d) (checked : Checked (authoredRegistry s.current))
    (atlas : B6OccurrenceAtlas401 s)
    (b6 : ∀ q (f : AuthoredBodyFrame393 s q), source s q f → NamedInputAtStoredHead401 atlas f)
    (root : AuthoredRequestSignature401 s q) :
    ∃ receipts : NamedReceiptsAtTree401 atlas tree, ∀ m : Model, ExactNamedTreeMeaning401 m receipts := by
  obtain ⟨receipts⟩ := source_tree_needs_only_root_signature_and_B6_input401 tree checked atlas b6 root
  exact ⟨receipts,fun m => original_named_forest_uses_one_model401 receipts checked m⟩

end Yulang.GeneralDeclarativeI65
