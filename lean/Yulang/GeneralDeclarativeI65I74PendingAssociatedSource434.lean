import Yulang.GeneralDeclarativeI65I74StructuralWhereReceiptRefinement433
import Yulang.GeneralDeclarativeWitnessNoHead350

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PendingAssociated434
open GeneralDeclarativeI65
open GeneralDeclarations (OutputBinder Clause Declaration Checked)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWitnessDeclaredState357 (point authoredRegistry)
open CommonRecursiveNominalIntervals (Endpoint)
open GeneralDeclarativeLowerKnown321 (Knows constructorTag)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open StructuralWhere428 WhereAssociated432

def outerRow434 (key root a : Nat) : Equation := ⟨root,.nominal key [.variable a]⟩
def retainedOutput434 (key a b : Nat) : Equation := ⟨a,.nominal key [.variable b]⟩
def untouchedOutput434 (b : Nat) : Equation := ⟨b,.variable b⟩

def sourceInput434 (key a : Nat) : Endpoint Nat :=
  .nominal key [.inl (.point (.ordinary (.var a)))]

/-- The exact scoped episode has the real original authored input,
one retained associated output, and an as-yet-open physical output
name. The reflexive equality at that name is ordinary storage, not
a type constructor or a claim of completed evidence. -/
structure LiteralEpisode434 (s : I72.State) (q : Request) where
  key : Nat
  seed : Origin
  a : Nat
  b : Nat
  seedSyntax : seed.endpoint = sourceInput434 key a
  onlySeed : s.core.origins = [seed]
  noRoutes : s.core.routes = []
  noNative : s.core.current.visible = []
  exactRows : s.core.current.ordinary.equations =
    [outerRow434 key seed.slot a,retainedOutput434 key a b,untouchedOutput434 b]
  noAtoms : s.core.current.ordinary.normal.ordinary = []
  noIntervals : s.core.current.ordinary.normal.intervals = []
  sourceNeA : seed.slot ≠ a
  sourceNeB : seed.slot ≠ b
  aNeB : a ≠ b
  targetArg : q.demand.arguments = [point a]

/-- This scope contains one independently supported source head, the
one actual speculative output producer, and the one actual dependent
where child. Completion is a finite proof, not an input bit. -/
inductive EpisodeFact434 where
  | head (name : Nat)
  | parentDone
  | originalChildDone

inductive HasEpisodeFact434 (root a : Nat) : EpisodeFact434 → Prop where
  | authored : HasEpisodeFact434 root a (.head root)
  | childAtReadyHead : HasEpisodeFact434 root a (.head a) →
      HasEpisodeFact434 root a .originalChildDone
  | parentWithWhereDone : HasEpisodeFact434 root a .originalChildDone →
      HasEpisodeFact434 root a .parentDone
  | reuseCompletedOutput : HasEpisodeFact434 root a .parentDone →
      HasEpisodeFact434 root a (.head a)

theorem exact_episode_has_no_finite_completion434 {root a} (different : root ≠ a)
    {fact} (derivation : HasEpisodeFact434 root a fact) : fact = .head root := by
  induction derivation with
  | authored => rfl
  | childAtReadyHead _ ih => exact (different (EpisodeFact434.head.inj ih).symm).elim
  | parentWithWhereDone _ ih => cases ih
  | reuseCompletedOutput _ ih => cases ih

theorem pending_episode_cannot_use_its_own_produced_head434 {s q} (actual : LiteralEpisode434 s q) :
    ¬ HasEpisodeFact434 actual.seed.slot actual.a (.head actual.a) ∧
    ¬ HasEpisodeFact434 actual.seed.slot actual.a .parentDone ∧
    ¬ HasEpisodeFact434 actual.seed.slot actual.a .originalChildDone := by
  refine ⟨fun h => actual.sourceNeA (EpisodeFact434.head.inj
    (exact_episode_has_no_finite_completion434 actual.sourceNeA h)).symm,
    fun h => ?_,fun h => ?_⟩
  · cases exact_episode_has_no_finite_completion434 actual.sourceNeA h
  · cases exact_episode_has_no_finite_completion434 actual.sourceNeA h

def episodeProvenance434 {s q} (a : LiteralEpisode434 s q) : Table :=
  ⟨[outerRow434 a.key a.seed.slot a.a],[(retainedOutput434 a.key a.a a.b,a.seed.slot)],[]⟩

def actual_episode_attachment434 {s q} (a : LiteralEpisode434 s q) :
    Attached s.core.current.ordinary (episodeProvenance434 a) where
  authored := fun row seen => by
    rw [a.exactRows]
    obtain rfl := List.mem_singleton.mp seen
    exact List.mem_cons_self
  produced := fun pair seen => by
    obtain rfl := List.mem_singleton.mp seen
    rw [a.exactRows]
    exact List.mem_cons_of_mem _ List.mem_cons_self

/-- A source scope proof includes the exact original producer body
and its actual unexpanded child. The retained typed row is checked
against the original B6 body, not reinterpreted as a completed child. -/
structure OriginalPendingWhere434 (s : I72.State) (q : Request) where
  episode : LiteralEpisode434 s q
  parent : Request
  sourcePath : parent.occurrence = episode.seed.issuer
  parentArgs : parent.demand.arguments = [point episode.seed.slot]
  parentRole : parent.demand.role = q.demand.role
  event : Event s parent
  checked : Checked (authoredRegistry s.core.current)
  onlyR : (authoredRegistry s.core.current).declarations = [event.frame.decl]
  headName : Nat 
  selectedHead : event.frame.decl.head = [.app episode.key [.var headName]]
  binder : OutputBinder
  originalBinders : event.frame.decl.outputBinders = [binder]
  clause : Clause
  originalClause : event.frame.decl.requirements = [clause]
  originalRead : clause.arguments = [.var headName]
  repeatedRole : clause.role = q.demand.role
  originalChild : event.kids = [q]
  childOrdinal : q.occurrence = parent.occurrence ++ [0]
  out : Fin parent.demand.outputs.length
  exactTarget : parent.demand.outputs[out].target = episode.a
  originalBody : GeneralDeclarations.Equation
  onlyAssociated : event.frame.decl.associated = [originalBody]
  childDemandOut : q.demand.outputs = [⟨originalBody.name,episode.b⟩]
  exactBody : (event.outputs out).body = .explicit originalBody
  bodyRhs : originalBody.rhs = .app episode.key [.var binder.name]
  rawRhs : fixedValueCode403 (event.outputs out).rhs =
    some (.nominal episode.key [.variable episode.b])
  noIndependent : ∀ tag, ¬ Knows
    (GeneralDeclarativeOrigins321.restriction
      (GeneralDeclarativeWitnessOrigins350.support (actual_episode_attachment434 episode))) episode.a tag

def pendingAssociatedLocal434 : SourcePrimitives where
  elected := fun _ _ _ _ => False
  other := fun s q v ns => ns = [] ∧ v = .pending ∧ Nonempty (OriginalPendingWhere434 s q)

def pendingAssociatedKernel434 : SourcePrimitives .withEndpoint where
  elected := (ruleUnion428 R16.named426 pendingAssociatedLocal434).elected
  other := (ruleUnion428 R16.named426 pendingAssociatedLocal434).other

theorem pending_only_rule_does_not_add_selected_local_evidence434 :
    SelectedLaw428 pendingAssociatedLocal434 := by
  intro _ _ _ _ impossible
  exact impossible.elim

theorem dictionary_sound_for_pending_associated434 : DictionarySound pendingAssociatedKernel434 := by
  intro s q d classified m fit
  rcases classification_has_exact_lane_rule426 classified with named|projected
  · obtain ⟨t,e,⟨trace⟩,summary⟩ := named
    exact actual_named_trace_same_model_dictionary428
      (union_local_law428 associated_named_law432 pending_only_rule_does_not_add_selected_local_evidence434)
      trace m fit d summary
  · obtain ⟨e,⟨keep⟩,eq⟩ := projected
    have same := CommonRoleOutermostResolver.Result.selected.inj eq
    exact same.symm ▸ original_projected_leaf_with_retention_has_dictionary_evidence426 e keep m fit

end Yulang.GeneralDeclarativeI65.I72.PendingAssociated434
