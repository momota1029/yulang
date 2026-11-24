import Yulang.GeneralDeclarativeI65CollectAliasNeeds384
import Yulang.GeneralDeclarativeI65RigidAtVisit384

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarativeK2Graph321 (Shape)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeInspect321 (Inspects)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralSourceMetadataRows291 (interpretation)

theorem unary_step_map_view384 {left right : Nat → Shape → Prop}
    (incl : ∀ n h, left n h → right n h)
    {s start outer site query} (step : UnaryOrdinaryStep384 left s start outer site query) :
    UnaryOrdinaryStep384 right s start outer site query := by
  cases step with
  | primitive safe seen known => exact .primitive safe (incl _ _ seen) known
  | nominal safe seen known => exact .nominal safe (incl _ _ seen) known
  | variant safe seen known => exact .variant safe (incl _ _ seen) known

theorem unary_trace_map_view384 {left right : Nat → Shape → Prop}
    (incl : ∀ n h, left n h → right n h)
    {s start outer site query} (walk : UnaryOrdinaryPrefix384 left s start outer site query) :
    UnaryOrdinaryPrefix384 right s start outer site query := by
  induction walk with
  | here read => exact .here read
  | next step _ rest => exact .next (unary_step_map_view384 incl step) rest

theorem unary_finding_map_view384 {left right : Nat → Shape → Prop}
    (incl : ∀ n h, left n h → right n h) {s site expr verdict}
    (found : UnaryVisitFinding384 left s site expr verdict) :
    UnaryVisitFinding384 right s site expr verdict := by
  cases found with
  | k2 cycle => exact .k2 cycle
  | rigid safe seen mismatch => exact .rigid safe (incl _ _ seen) mismatch

theorem collect_sourced_unary_step384
    {source ordinary tagged direct intervals constraints s start outer site query}
    (step : UnaryOrdinaryStep384
      (SourcedObserved384 source ordinary tagged direct intervals constraints s) s start outer site query) :
    ∃ needs, Nonempty (ExactSupportForest384 source ordinary tagged s needs) ∧
      UnaryOrdinaryStep384 (OpenObserved384 direct intervals constraints s needs) s start outer site query := by
  cases step with
  | primitive safe seen read =>
    obtain ⟨xs,ready,seen⟩ := collect_sourced_observation384 seen
    exact ⟨xs,ready,.primitive safe seen read⟩
  | nominal safe seen read =>
    obtain ⟨xs,ready,seen⟩ := collect_sourced_observation384 seen
    exact ⟨xs,ready,.nominal safe seen read⟩
  | variant safe seen read =>
    obtain ⟨xs,ready,seen⟩ := collect_sourced_observation384 seen
    exact ⟨xs,ready,.variant safe seen read⟩

theorem collect_sourced_unary_trace384
    {source ordinary tagged direct intervals constraints s start outer site query}
    (walk : UnaryOrdinaryPrefix384
      (SourcedObserved384 source ordinary tagged direct intervals constraints s) s start outer site query) :
    ∃ needs, Nonempty (ExactSupportForest384 source ordinary tagged s needs) ∧
      UnaryOrdinaryPrefix384 (OpenObserved384 direct intervals constraints s needs) s start outer site query := by
  induction walk with
  | here read => exact ⟨[],⟨.nil⟩,.here read⟩
  | next step _ tail =>
    obtain ⟨xs,⟨first⟩,step⟩ := collect_sourced_unary_step384 step
    obtain ⟨ys,⟨last⟩,trail⟩ := tail
    exact ⟨xs ++ ys,⟨append_exact_supports384 first last⟩,.next
      (unary_step_map_view384 (fun _ _ => reindex_open_observed384 (needs_embed_left384 xs ys)) step)
      (unary_trace_map_view384 (fun _ _ => reindex_open_observed384 (needs_embed_right384 xs ys)) trail)⟩

theorem collect_sourced_unary_finding384
    {source ordinary tagged direct intervals constraints s site query verdict}
    (read : UnaryVisitFinding384
      (SourcedObserved384 source ordinary tagged direct intervals constraints s) s site query verdict) :
    ∃ needs, Nonempty (ExactSupportForest384 source ordinary tagged s needs) ∧
      UnaryVisitFinding384 (OpenObserved384 direct intervals constraints s needs) s site query verdict := by
  cases read with
  | k2 cycle => exact ⟨[],⟨.nil⟩,.k2 cycle⟩
  | rigid safe seen clash =>
    obtain ⟨xs,ready,seen⟩ := collect_sourced_observation384 seen
    exact ⟨xs,ready,.rigid safe seen clash⟩

/-- The earliest ordinary source root before the local need vector
has been collected. Neither layout of a support proof nor an
externally chosen smaller set of visible rows defines this root. -/
structure SourcedUnaryRoot384 (view : Nat → Shape → Prop) (s : State)
    (q : Request) (row : Declaration) (root : Nat) (query : Expr) : Prop where
  visibleRow : row ∈ visible s q
  operand : ∃ arg : Capture, q.demand.arguments = [arg] ∧ root = arg.lower
  written : ∃ pat : Pattern, row.head = [pat] ∧
    translate (authoredRegistry s.current).constructors
      (interpretation s.current.environment.source.snapshot) (normalize pat) = some query
  ready : ∃ shape, view root shape
  inspects : Inspects query
  safe : ¬RootCycle383 s q

theorem sourced_root_with_exact_slots384
    {source ordinary tagged direct intervals constraints s q row root query}
    (atRoot : SourcedUnaryRoot384
      (SourcedObserved384 source ordinary tagged direct intervals constraints s) s q row root query) :
    ∃ needs, Nonempty (ExactSupportForest384 source ordinary tagged s needs) ∧
      UnaryOrdinaryRoot384 direct intervals constraints s needs q row root query := by
  obtain ⟨shape,read⟩ := atRoot.ready
  obtain ⟨xs,ready,read⟩ := collect_sourced_observation384 read
  exact ⟨xs,ready,⟨atRoot.visibleRow,atRoot.operand,atRoot.written,⟨shape,read⟩,
    atRoot.inspects,atRoot.safe⟩⟩

theorem reindex_unary_root384
    {direct intervals constraints s prior revised q row root query}
    (larger : NeedEmbedding384 prior revised)
    (literal : UnaryOrdinaryRoot384 direct intervals constraints s prior q row root query) :
    UnaryOrdinaryRoot384 direct intervals constraints s revised q row root query := by
  obtain ⟨shape,read⟩ := literal.ready
  exact ⟨literal.inScope,literal.literal,literal.translated,⟨shape,reindex_open_observed384 larger read⟩,
    literal.inspects,literal.safe⟩

/-- Collect exact output reads *from* an independently sourced
ordinary unary visit. Order is root support, literal path support,
then the visited-site observation if one was needed. The selected
result and scope are not inferred from this positive fragment. -/
theorem collect_literal_unary_finding384
    {source ordinary tagged direct intervals constraints s q row root outer site inner verdict}
    (atRoot : SourcedUnaryRoot384
      (SourcedObserved384 source ordinary tagged direct intervals constraints s) s q row root outer)
    (path : UnaryOrdinaryPrefix384
      (SourcedObserved384 source ordinary tagged direct intervals constraints s) s root outer site inner)
    (read : UnaryVisitFinding384
      (SourcedObserved384 source ordinary tagged direct intervals constraints s) s site inner verdict) :
    ∃ needs, Nonempty (ExactSupportForest384 source ordinary tagged s needs) ∧
      UnaryOrdinaryRoot384 direct intervals constraints s needs q row root outer ∧
      UnaryOrdinaryPrefix384 (OpenObserved384 direct intervals constraints s needs) s root outer site inner ∧
      UnaryVisitFinding384 (OpenObserved384 direct intervals constraints s needs) s site inner verdict := by
  obtain ⟨xs,⟨xProof⟩,x⟩ := sourced_root_with_exact_slots384 atRoot
  obtain ⟨ys,⟨yProof⟩,y⟩ := collect_sourced_unary_trace384 path
  obtain ⟨zs,⟨zProof⟩,z⟩ := collect_sourced_unary_finding384 read
  have keepRoot := reindex_unary_root384 (needs_embed_left384 xs ys) x
  have keepPath := unary_trace_map_view384
    (fun _ _ => reindex_open_observed384 (needs_embed_right384 xs ys)) y
  have retain := needs_embed_left384 (xs ++ ys) zs
  exact ⟨(xs ++ ys) ++ zs,⟨append_exact_supports384 (append_exact_supports384 xProof yProof) zProof⟩,
    reindex_unary_root384 retain keepRoot,
    unary_trace_map_view384 (fun _ _ => reindex_open_observed384 retain) keepPath,
    unary_finding_map_view384
      (fun _ _ => reindex_open_observed384 (needs_embed_right384 (xs ++ ys) zs)) z⟩

end Yulang.GeneralDeclarativeI65
