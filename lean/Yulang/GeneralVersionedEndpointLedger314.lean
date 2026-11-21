import Yulang.GeneralVersionedEndpointModes314

set_option backward.isDefEq.respectTransparency false
/-! Exact historical rows for compound where endpoints. The coordinates
are old even when their prospective operand projections have changed. -/
namespace Yulang.GeneralVersionedEndpointLedger314
open GeneralDeclarations GeneralSourceDictionaries GeneralDeclarationPatterns GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedPlans231 (emittedRequests emittedSchema variables)
open GeneralNominalCenteredHeadMatSchemas (generated_contains emissionRequests inputRequests)
open GeneralNominalVersionedFrame231 (capture frame)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralVersionedCompoundRows313 (address mode)
open GeneralNominalMaterialization (Request)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCommonBridge (Assignment)

theorem previous {s : State roles} {p q : Plan roles}
    (actual : Reachable registry root s)
    (current : Frame (Compiled registry) s.core focus key p)
    (stored : q ∈ s.plans)
    (identity : q.packet.site.occurrence.identity = p.packet.site.occurrence.identity)
    (rule : q.packet.declaration = p.packet.declaration)
    (clause : Clause) (inClause : clause ∈ p.packet.declaration.requirements)
    (index : Nat) (kind : Nat) (polarity : kind = 3 ∨ kind = 4)
    (pat : Pattern) (existsAt : clause.arguments[index]? = some pat)
    (compound : ∀ n, normalize pat ≠ .var n)
    (row : GeneralNominalCenteredHeadMatSchemas.Equation) (compiled : translate p.packet.registry.constructors p.packet.context.interpretation pat = some row.expression)
    (target : row.target = address p kind clause.id index) (tag : row.mode = mode kind) :
    row ∈ (emittedSchema q).equations := by
  have cfg := GeneralVersionedSiteOrigins312.stored_current_config actual stored
  have seedEq := cfg.1.trans (congrArg (fun c => c.state.seed) current.context_eq).symm
  have constructorEq : q.packet.registry.constructors = p.packet.registry.constructors :=
    congrArg Registry.constructors (((GeneralNominalVersionedMixedRegistry234.reachable actual).2.1 q stored).trans current.registry_eq.symm)
  have interp := cfg.2.2.trans (congrArg GeneralNominalCandidates.Context.interpretation current.context_eq).symm
  have oldCompile : translate q.packet.registry.constructors q.packet.context.interpretation pat = some row.expression := by
    rwa [constructorEq,interp]
  have targetId : row.target = address q kind clause.id index := by
    simpa only [address,seedEq,identity,rule] using target
  have listed : clause ∈ q.packet.declaration.requirements := rule.symm ▸ inClause
  let sig := q.packet.checked.signature.2.2.2 clause listed
  obtain ⟨inRange,equals⟩ := List.getElem?_eq_some_iff.mp existsAt
  let i : Fin (roles clause.role).arity := ⟨index,by rw [← sig.1]; exact inRange⟩
  let alloc := (frame q.packet).allocation q.packet.declaration.id clause
  let emission := GeneralDeclarationDemands.emit q.packet.site.occurrence.identity q.packet.declaration
    clause sig (capture q.packet) alloc
  have member : emission ∈ GeneralDeclarationDemands.emitAll q.packet.site.occurrence.identity
      q.packet.declaration q.packet.checked.signature (capture q.packet) ((frame q.packet).allocation q.packet.declaration.id) :=
    List.mem_map.mpr ⟨⟨clause,listed⟩,by simp,rfl⟩
  have canon := (GeneralCanonicalChildOrder.canonicalEmit_perm q.packet.site.occurrence.identity q.packet.declaration
    q.packet.checked (capture q.packet) ((frame q.packet).allocation q.packet.declaration.id)).mem_iff.mp member
  let rq : Request := ⟨pat,row.target,row.mode⟩
  have matchArg : clause.arguments[i.val]'(by rw [sig.1]; exact i.isLt) = pat := equals
  have bounds : GeneralDeclarationDemands.inputInterval (capture q.packet) (alloc.arguments i) pat =
      (address q 3 clause.id index,address q 4 clause.id index) := by
    unfold GeneralDeclarationDemands.inputInterval
    split
    · rename_i n normalized
      exact False.elim (compound n normalized)
    · rfl
  have oldRequests : rq ∈ emissionRequests emission := by
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    refine ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,?_⟩
    change rq ∈ inputRequests ⟨_,_,_⟩
    unfold inputRequests
    dsimp only
    let sourcePat := clause.arguments[i.val]'(by rw [sig.1]; exact i.isLt)
    let sourceBounds := GeneralDeclarationDemands.inputInterval (capture q.packet) (alloc.arguments i) sourcePat
    change rq ∈ ([⟨sourcePat,sourceBounds.1,.lower⟩,⟨sourcePat,sourceBounds.2,.upper⟩] : List Request)
    have samePat : sourcePat = pat := matchArg
    have sameBounds : sourceBounds = (address q 3 clause.id index,address q 4 clause.id index) := by
      unfold sourceBounds
      rw [samePat,bounds]
    rw [samePat,sameBounds]
    rcases polarity with rfl|rfl
    · change (⟨pat,row.target,row.mode⟩ : Request) ∈ [⟨pat,address q 3 clause.id index,.lower⟩,_]
      rw [targetId,tag]
      exact List.mem_cons_self
    · change (⟨pat,row.target,row.mode⟩ : Request) ∈ [_,⟨pat,address q 4 clause.id index,.upper⟩]
      rw [targetId,tag]
      exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have emitted : rq ∈ emittedRequests q.packet :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨emission,canon,oldRequests⟩)
  have rowWritten := generated_contains emitted oldCompile
  cases row
  exact rowWritten

theorem on_reads {s : State roles} {p q : Plan roles} {m : Assignment} {row : GeneralNominalCenteredHeadMatSchemas.Equation}
    (stored : q ∈ s.plans) (valid : Models s m)
    (previous : row ∈ (emittedSchema q).equations)
    (same : ∀ cell ∈ GeneralNominalVersionedExpressionFrame236.reads row.mode row.expression,
      Equivalent (variables q m cell.1 cell.2) (variables p m cell.1 cell.2)) :
    row.Holds (variables p m) m :=
  GeneralVersionedEndpointModes314.reuse_exact ((valid.2.1 q stored).2.2 row previous) same


open GeneralVersionedCompoundRows313 (Taut Cell clause_arg materializes)
open GeneralVersionedNormalizedVariable313 (normalized_value)
open GeneralNominalCenteredHeadMatSchemas (materialize generated)
open GeneralVersionedRootWrites312 (whereRequests from_request)
open GeneralVersionedComputedRows313 (OutputCell output_row)

abbrev Row := GeneralNominalCenteredHeadMatSchemas.Equation

def Endpoint (p : Plan roles) (eq : Row) : Prop :=
  ∃ clause ∈ p.packet.declaration.requirements, ∃ pos kind pat,
    (kind = 3 ∨ kind = 4) ∧ clause.arguments[pos]? = some pat ∧
    (∀ n, normalize pat ≠ .var n) ∧
    translate p.packet.registry.constructors p.packet.context.interpretation pat = some eq.expression ∧
    eq.target = address p kind clause.id pos ∧ eq.mode = mode kind

theorem endpoint_row (p : Plan roles)
    (clause : Clause) (inClause : clause ∈ p.packet.declaration.requirements) (sig : clause.Signature roles)
    (i : Fin (roles clause.role).arity) (kind : Nat) (which : kind = 3 ∨ kind = 4)
    (eq : GeneralNominalCenteredHeadMatSchemas.Equation)
    (found : eq ∈ (materialize p.packet.registry.constructors p.packet.context.interpretation
      (let pat := clause.arguments[i.val]'(by rw [sig.1]; exact i.isLt)
       let pair := GeneralDeclarationDemands.inputInterval (capture p.packet)
         (((frame p.packet).allocation p.packet.declaration.id clause).arguments i) pat
       ⟨pat, if kind = 3 then pair.1 else pair.2, mode kind⟩)).equations) :
    Taut p eq ∨ Endpoint p eq := by
  let pos : Fin clause.arguments.length := ⟨i.val,by rw [sig.1]; exact i.isLt⟩
  let pat := clause.arguments[pos.val]
  obtain ⟨translated,target,modeEq⟩ := materializes found
  change translate p.packet.registry.constructors p.packet.context.interpretation pat = _ at translated
  let boundPair := GeneralDeclarationDemands.inputInterval (capture p.packet)
    (((frame p.packet).allocation p.packet.declaration.id clause).arguments i) pat
  change eq.target = (if kind = 3 then boundPair.1 else boundPair.2) at target
  change eq.mode = mode kind at modeEq
  have patEq : clause.arguments[i.val]? = some pat := List.getElem?_eq_some_iff.mpr ⟨pos.isLt,rfl⟩
  cases normalForm : normalize pat with
  | var n =>
    have notOutput := clause_arg p clause inClause pos n normalForm
    have pairEq : boundPair = (capture p.packet).inputs n := by
      simp [boundPair,GeneralDeclarationDemands.inputInterval,normalForm]
    rw [pairEq] at target
    left
    intro m
    have equivalence := GeneralVersionedNormalizedVariable313.normalized_value pat normalForm translated (variables p m) (mode kind)
    unfold GeneralNominalCenteredHeadMatSchemas.Equation.Holds
    rw [target,modeEq]
    rcases which with rfl|rfl <;>
      simpa only [mode,variables,notOutput,ite_false,↓reduceIte,show (4:Nat) ≠ 3 from by decide] using GeneralFiniteTypedWrites312.symmetric equivalence
  | app | record | variant | join =>
    all_goals
      have pairEq : boundPair = (address p 3 clause.id i.val,address p 4 clause.id i.val) := by
        simp only [boundPair,GeneralDeclarationDemands.inputInterval,normalForm]
        rfl
      rw [pairEq] at target
      right
      refine ⟨clause,inClause,i.val,kind,pat,which,patEq,?_,translated,?_,modeEq⟩
      · intro name same
        rw [normalForm] at same
        cases same
      · rcases which with rfl|rfl <;> exact target

theorem exact_where (p : Plan roles) (eq : Row)
    (found : eq ∈ (generated p.packet.registry.constructors p.packet.context.interpretation
      (whereRequests p)).equations) : Taut p eq ∨ Endpoint p eq ∨ OutputCell p eq := by
  obtain ⟨rq,seen,materialized⟩ := from_request found
  obtain ⟨emit,emitted,inside⟩ := List.mem_flatMap.mp seen
  have posted := (GeneralCanonicalChildOrder.canonicalEmit_perm p.packet.site.occurrence.identity p.packet.declaration
    p.packet.checked (capture p.packet) ((frame p.packet).allocation p.packet.declaration.id)).mem_iff.mpr emitted
  unfold GeneralDeclarationDemands.emitAll at posted
  obtain ⟨item,_,rfl⟩ := List.mem_map.mp posted
  let clause := item.val
  have requirement := p.packet.checked.signature.2.2.2 clause item.property
  unfold GeneralNominalCenteredHeadMatSchemas.emissionRequests at inside
  rcases List.mem_append.mp inside with input|output
  · obtain ⟨arg,args,byArg⟩ := List.mem_flatMap.mp input
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp args
    rcases List.mem_cons.mp byArg with rfl|next
    · exact (endpoint_row p clause item.property requirement index 3 (.inl rfl) eq materialized).elim
        .inl (fun h => .inr (.inl h))
    · cases List.mem_singleton.mp next
      exact (endpoint_row p clause item.property requirement index 4 (.inr rfl) eq materialized).elim
        .inl (fun h => .inr (.inl h))
  · obtain ⟨request,requestMember,rfl⟩ := List.mem_map.mp output
    obtain ⟨rule,ruleMember,rfl⟩ := List.mem_map.mp requestMember
    exact (output_row p clause item.property rule ruleMember eq materialized).elim .inl
      (fun h => .inr (.inr h))


theorem previous_of_endpoint {s : State roles} {p q : Plan roles}
    (actual : Reachable registry root s) (current : Frame (Compiled registry) s.core focus key p)
    (stored : q ∈ s.plans)
    (identity : q.packet.site.occurrence.identity = p.packet.site.occurrence.identity)
    (rule : q.packet.declaration = p.packet.declaration)
    {eq : Row} (cell : Endpoint p eq) : eq ∈ (emittedSchema q).equations := by
  obtain ⟨clause,seen,index,kind,pat,pol,atPat,compound,compile,target,tag⟩ := cell
  exact previous actual current stored identity rule clause seen index kind pol pat atPat compound eq compile target tag

end Yulang.GeneralVersionedEndpointLedger314
