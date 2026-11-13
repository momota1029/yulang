import Yulang.GeneralNominalSharedCaptures
import Yulang.GeneralNominalMaterializedHeadRecovery

/-! Finite query trees produce recipes. A nominal root switches every nested
binder to actual mode, so both allocated endpoints use one substitution. -/
namespace Yulang.GeneralNominalCompoundReadback
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalMaterialization
open GeneralNominalInspection (Query)
open GeneralNominalSharedCaptures GeneralNominalSaturationState

def quote : Expr Nat → Query
  | .leaf name => .variables [name]
  | .node test children => match test with
    | .scalar base => .scalar base
    | .structural shape => .node shape (List.ofFn fun index => quote (children index))
    | .nominal name _count => .nominal name (List.ofFn fun index => quote (children index))

def Included (first last : Schema) : Prop :=
  first.tests ⊆ last.tests ∧ first.variables ⊆ last.variables

theorem recipe_mono (recipe : Recipe first root term) (included : Included first last) :
    Recipe last root term := by
  induction recipe with
  | capture origin name member => exact .capture origin name (included.2 member)
  | node origin test children member recipes ih => exact .node origin test children (included.1 member) ih

theorem schemas_component (queries : List Query) (origins : Nat → Origin) (mode : Mode)
    (start position : Nat) (found : queries[position]? = some query) :
    Included (schema query (origins (start+position)) mode) (schemas queries origins mode start) := by
  induction queries generalizing start position with
  | nil => cases found
  | cons head tail ih =>
    cases position with
    | zero =>
      cases Option.some.inj found
      simp only [Nat.add_zero,schemas,Schema.append]
      exact ⟨List.subset_append_left _ _,List.subset_append_left _ _⟩
    | succ position =>
      have sub := ih (start+1) position found
      have same : start+(position+1) = start+1+position := by omega
      rw [same]
      simp only [schemas,Schema.append]
      exact ⟨fun _ member => List.mem_append_right _ (sub.1 member),
        fun _ member => List.mem_append_right _ (sub.2 member)⟩

theorem quote_recipe (term : Expr Nat) (root : Origin) :
    Recipe (schema (quote term) root .actual) root term := by
  induction term generalizing root with
  | leaf name => exact .capture root name (by simp [quote,schema])
  | node test children ih =>
    cases test with
    | scalar base =>
      apply Recipe.node
      · simp [quote,schema]
      · intro index; exact Fin.elim0 index
    | structural shape =>
      apply Recipe.node
      · simp [quote,schema,arity]
      · intro index
        apply recipe_mono (ih index _)
        have sub := schemas_component (List.ofFn fun index => quote (children index))
          (fun position => .structural root shape position) .actual 0 index.val (query := quote (children index)) (by simp [index.isLt])
        simp only [Included,Nat.zero_add] at sub
        simp only [Included,quote,schema,project]
        exact ⟨fun _ member => List.mem_cons_of_mem _ (sub.1 member),sub.2⟩
    | nominal name count =>
      apply Recipe.node
      · simp [quote,schema,arity]
      · intro index
        apply recipe_mono (ih index _)
        have sub := schemas_component (List.ofFn fun index => quote (children index))
          (fun position => .nominal root name position) .actual 0 index.val (query := quote (children index)) (by simp [index.isLt])
        simp only [Included,Nat.zero_add] at sub
        simp only [Included,quote,schema,project]
        exact ⟨fun _ member => List.mem_cons_of_mem _ (sub.1 member),sub.2⟩

theorem nominal_mode_independent (name count : Nat) (children : Fin count → Expr Nat)
    (root : Origin) (mode : Mode) :
    schema (quote (.node (.nominal name count) children)) root mode =
      schema (quote (.node (.nominal name count) children)) root .actual := by simp only [quote,schema]

theorem nominal_recipe (name count : Nat) (children : Fin count → Expr Nat)
    (root : Origin) (mode : Mode) :
    Recipe (schema (quote (.node (.nominal name count) children)) root mode) root
      (.node (.nominal name count) children) := by
  rw [nominal_mode_independent]
  exact quote_recipe _ _

theorem usable_same (one : Usable packet name first) (two : Usable packet name last)
    (model : GeneralNominalCommonBridge.Assignment) (valid : packet.Holds model) :
    Same model first last := by
  obtain ⟨capture,member,captured,recorded⟩ := two.1.1
  obtain ⟨other,kept,agree⟩ := one.1.2 capture member captured
  have equal := Option.some.inj (kept.symm.trans recorded)
  exact equal ▸ agree model valid

noncomputable def representative (packet : Packet roles) (name : Nat) : Origin := by
  classical
  exact if existsOrigin : ∃ origin, Usable packet name origin then Classical.choose existsOrigin else .source 0

theorem representative_usable (available : ∃ origin, Usable packet name origin) :
    Usable packet name (representative packet name) := by
  classical
  simpa only [representative,dite_eq_left available] using Classical.choose_spec available

theorem input_coherent (packet : Packet roles) (coherence : InputCoherence packet)
    (model : GeneralNominalCommonBridge.Assignment) (valid : packet.Holds model) :
    Coherent model (GeneralNominalPacketSupport.inputSchema packet)
      (fun name => .leaf (representative packet name)) := by
  refine ⟨((GeneralNominalPacketSupport.packet_exact packet model).mp valid).2.1.2.2.1,?_⟩
  intro entry member actual
  obtain ⟨origin,usable,agree⟩ := coherence entry member actual
  exact same_trans (agree model valid)
    (usable_same usable (representative_usable ⟨origin,usable⟩) model valid)

theorem request_included (state : GeneralNominalState.State) (interpretation : GeneralNominalInspection.Interpretation)
    (requests : List Request) (request : Request) (member : request ∈ requests) :
    Included (schema (GeneralNominalInspection.translate state.constructors interpretation
      (GeneralDeclarationPatterns.normalize request.pattern)) (.source request.target) request.mode)
      (generated state interpretation requests) := by
  exact GeneralNominalMaterializedHeadRecovery.component_membership _ _ (List.mem_map.mpr ⟨request,member,rfl⟩)

theorem input_request_readback (packet : Packet roles) (coherence : InputCoherence packet)
    (request : Request) (requested : request ∈ GeneralNominalPacketSupport.inputRequests packet)
    (translated : GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation
      (GeneralDeclarationPatterns.normalize request.pattern) = quote (.node (.nominal name count) children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : packet.Holds model) :
    Holds model ((Expr.node (.nominal name count) children).bind
      (fun binder => .leaf (representative packet binder))) (.source request.target) := by
  have included := request_included packet.context.state packet.context.interpretation
    (GeneralNominalPacketSupport.inputRequests packet) request requested
  rw [translated] at included
  exact recipe_readback (recipe_mono (nominal_recipe name count children _ request.mode) included)
    (input_coherent packet coherence model valid)

theorem input_request_over (packet : Packet roles) (coherence : InputCoherence packet)
    (request : Request) (requested : request ∈ GeneralNominalPacketSupport.inputRequests packet)
    (translated : GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation
      (GeneralDeclarationPatterns.normalize request.pattern) = quote (.node (.nominal name count) children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : packet.Holds model)
    (basis : List Origin)
    (represented : ∀ binder ∈ (Expr.node (.nominal name count) children).leaves,
      representative packet binder ∈ basis) :
    Holds model ((Expr.node (.nominal name count) children).bind
      (fun binder => .leaf (representative packet binder))) (.source request.target) ∧
    ∀ leaf ∈ ((Expr.node (.nominal name count) children).bind
      (fun binder => .leaf (representative packet binder))).leaves, leaf ∈ basis := by
  refine ⟨input_request_readback packet coherence request requested translated model valid,?_⟩
  intro leaf member
  obtain ⟨binder,present,found⟩ := (leaves_bind _ _ leaf).mp member
  have equal : leaf = representative packet binder := List.mem_singleton.mp found
  exact equal ▸ represented binder present

end Yulang.GeneralNominalCompoundReadback
