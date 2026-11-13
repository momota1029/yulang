import Yulang.GeneralNominalFiniteMeaning
import Yulang.GeneralNominalCompoundEmission

/-! Actual input materialization contains the finite instantiated input.
This covers structural roots, nested nominal resets and repeated captures. -/
namespace Yulang.GeneralNominalStructuralContainment
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalMaterialization
open GeneralNominalReadbackFunctionality GeneralNominalFiniteMeaning
open GeneralNominalCompoundReadback GeneralNominalSaturationState GeneralNominalSharedCaptures
open CommonNominalFullCarrier

def CaptureValue (packet : Packet roles) (model : GeneralNominalCommonBridge.Assignment)
    (name : Nat) (value : Ty) : Prop :=
  name ∉ packet.declaration.outputNames ∧
  GeneralNominalCaptureMerges.Fits model ((GeneralNominalPacketSupport.capture packet).inputs name) value ∧
  ∀ origin, Usable packet name origin → At model .actual origin value

theorem included_trans (first : Included one two) (last : Included two three) : Included one three :=
  ⟨fun _ member => last.1 (first.1 member),fun _ member => last.2 (first.2 member)⟩

theorem child_included (test : Test) (children : Fin (arity test) → Expr Nat)
    (root : Origin) (mode : Mode) (index : Fin (arity test)) :
    Included (schema (quote (children index)) (project root test index) (childMode test mode))
      (schema (quote (.node test children)) root mode) := by
  cases test with
  | scalar base => exact Fin.elim0 index
  | structural shape =>
    have sub := schemas_component (List.ofFn fun index => quote (children index))
      (fun position => .structural root shape position) mode 0 index.val
      (query := quote (children index)) (by simp [index.isLt])
    simp only [Included,Nat.zero_add] at sub
    simp only [Included,quote,schema,project,childMode]
    exact ⟨fun _ member => List.mem_cons_of_mem _ (sub.1 member),sub.2⟩
  | nominal name count =>
    have sub := schemas_component (List.ofFn fun index => quote (children index))
      (fun position => .nominal root name position) .actual 0 index.val
      (query := quote (children index)) (by simp [index.isLt])
    simp only [Included,Nat.zero_add] at sub
    simp only [Included,quote,schema,project,childMode]
    exact ⟨fun _ member => List.mem_cons_of_mem _ (sub.1 member),sub.2⟩

theorem root_test (test : Test) (children : Fin (arity test) → Expr Nat) (root : Origin) (mode : Mode) :
    (root,test) ∈ (schema (quote (.node test children)) root mode).tests := by
  cases test <;> simp [quote,schema,arity]

theorem schema_contains (packet : Packet roles) (coherence : InputCoherence packet)
    (model : GeneralNominalCommonBridge.Assignment) (valid : packet.Holds model)
    (term : Expr Nat) (canonical : Canonical term) (values : Nat → Ty)
    (captures : ∀ name ∈ term.leaves, CaptureValue packet model name (values name))
    (root : Origin) (unique : Unique model root) (mode : Mode)
    (included : Included (schema (quote term) root mode) (GeneralNominalPacketSupport.inputSchema packet)) :
    At model mode root (denote values term) := by
  have materialized := ((GeneralNominalPacketSupport.packet_exact packet model).mp valid).2.1.2.2
  induction term generalizing root mode with
  | leaf name =>
    have captured := captures name (by simp [Expr.leaves])
    have member : (⟨name,root,mode⟩ : Use) ∈ (GeneralNominalPacketSupport.inputSchema packet).variables :=
      included.2 (by simp [quote,schema])
    have use := materialized.2.1 _ member
    refine ⟨use.1,?_⟩
    intro actual seen
    cases mode with
    | lower =>
      have equal : Equivalent actual (model ((GeneralNominalPacketSupport.capture packet).inputs name).1).1 := by
        simpa only [VariableHolds,ite_eq_right captured.1] using use.2 actual seen
      exact subtype_trans equal.1 captured.2.1.1
    | upper =>
      have equal : Equivalent actual (model ((GeneralNominalPacketSupport.capture packet).inputs name).2).1 := by
        simpa only [VariableHolds,ite_eq_right captured.1] using use.2 actual seen
      exact subtype_trans captured.2.1.2 equal.2
    | actual =>
      obtain ⟨origin,usable,agree⟩ := coherence _ member rfl
      have represented := captured.2.2 origin usable
      obtain ⟨other,observed⟩ := represented.1
      exact approx_left ((agree model valid).2.2 actual other seen observed) (represented.2 other observed)
  | node test children ih =>
    apply assemble test mode (fun index => denote values (children index)) unique
      (materialized.1 _ (included.1 (root_test test children root mode)))
    intro index
    apply ih index (canonical.2 index) ?_ _ (projection_unique unique test canonical.1 index)
      (childMode test mode) (included_trans (child_included test children root mode index) included)
    intro name member
    apply captures name
    simp only [Expr.leaves,List.mem_flatten,List.mem_ofFn]
    exact ⟨_,⟨index,rfl⟩,member⟩

theorem request_contains (packet : Packet roles) (coherence : InputCoherence packet)
    (model : GeneralNominalCommonBridge.Assignment) (valid : packet.Holds model)
    (request : Request) (requested : request ∈ GeneralNominalPacketSupport.inputRequests packet)
    (term : Expr Nat) (canonical : Canonical term) (values : Nat → Ty)
    (captures : ∀ name ∈ term.leaves, CaptureValue packet model name (values name))
    (translated : GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation
      (GeneralDeclarationPatterns.normalize request.pattern) = quote term) :
    Approx request.mode (model request.target).1 (denote values term) := by
  have included := request_included packet.context.state packet.context.interpretation
    (GeneralNominalPacketSupport.inputRequests packet) request requested
  rw [translated] at included
  exact (schema_contains packet coherence model valid term canonical values captures (.source request.target)
    (source_unique model request.target) request.mode included).2 _ (.source request.target)

theorem compound_child_contains (packet : Packet roles) (coherence : InputCoherence packet)
    (model : GeneralNominalCommonBridge.Assignment) (valid : packet.Holds model)
    (clause : GeneralDeclarations.Clause) (present : clause ∈ packet.declaration.requirements)
    (signature : clause.Signature roles) (index : Fin (roles clause.role).arity)
    (compound : ∀ binder, GeneralDeclarationPatterns.normalize
      (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)) ≠ .var binder)
    (term : Expr Nat) (canonical : Canonical term) (values : Nat → Ty)
    (captures : ∀ name ∈ term.leaves, CaptureValue packet model name (values name))
    (translated : GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation
      (GeneralDeclarationPatterns.normalize (GeneralNominalCompoundEmission.lowerRequest packet clause signature index).pattern) = quote term) :
    GeneralNominalCaptureMerges.Fits model
      ((GeneralNominalFeedbackSites.clauseChild packet clause signature).demand.arguments index) (denote values term) := by
  have requests := GeneralNominalCompoundEmission.emitted_requests packet clause present signature index compound
  exact ⟨request_contains packet coherence model valid _ requests.1 term canonical values captures translated,
    request_contains packet coherence model valid _ requests.2 term canonical values captures translated⟩

theorem equal_endpoints_exact (model : GeneralNominalCommonBridge.Assignment)
    (contained : GeneralNominalCaptureMerges.Fits model bounds value)
    (equal : Equivalent (model bounds.1).1 (model bounds.2).1) :
    Equivalent (model bounds.1).1 value :=
  ⟨contained.1,subtype_trans contained.2 equal.2⟩

end Yulang.GeneralNominalStructuralContainment
