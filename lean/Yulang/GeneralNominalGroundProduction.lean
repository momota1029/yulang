import Yulang.GeneralNominalGroundAccessibility

/-! Local production of child meanings from shared capture values. The
materialization and origin-selection conclusions follow from the emitter. -/
namespace Yulang.GeneralNominalGroundProduction
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalSaturationState
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalSharedCaptures
open GeneralNominalFiniteMeaning GeneralNominalStructuralContainment GeneralNominalCompoundReadback
open GeneralNominalReadbackFunctionality GeneralNominalGroundAccessibility
open GeneralNominalFeedbackSites (clauseChild)
open CommonNominalFullCarrier

theorem capture_value (packet : Packet roles) (model : GeneralNominalCommonBridge.Assignment)
    (valid : packet.Holds model) (input : name ∉ packet.declaration.outputNames)
    (usable : Usable packet name origin) (meaning : At model .actual origin value) :
    CaptureValue packet model name value := by
  obtain ⟨actual,observed⟩ := meaning.1
  have fitted := (usable.2 model valid).2 actual observed
  have equal := meaning.2 actual observed
  refine ⟨input,⟨subtype_trans fitted.1 equal.1,subtype_trans equal.2 fitted.2⟩,?_⟩
  intro other known
  have agree := usable_same known usable model valid
  exact ⟨agree.1,fun actual seen => approx_left (agree.2.2 actual _ seen observed) equal⟩

private theorem unique_key (key : α → Nat) (xs : List α)
    (unique : (xs.map key).Nodup) (a b : α) (left : a ∈ xs) (right : b ∈ xs)
    (same : key a = key b) : a = b := by
  induction xs with
  | nil => cases left
  | cons head rest ih =>
    have pair := List.nodup_cons.mp unique
    rcases List.mem_cons.mp left with equalA | tailA
    · subst a
      rcases List.mem_cons.mp right with equalB | tailB
      · subst b; rfl
      · exact False.elim (pair.1 (List.mem_map.mpr ⟨b,tailB,same.symm⟩))
    · rcases List.mem_cons.mp right with equalB | tailB
      · subst b
        exact False.elim (pair.1 (List.mem_map.mpr ⟨a,tailA,same⟩))
      · exact ih pair.2 tailA tailB

theorem emitted_clause_unique (packet : Packet roles)
    (one : first ∈ packet.declaration.requirements) (two : last ∈ packet.declaration.requirements)
    (firstSignature : first.Signature roles) (lastSignature : last.Signature roles)
    (same : clauseChild packet first firstSignature = clauseChild packet last lastSignature) : first = last := by
  have identities := congrArg (fun occurrence => occurrence.identity) same
  have encoded := (GeneralNominalIdentities.source_identity packet.context.state.seed _ _).mp identities
  have clauseEq : first.id = last.id := congrArg (fun key => key.2.2.2.1) encoded
  exact unique_key Clause.id _ packet.checked.identified.1 first last one two clauseEq

theorem shared_origin_variable (packet : Packet roles) (clause : Clause)
    (present : clause ∈ packet.declaration.requirements) (signature : clause.Signature roles)
    (index : Fin (roles clause.role).arity)
    (recorded : GeneralNominalSharedEmission.OriginAt packet (clauseChild packet clause signature) index.val origin) :
    ∃ name, Usable packet name origin ∧
      normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)) = .var name := by
  obtain ⟨other,member,otherSignature,position,same,equal,name,usable,pattern⟩ := recorded
  have clauses := emitted_clause_unique packet present member signature otherSignature same
  subst other
  have positions : index = position := Fin.ext equal
  subst position
  exact ⟨name,usable,pattern⟩

theorem raw_origin_variable (packet : Packet roles) (clause : Clause)
    (present : clause ∈ packet.declaration.requirements) (signature : clause.Signature roles)
    (index : Fin (roles clause.role).arity)
    (recorded : GeneralNominalFeedbackSites.OriginAt packet (clauseChild packet clause signature) index.val origin) :
    ∃ name, normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)) = .var name := by
  obtain ⟨other,member,otherSignature,position,same,equal,capture,_,_,_,pattern⟩ := recorded
  have clauses := emitted_clause_unique packet present member signature otherSignature same
  subst other
  have positions : index = position := Fin.ext equal
  subst position
  exact ⟨capture.name,pattern⟩

def ArgumentValue (packet : Packet roles) (model : GeneralNominalCommonBridge.Assignment)
    (clause : Clause) (signature : clause.Signature roles) (index : Fin (roles clause.role).arity)
    (value : Ty) : Prop :=
  (∃ name, normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)) = .var name ∧
    CaptureValue packet model name value ∧ ∃ origin, Usable packet name origin) ∨
  (∀ name, normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)) ≠ .var name) ∧
    ∃ term values, Canonical term ∧
      (∀ name ∈ term.leaves, CaptureValue packet model name (values name)) ∧
      GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation
        (normalize (GeneralNominalCompoundEmission.lowerRequest packet clause signature index).pattern) = quote term ∧
      denote values term = value

theorem argument_contained (packet : Packet roles) (coherence : InputCoherence packet)
    (model : GeneralNominalCommonBridge.Assignment) (valid : packet.Holds model)
    (clause : Clause) (present : clause ∈ packet.declaration.requirements) (signature : clause.Signature roles)
    (index : Fin (roles clause.role).arity) (meaning : ArgumentValue packet model clause signature index value) :
    GeneralNominalCaptureMerges.Fits model ((clauseChild packet clause signature).demand.arguments index) value := by
  rcases meaning with ⟨name,pattern,captured,_⟩ | ⟨compound,term,values,canonical,captures,translated,rfl⟩
  · have bounds : (clauseChild packet clause signature).demand.arguments index =
        (GeneralNominalPacketSupport.capture packet).inputs name := by
      change GeneralDeclarationDemands.inputInterval _ _ _ = _
      simp only [GeneralDeclarationDemands.inputInterval,pattern]
      rfl
    rw [bounds]
    exact captured.2.1
  · exact compound_child_contains packet coherence model valid clause present signature index
      compound term canonical values captures translated

theorem argument_retained (packet : Packet roles) (coherence : InputCoherence packet)
    (model : GeneralNominalCommonBridge.Assignment) (valid : packet.Holds model)
    (clause : Clause) (present : clause ∈ packet.declaration.requirements) (signature : clause.Signature roles)
    (index : Fin (roles clause.role).arity) (meaning : ArgumentValue packet model clause signature index value)
    (recorded : (GeneralNominalSharedEmission.childSite packet (clauseChild packet clause signature)).inputs[index.val]? = some (some origin)) :
    At model .actual origin value := by
  classical
  let child := clauseChild packet clause signature
  have entry : GeneralNominalSharedEmission.childOrigin packet child index = some origin := by
    change (List.ofFn (GeneralNominalSharedEmission.childOrigin packet child))[index.val]? = _ at recorded
    rw [List.getElem?_ofFn] at recorded
    split at recorded
    · exact Option.some.inj recorded
    · rename_i absent; exact False.elim (absent index.isLt)
  rcases meaning with ⟨name,pattern,captured,available⟩ | compound
  · have shared : ∃ origin, GeneralNominalSharedEmission.OriginAt packet child index.val origin := by
      obtain ⟨actual,usable⟩ := available
      exact ⟨actual,clause,present,signature,index,rfl,rfl,name,usable,pattern⟩
    have same : Classical.choose shared = origin := Option.some.inj (by
      simpa only [GeneralNominalSharedEmission.childOrigin,dite_eq_left shared] using entry)
    obtain ⟨other,usable,otherPattern⟩ := shared_origin_variable packet clause present signature index (Classical.choose_spec shared)
    have names : other = name := by rw [pattern] at otherPattern; exact Pattern.var.inj otherPattern.symm
    subst other
    exact same ▸ captured.2.2 _ usable
  · have noShared : ¬ ∃ origin, GeneralNominalSharedEmission.OriginAt packet child index.val origin := by
      rintro ⟨actual,recorded⟩
      obtain ⟨name,_,pattern⟩ := shared_origin_variable packet clause present signature index recorded
      exact compound.1 name pattern
    have noRaw : ¬ ∃ origin, GeneralNominalFeedbackSites.OriginAt packet child index.val origin := by
      rintro ⟨actual,recorded⟩
      obtain ⟨name,pattern⟩ := raw_origin_variable packet clause present signature index recorded
      exact compound.1 name pattern
    have fallback : (GeneralNominalDemandMerging.pointSite child).inputs[index.val]'(by
        rw [(GeneralNominalDemandMerging.pointSite child).arity]; exact index.isLt) = some origin := by
      simpa only [GeneralNominalSharedEmission.childOrigin,dite_eq_right noShared,
        GeneralNominalFeedbackSites.childOrigin,dite_eq_right noRaw] using entry
    have point : (child.demand.arguments index).1 = (child.demand.arguments index).2 := by
      simp only [GeneralNominalDemandMerging.pointSite,List.getElem_ofFn] at fallback
      split at fallback
      · assumption
      · cases fallback
    have identity : Origin.source (child.demand.arguments index).1 = origin := by
      simp only [GeneralNominalDemandMerging.pointSite,List.getElem_ofFn] at fallback
      split at fallback
      · exact Option.some.inj fallback
      · cases fallback
    subst origin
    have contained := argument_contained packet coherence model valid clause present signature index (Or.inr compound)
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual observed
    cases observed
    exact equal_endpoints_exact model contained (by rw [point]; exact ⟨subtype_refl _,subtype_refl _⟩)

theorem child_inputs (packet : Packet roles) (coherence : InputCoherence packet)
    (model : GeneralNominalCommonBridge.Assignment) (valid : packet.Holds model)
    (clause : Clause) (present : clause ∈ packet.declaration.requirements) (signature : clause.Signature roles)
    (length : labels.length = (roles clause.role).arity)
    (meanings : ∀ index : Fin (roles clause.role).arity, ∃ term,
      ClosedTerm context (labels[index.val]'(by rw [length]; exact index.isLt)) term ∧
      ArgumentValue packet model clause signature index (denote (fun _ => .bottom) term)) :
    Inputs context model (GeneralNominalSharedEmission.childSite packet (clauseChild packet clause signature)) labels := by
  refine ⟨length,?_⟩
  intro index
  obtain ⟨term,closed,meaning⟩ := meanings index
  exact ⟨term,closed,argument_contained packet coherence model valid clause present signature index meaning,
    fun origin recorded => argument_retained packet coherence model valid clause present signature index meaning recorded⟩

theorem recovered_inputs (state : State roles) (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models state model) (known : Inputs context model site labels) :
    Inputs context model (GeneralNominalFeedbackSites.recover state site) labels := by
  classical
  obtain ⟨length,meanings⟩ := known
  refine ⟨length,?_⟩
  intro index
  obtain ⟨term,closed,contained,retained⟩ := meanings index
  refine ⟨term,closed,contained,?_⟩
  intro origin recorded
  have entry : GeneralNominalFeedbackSites.recoverOrigin state site index = some origin := by
    change (List.ofFn (GeneralNominalFeedbackSites.recoverOrigin state site))[index.val]? = _ at recorded
    rw [List.getElem?_ofFn] at recorded
    split at recorded
    · exact Option.some.inj recorded
    · rename_i absent; exact False.elim (absent index.isLt)
  have bounded : index.val < site.inputs.length := by rw [site.arity]; exact index.isLt
  cases old : site.inputs[index.val]'bounded with
  | some prior =>
    have same : prior = origin := Option.some.inj (by
      simpa only [GeneralNominalFeedbackSites.recoverOrigin,old] using entry)
    subst origin
    apply retained prior
    rw [List.getElem?_eq_getElem bounded,old]
  | none =>
    by_cases equal : GeneralNominalFeedbackSites.EndpointEqual state (site.occurrence.demand.arguments index)
    · have same : Origin.source (site.occurrence.demand.arguments index).1 = origin := Option.some.inj (by
        simpa only [GeneralNominalFeedbackSites.recoverOrigin,old,ite_eq_left equal] using entry)
      subst origin
      refine ⟨⟨_,.source _⟩,?_⟩
      intro actual observed
      cases observed
      exact equal_endpoints_exact model contained (equal model valid)
    · simp only [GeneralNominalFeedbackSites.recoverOrigin,old,ite_eq_right equal] at entry
      cases entry

/-- The remaining inspection and finite-syntax obligation. Its child fields
contain capture/template evidence, not emitted-site semantics or any bound
on traces. The producer theorems above establish those site semantics. -/
def GroundCaptureFactorization (roles : Roles.RoleDecls) (registry : Registry)
    (context : GeneralNominalCandidates.Context) : Prop :=
  ∀ (state : GeneralNominalSupport.Tracked roles) (packet : Packet roles) (support : List (GeneralSourceDictionaries.Occurrence roles)),
    state.current.context.state.constructors = context.state.constructors →
    state.current.context.interpretation = context.interpretation →
    GeneralNominalFeedbackSteps.Installable registry state.current packet →
    GeneralNominalActualInspectionSteps.PacketGuard state packet support →
    packet.declaration.requirements ≠ [] →
    ∀ model, Models state.current model → packet.Holds model →
    ∀ labels, Inputs context model packet.site labels →
      ∃ capture : Nat → Pattern,
        GeneralNominalPatersonLineage.mass (substArgs capture packet.declaration.head) ≤
          GeneralNominalPatersonLineage.mass labels ∧
        ∀ clause ∈ packet.declaration.requirements, ∀ signature : clause.Signature roles,
          ∃ length : (substArgs capture clause.arguments).length = (roles clause.role).arity,
            ∀ index : Fin (roles clause.role).arity, ∃ term,
              ClosedTerm context ((substArgs capture clause.arguments)[index.val]'(by rw [length]; exact index.isLt)) term ∧
              ArgumentValue packet model clause signature index (denote (fun _ => .bottom) term)

theorem packet_production (factorization : GroundCaptureFactorization roles registry context) :
    GroundPacketProduction roles registry context := by
  intro state packet support constructors interpretation enabled guard nonempty model valid branch labels inputs
  obtain ⟨capture,bounded,children⟩ := factorization state packet support constructors interpretation
    enabled guard nonempty model valid branch labels inputs
  refine ⟨capture,bounded,?_⟩
  intro clause present signature
  obtain ⟨length,meanings⟩ := children clause present signature
  exact child_inputs packet guard.1.2.2.2 model branch clause present signature length meanings

theorem ground_accessible_of_capture_factorization (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : GeneralSourceDictionaries.Occurrence roles))
    (point : GeneralNominalActualBudget.PointSource context root)
    (ground : GroundRoots context root rootLabels)
    (factorization : GroundCaptureFactorization roles registry context) :
    Acc (fun next current => GeneralNominalActualInspectionSteps.Step registry root current next)
      (GeneralNominalSupport.initial context root) :=
  ground_accessible checked source point ground (packet_production factorization)

end Yulang.GeneralNominalGroundProduction
