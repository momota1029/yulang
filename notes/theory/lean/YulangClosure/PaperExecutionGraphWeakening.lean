import YulangClosure.PaperExecutionTypingSubstitution

/-!
Lookup-preserving graph weakening for the six existing partial paper judgments.
This module does not assert heap typing, allocation, guardedness, or the full
manuscript graph-extension or type-substitution theorem.
-/
namespace YulangClosure.PaperTypes

/-- Every old successful first-match lookup keeps the same type. -/
def GraphLookupPreserved (old new : GraphEnvironment) : Prop :=
  ∀ identity ty, lookupGraphEnvironment old identity = some ty →
    lookupGraphEnvironment new identity = some ty

/-- Shared type substitution preserves lookup preservation, including binder shift. -/
theorem GraphLookupPreserved.map {old new : GraphEnvironment}
    (hpres : GraphLookupPreserved old new) (σ : Nat → Ty) :
    GraphLookupPreserved (mapGraphEnvironment σ old) (mapGraphEnvironment σ new) := by
  intro identity ty lookup
  rw [lookupGraphEnvironment_subst] at lookup ⊢
  cases original : lookupGraphEnvironment old identity with
  | none =>
      simp only [original, Option.map_none] at lookup
      cases lookup
  | some originalType =>
      rw [hpres identity originalType original]
      simpa only [original] using lookup

theorem PaperValueTyped.graphWeaken {declarations : DeclarationTable}
    {old new : GraphEnvironment} {environment : TypeEnvironment}
    {value : Value} {ty : Ty} (hpres : GraphLookupPreserved old new)
    (derivation : PaperValueTyped declarations old environment value ty) :
    PaperValueTyped declarations new environment value ty := by
  exact PaperValueTyped.rec
    (motive_1 := fun declarations old environment values types _ =>
      ∀ new, GraphLookupPreserved old new → ValuesTyped declarations new environment values types)
    (motive_2 := fun declarations old environment values ty _ =>
      ∀ new, GraphLookupPreserved old new → ValuesAllTyped declarations new environment values ty)
    (motive_3 := fun declarations old environment fields ty _ =>
      ∀ new, GraphLookupPreserved old new → RecordPayloadsTyped declarations new environment fields ty)
    (motive_4 := fun declarations old environment value ty _ =>
      ∀ new, GraphLookupPreserved old new → PaperValueTyped declarations new environment value ty)
    (motive_5 := fun declarations old environment computation ty _ =>
      ∀ new, GraphLookupPreserved old new → PaperComputationTyped declarations new environment computation ty)
    (motive_6 := fun declarations old environment continuation response result _ =>
      ∀ new, GraphLookupPreserved old new →
        PaperContinuationTyped declarations new environment continuation response result)
    (by intro declarations graphTypes environment new hpres; exact ValuesTyped.nil)
    (by intro declarations graphTypes environment value values ty types hvalue hvalues ihValue ihValues new hpres; exact ValuesTyped.cons (ihValue new hpres) (ihValues new hpres))
    (by intro declarations graphTypes environment ty new hpres; exact ValuesAllTyped.nil)
    (by intro declarations graphTypes environment value values ty hvalue hvalues ihValue ihValues new hpres; exact ValuesAllTyped.cons (ihValue new hpres) (ihValues new hpres))
    (by intro declarations graphTypes environment recordType new hpres; exact RecordPayloadsTyped.nil)
    (by intro declarations graphTypes label tag value fields recordType presence fieldType environment hfield hvalue hfields ihValue ihFields new hpres; exact RecordPayloadsTyped.cons hfield (ihValue new hpres) (ihFields new hpres))
    (by intro declarations graphTypes environment index ty lookup new hpres; exact PaperValueTyped.variable lookup)
    (by intro declarations graphTypes environment identity ty lookup new hpres; exact PaperValueTyped.graphReference (hpres identity ty lookup))
    (by intro declarations graphTypes environment literal new hpres; exact PaperValueTyped.literal)
    (by intro declarations graphTypes environment values types hvalues ihValues new hpres; exact PaperValueTyped.tuple (ihValues new hpres))
    (by intro declarations graphTypes environment values elementType hvalues ihValues new hpres; exact PaperValueTyped.sequence (ihValues new hpres))
    (by intro declarations graphTypes environment fields recordType labels required shape unique allRequired hfields ihFields new hpres; exact PaperValueTyped.record shape unique allRequired (ihFields new hpres))
    (by intro declarations graphTypes environment body resultType hbody ihBody new hpres; exact PaperValueTyped.delay (ihBody new hpres))
    (by intro declarations graphTypes environment profile parameter body inputType outputType hbody ihBody new hpres; exact PaperValueTyped.valueLambda (ihBody new hpres))
    (by intro declarations graphTypes environment profile parameter body inputType outputType hbody ihBody new hpres; exact PaperValueTyped.computationLambda (ihBody new hpres))
    (by intro declarations graphTypes environment function argumentAdapter resultAdapter inputType outputType adaptedInputType adaptedOutputType hfunction hargument hresult ihFunction ihArgument ihResult new hpres; exact PaperValueTyped.wrap (ihFunction new hpres) (ihArgument new hpres) (ihResult new hpres))
    (by intro declarations graphTypes environment value left right hvalue ihValue new hpres; exact PaperValueTyped.injectLeft (ihValue new hpres))
    (by intro declarations graphTypes environment value left right hvalue ihValue new hpres; exact PaperValueTyped.injectRight (ihValue new hpres))
    (by intro declarations graphTypes environment value left right hleft hright ihLeft ihRight new hpres; exact PaperValueTyped.both (ihLeft new hpres) (ihRight new hpres))
    (by intro declarations graphTypes environment value ty hvalue ihValue new hpres; exact PaperValueTyped.topView (ihValue new hpres))
    (by intro declarations graphTypes environment metadata value ty hvalue ihValue new hpres; exact PaperValueTyped.view (ihValue new hpres))
    (by intro declarations graphTypes environment owners binder body responseType resultType hcontinuation ihContinuation new hpres; exact PaperValueTyped.continuation (ihContinuation new hpres))
    (by intro declarations graphTypes environment body bodyType hbody ihBody new hpres; exact PaperValueTyped.typeAbstraction (ihBody _ (hpres.map (fun i => .var (i + 1)))))
    (by intro declarations graphTypes environment function body argument hfunction ihFunction new hpres; exact PaperValueTyped.typeApplication (ihFunction new hpres))
    (by intro declarations graphTypes environment value body hvalue ihValue new hpres; exact PaperValueTyped.roll (ihValue new hpres))
    (by intro declarations graphTypes environment value ty hvalue ihValue new hpres; exact PaperComputationTyped.ret (ihValue new hpres))
    (by intro declarations graphTypes environment first body firstType resultType hfirst hbody ihFirst ihBody new hpres; exact PaperComputationTyped.letE (ihFirst new hpres) (ihBody new hpres))
    (by intro declarations graphTypes environment thunk resultType hthunk ihThunk new hpres; exact PaperComputationTyped.force (ihThunk new hpres))
    (by intro declarations graphTypes environment function thunk argumentType resultType hfunction hthunk ihFunction ihThunk new hpres; exact PaperComputationTyped.call (ihFunction new hpres) (ihThunk new hpres))
    (by intro declarations graphTypes environment tuple binders body types resultType arity htuple hbody ihTuple ihBody new hpres; exact PaperComputationTyped.split arity (ihTuple new hpres) (ihBody new hpres))
    (by intro declarations graphTypes environment value leftBinder left rightBinder right leftType rightType resultType hvalue hleft hright ihValue ihLeft ihRight new hpres; exact PaperComputationTyped.unionCase (ihValue new hpres) (ihLeft new hpres) (ihRight new hpres))
    (by intro declarations graphTypes environment value recordType label fieldType hvalue hfield ihValue new hpres; exact PaperComputationTyped.field (ihValue new hpres) hfield)
    (by intro declarations graphTypes environment value recordType label presence fieldType hvalue hfield ihValue new hpres; exact PaperComputationTyped.lookup (ihValue new hpres) hfield)
    (by intro declarations graphTypes environment operation arguments payload declaration resolved arity payloadTyping ihPayload new hpres; exact PaperComputationTyped.perform resolved arity (ihPayload new hpres))
    (by intro declarations graphTypes environment opInstance payload continuation declaration arguments resultType resolved arity instanceEq payloadTyping continuationTyping ihPayload ihContinuation new hpres; exact PaperComputationTyped.request resolved arity instanceEq (ihPayload new hpres) (ihContinuation new hpres))
    (by intro declarations graphTypes environment continuation response responseType resultType hcontinuation hresponse ihContinuation ihResponse new hpres; exact PaperComputationTyped.resume (ihContinuation new hpres) (ihResponse new hpres))
    (by intro declarations graphTypes environment value body hvalue ihValue new hpres; exact PaperComputationTyped.unroll (ihValue new hpres))
    (by intro declarations graphTypes environment identity typeArguments arguments typeArity formals result body resolved arity argumentsTyping ihArguments new hpres; exact PaperComputationTyped.template resolved arity (ihArguments new hpres))
    (by intro declarations graphTypes environment value left right hvalue ihValue new hpres
        exact PaperComputationTyped.chooseLeft (ihValue new hpres))
    (by intro declarations graphTypes environment value left right hvalue ihValue new hpres
        exact PaperComputationTyped.chooseRight (ihValue new hpres))
    (by intro declarations graphTypes environment value resultType hvalue ihValue new hpres
        exact PaperComputationTyped.absurd (ihValue new hpres))
    (by intro declarations graphTypes environment reason ty new hpres; exact PaperComputationTyped.fail)
    (by intro declarations graphTypes environment owners binder body responseType resultType hbody ihBody new hpres; exact PaperContinuationTyped.continuation (ihBody new hpres))
    derivation new hpres

theorem ValuesTyped.graphWeaken {declarations : DeclarationTable}
    {old new : GraphEnvironment} {environment : TypeEnvironment}
    {values : List Value} {types : List Ty} (hpres : GraphLookupPreserved old new)
    (derivation : ValuesTyped declarations old environment values types) :
    ValuesTyped declarations new environment values types := by
  induction values generalizing types with
  | nil => cases derivation; exact .nil
  | cons value values ih =>
      cases derivation with
      | cons head tail => exact .cons (head.graphWeaken hpres) (ih tail)

theorem ValuesAllTyped.graphWeaken {declarations : DeclarationTable}
    {old new : GraphEnvironment} {environment : TypeEnvironment}
    {values : List Value} {ty : Ty} (hpres : GraphLookupPreserved old new)
    (derivation : ValuesAllTyped declarations old environment values ty) :
    ValuesAllTyped declarations new environment values ty := by
  induction values with
  | nil => cases derivation; exact .nil
  | cons value values ih =>
      cases derivation with
      | cons head tail => exact .cons (head.graphWeaken hpres) (ih tail)

theorem RecordPayloadsTyped.graphWeaken {declarations : DeclarationTable}
    {old new : GraphEnvironment} {environment : TypeEnvironment}
    {fields : List (Label × Presence × Value)} {recordType : Ty}
    (hpres : GraphLookupPreserved old new)
    (derivation : RecordPayloadsTyped declarations old environment fields recordType) :
    RecordPayloadsTyped declarations new environment fields recordType := by
  induction fields with
  | nil => cases derivation; exact .nil
  | cons field fields ih =>
      cases derivation with
      | cons fieldProof valueProof tail =>
          exact .cons fieldProof (valueProof.graphWeaken hpres) (ih tail)

theorem PaperComputationTyped.graphWeaken {declarations : DeclarationTable}
    {old new : GraphEnvironment} {environment : TypeEnvironment}
    {computation : Computation} {ty : Ty} (hpres : GraphLookupPreserved old new)
    (derivation : PaperComputationTyped declarations old environment computation ty) :
    PaperComputationTyped declarations new environment computation ty := by
  have transported := (PaperValueTyped.delay derivation).graphWeaken hpres
  cases transported with
  | delay body => exact body

theorem PaperContinuationTyped.graphWeaken {declarations : DeclarationTable}
    {old new : GraphEnvironment} {environment : TypeEnvironment}
    {continuation : Value} {responseType resultType : Ty}
    (hpres : GraphLookupPreserved old new)
    (derivation : PaperContinuationTyped declarations old environment
      continuation responseType resultType) :
    PaperContinuationTyped declarations new environment continuation responseType resultType := by
  cases derivation with
  | continuation body => exact .continuation (body.graphWeaken hpres)

/-- A successful lookup witnesses membership of its identity in the ordered domain. -/
theorem lookupGraphEnvironment_identity_mem {environment : GraphEnvironment}
    {identity : Nat} {ty : Ty}
    (lookup : lookupGraphEnvironment environment identity = some ty) :
    identity ∈ environment.map Prod.fst := by
  induction environment with
  | nil => cases lookup
  | cons head tail ih =>
      rcases head with ⟨name, headType⟩
      by_cases same : name = identity
      · subst name; simp
      · have tailLookup : lookupGraphEnvironment tail identity = some ty := by
          simpa only [lookupGraphEnvironment, same, ite_false] using lookup
        exact List.mem_cons_of_mem _ (ih tailLookup)

/-- Freshness excludes first-match shadowing, with no extra typing premises. -/
theorem GraphLookupPreserved.freshCons {old : GraphEnvironment}
    {identity : Nat} {newType : Ty} (fresh : identity ∉ old.map Prod.fst) :
    GraphLookupPreserved old ((identity, newType) :: old) := by
  intro query ty lookup
  by_cases same : identity = query
  · subst query
    exact False.elim (fresh (lookupGraphEnvironment_identity_mem lookup))
  · simp only [lookupGraphEnvironment, same, ite_false, lookup]

/-- Reusing an existing identity with a different head type fails preservation. -/
theorem graphLookupPreserved_shadowing_falsifier (identity : Nat) :
    ¬ GraphLookupPreserved [(identity, .base .int)]
      [(identity, .base .bool), (identity, .base .int)] := by
  intro hpres
  have contradiction := hpres identity (.base .int) (by simp [lookupGraphEnvironment])
  simp [lookupGraphEnvironment] at contradiction

theorem PaperValueTyped.graphFreshCons {declarations : DeclarationTable}
    {old : GraphEnvironment} {environment : TypeEnvironment}
    {value : Value} {ty : Ty} {identity : Nat} {newType : Ty}
    (fresh : identity ∉ old.map Prod.fst)
    (derivation : PaperValueTyped declarations old environment value ty) :
    PaperValueTyped declarations ((identity, newType) :: old) environment value ty := by
  exact derivation.graphWeaken (GraphLookupPreserved.freshCons fresh)

theorem ValuesTyped.graphFreshCons {declarations : DeclarationTable}
    {old : GraphEnvironment} {environment : TypeEnvironment}
    {values : List Value} {types : List Ty} {identity : Nat} {newType : Ty}
    (fresh : identity ∉ old.map Prod.fst)
    (derivation : ValuesTyped declarations old environment values types) :
    ValuesTyped declarations ((identity, newType) :: old) environment values types := by
  exact derivation.graphWeaken (GraphLookupPreserved.freshCons fresh)

theorem ValuesAllTyped.graphFreshCons {declarations : DeclarationTable}
    {old : GraphEnvironment} {environment : TypeEnvironment}
    {values : List Value} {ty : Ty} {identity : Nat} {newType : Ty}
    (fresh : identity ∉ old.map Prod.fst)
    (derivation : ValuesAllTyped declarations old environment values ty) :
    ValuesAllTyped declarations ((identity, newType) :: old) environment values ty := by
  exact derivation.graphWeaken (GraphLookupPreserved.freshCons fresh)

theorem RecordPayloadsTyped.graphFreshCons {declarations : DeclarationTable}
    {old : GraphEnvironment} {environment : TypeEnvironment}
    {fields : List (Label × Presence × Value)} {recordType : Ty} {identity : Nat} {newType : Ty}
    (fresh : identity ∉ old.map Prod.fst)
    (derivation : RecordPayloadsTyped declarations old environment fields recordType) :
    RecordPayloadsTyped declarations ((identity, newType) :: old) environment fields recordType := by
  exact derivation.graphWeaken (GraphLookupPreserved.freshCons fresh)

theorem PaperComputationTyped.graphFreshCons {declarations : DeclarationTable}
    {old : GraphEnvironment} {environment : TypeEnvironment}
    {computation : Computation} {ty : Ty} {identity : Nat} {newType : Ty}
    (fresh : identity ∉ old.map Prod.fst)
    (derivation : PaperComputationTyped declarations old environment computation ty) :
    PaperComputationTyped declarations ((identity, newType) :: old) environment computation ty := by
  exact derivation.graphWeaken (GraphLookupPreserved.freshCons fresh)

theorem PaperContinuationTyped.graphFreshCons {declarations : DeclarationTable}
    {old : GraphEnvironment} {environment : TypeEnvironment}
    {continuation : Value} {responseType resultType : Ty} {identity : Nat} {newType : Ty}
    (fresh : identity ∉ old.map Prod.fst)
    (derivation : PaperContinuationTyped declarations old environment continuation responseType resultType) :
    PaperContinuationTyped declarations ((identity, newType) :: old) environment continuation responseType resultType := by
  exact derivation.graphWeaken (GraphLookupPreserved.freshCons fresh)

end YulangClosure.PaperTypes
