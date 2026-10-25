import YulangClosure.PaperExecutionGraphWeakening

/-! R28: simultaneous term substitution for the six represented judgments.
The partial public operations reject every omitted raw constructor. This is not
full-paper substitution, recursive allocation, heap typing, or guardedness. -/
namespace YulangClosure.PaperTypes

def liftTermRenaming (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => f n + 1

def liftTermRenamingN : Nat → (Nat → Nat) → Nat → Nat
  | 0, f => f
  | n + 1, f => liftTermRenaming (liftTermRenamingN n f)

private theorem recordValueSize (field : Label × Presence × Value) :
    sizeOf field.2.2 ≤ sizeOf field := by
  rcases field with ⟨a,b,c⟩
  simp +arith

mutual
  def renameTermValue (f : Nat → Nat) : Value → Value
    | .variable n => .variable (f n)
    | .graphReference n => .graphReference n
    | .literal l => .literal l
    | .tuple vs => .tuple (vs.attach.map fun ⟨v, hv⟩ => renameTermValue f v)
    | .sequence vs => .sequence (vs.attach.map fun ⟨v, hv⟩ => renameTermValue f v)
    | .record fs => .record (fs.attach.map fun ⟨x,hv⟩ => (x.1,x.2.1,renameTermValue f x.2.2))
    | .lambda m p n b => .lambda m p n (renameTermComputation (liftTermRenaming f) b)
    | .delay b => .delay (renameTermComputation f b)
    | .wrap v a r => .wrap (renameTermValue f v)
        (renameTermComputation (liftTermRenaming f) a) (renameTermComputation (liftTermRenaming f) r)
    | .typeAbstraction v => .typeAbstraction (renameTermValue f v)
    | .typeApplication v a => .typeApplication (renameTermValue f v) a
    | .injectLeft v => .injectLeft (renameTermValue f v)
    | .injectRight v => .injectRight (renameTermValue f v)
    | .both v => .both (renameTermValue f v)
    | .roll v => .roll (renameTermValue f v)
    | .topView v => .topView (renameTermValue f v)
    | .view m v => .view m (renameTermValue f v)
    | .continuation os n b => .continuation os n (renameTermComputation (liftTermRenaming f) b)
    | v => v
  termination_by v => sizeOf v
  decreasing_by all_goals
    first
    | have hs := List.sizeOf_lt_of_mem hv
      have hp := recordValueSize x
      simp +arith at hs hp ⊢ <;> omega
    | have hs := List.sizeOf_lt_of_mem hv
      simp +arith at hs ⊢ <;> omega
    | with_reducible decreasing_trivial

  def renameTermComputation (f : Nat → Nat) : Computation → Computation
    | .ret v => .ret (renameTermValue f v)
    | .letE a b => .letE (renameTermComputation f a) (renameTermComputation (liftTermRenaming f) b)
    | .force v => .force (renameTermValue f v)
    | .call a b => .call (renameTermValue f a) (renameTermValue f b)
    | .resume a b => .resume (renameTermValue f a) (renameTermValue f b)
    | .split v ns b => .split (renameTermValue f v) ns (renameTermComputation (liftTermRenamingN ns.length f) b)
    | .field v l => .field (renameTermValue f v) l
    | .lookup v l => .lookup (renameTermValue f v) l
    | .unroll v => .unroll (renameTermValue f v)
    | .unionCase v ln l rn r => .unionCase (renameTermValue f v) ln
        (renameTermComputation (liftTermRenaming f) l) rn (renameTermComputation (liftTermRenaming f) r)
    | .perform op ts v => .perform op ts (renameTermValue f v)
    | .template n ts vs => .template n ts (vs.attach.map fun ⟨v,hv⟩ => renameTermValue f v)
    | .request op p k => .request op (renameTermValue f p) (renameTermValue f k)
    | .fail r => .fail r
    | c => c
  termination_by c => sizeOf c
  decreasing_by all_goals
    first
    | have hs := List.sizeOf_lt_of_mem hv
      simp +arith at hs ⊢ <;> omega
    | with_reducible decreasing_trivial
end

def TermRenamingTyped (source target : TypeEnvironment) (f : Nat → Nat) : Prop :=
  ∀ n a, lookupTypeEnvironment source n = some a → lookupTypeEnvironment target (f n) = some a

theorem TermRenamingTyped.lift {source target f} (h : TermRenamingTyped source target f) (a : Ty) :
    TermRenamingTyped (a :: source) (a :: target) (liftTermRenaming f) := by
  intro n b hn
  cases n with
  | zero => simpa [lookupTypeEnvironment, liftTermRenaming] using hn
  | succ n => exact h n b hn

theorem TermRenamingTyped.liftN {source target f} (h : TermRenamingTyped source target f) (as : List Ty) :
    TermRenamingTyped (extendTupleEnvironment as source) (extendTupleEnvironment as target)
      (liftTermRenamingN as.length f) := by
  have aux : ∀ boundTypes : List Ty,
      TermRenamingTyped (boundTypes ++ source) (boundTypes ++ target) (liftTermRenamingN boundTypes.length f) := by
    intro boundTypes
    induction boundTypes with
    | nil => exact h
    | cons a rest ih => exact ih.lift a
  simpa only [extendTupleEnvironment, List.length_reverse] using aux as.reverse

theorem TermRenamingTyped.typeShift {source target f} (h : TermRenamingTyped source target f) :
    TermRenamingTyped (mapTypeEnvironment shiftTypeSubstitution source)
      (mapTypeEnvironment shiftTypeSubstitution target) f := by
  intro n a hn
  rw [lookupTypeEnvironment_subst] at hn ⊢
  cases he : lookupTypeEnvironment source n with
  | none => simp [he] at hn
  | some b =>
      rw [h n b he]
      simpa [he] using hn

private theorem renameRecordLabels (f : Nat → Nat) (fs : List (Label × Presence × Value)) :
    ((fs.map fun x => (x.1,x.2.1,renameTermValue f x.2.2)).map Prod.fst) = fs.map Prod.fst := by
  simp only [List.map_map, Function.comp_def]

private theorem renameTermValue_record_eq (f : Nat → Nat) (fields : List (Label × Presence × Value)) :
    renameTermValue f (.record fields) =
      .record (fields.map fun x => (x.1,x.2.1,renameTermValue f x.2.2)) := by
  simp only [renameTermValue]
  exact congrArg Value.record (List.attach_map_val (l := fields)
    (f := fun x : Label × Presence × Value => (x.1,x.2.1,renameTermValue f x.2.2)))

theorem PaperValueTyped.termRename {declarations : DeclarationTable} {graphTypes : GraphEnvironment}
    {environment target : TypeEnvironment} {value : Value} {ty : Ty} {f : Nat → Nat}
    (h : TermRenamingTyped environment target f)
    (derivation : PaperValueTyped declarations graphTypes environment value ty) :
    PaperValueTyped declarations graphTypes target (renameTermValue f value) ty := by
  exact PaperValueTyped.rec
    (motive_1 := fun declarations graphTypes environment values types _ =>
      ∀ target f, TermRenamingTyped environment target f → ValuesTyped declarations graphTypes target (values.map (renameTermValue f)) types)
    (motive_2 := fun declarations graphTypes environment values ty _ =>
      ∀ target f, TermRenamingTyped environment target f → ValuesAllTyped declarations graphTypes target (values.map (renameTermValue f)) ty)
    (motive_3 := fun declarations graphTypes environment fields ty _ =>
      ∀ target f, TermRenamingTyped environment target f → RecordPayloadsTyped declarations graphTypes target (fields.map fun x => (x.1,x.2.1,renameTermValue f x.2.2)) ty)
    (motive_4 := fun declarations graphTypes environment value ty _ =>
      ∀ target f, TermRenamingTyped environment target f → PaperValueTyped declarations graphTypes target (renameTermValue f value) ty)
    (motive_5 := fun declarations graphTypes environment computation ty _ =>
      ∀ target f, TermRenamingTyped environment target f → PaperComputationTyped declarations graphTypes target (renameTermComputation f computation) ty)
    (motive_6 := fun declarations graphTypes environment continuation response result _ =>
      ∀ target f, TermRenamingTyped environment target f → PaperContinuationTyped declarations graphTypes target (renameTermValue f continuation) response result)
    (by intro declarations graphTypes environment target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using ValuesTyped.nil)
    (by intro declarations graphTypes environment value values ty types hvalue hvalues ihValue ihValues target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using ValuesTyped.cons (ihValue target f h) (ihValues target f h))
    (by intro declarations graphTypes environment ty target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using ValuesAllTyped.nil)
    (by intro declarations graphTypes environment value values ty hvalue hvalues ihValue ihValues target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using ValuesAllTyped.cons (ihValue target f h) (ihValues target f h))
    (by intro declarations graphTypes environment recordType target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using RecordPayloadsTyped.nil)
    (by intro declarations graphTypes label tag value fields recordType presence fieldType environment hfield hvalue hfields ihValue ihFields target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using RecordPayloadsTyped.cons hfield (ihValue target f h) (ihFields target f h))
    (by intro declarations graphTypes environment index ty lookup target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.variable (h index ty lookup))
    (by intro declarations graphTypes environment identity ty lookup target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.graphReference lookup)
    (by intro declarations graphTypes environment literal target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.literal)
    (by intro declarations graphTypes environment values types hvalues ihValues target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.tuple (ihValues target f h))
    (by intro declarations graphTypes environment values elementType hvalues ihValues target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.sequence (ihValues target f h))
    (by intro declarations graphTypes environment fields recordType labels required shape unique allRequired hfields ihFields target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.record shape (by simpa only [renameRecordLabels] using unique) (by simpa only [renameRecordLabels] using allRequired) (ihFields target f h))
    (by intro declarations graphTypes environment body resultType hbody ihBody target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.delay (ihBody target f h))
    (by intro declarations graphTypes environment profile parameter body inputType outputType hbody ihBody target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.valueLambda (ihBody _ _ (h.lift _)))
    (by intro declarations graphTypes environment profile parameter body inputType outputType hbody ihBody target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.computationLambda (ihBody _ _ (h.lift _)))
    (by intro declarations graphTypes environment function argumentAdapter resultAdapter inputType outputType adaptedInputType adaptedOutputType hfunction hargument hresult ihFunction ihArgument ihResult target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.wrap (ihFunction target f h) (ihArgument _ _ (h.lift _)) (ihResult _ _ (h.lift _)))
    (by intro declarations graphTypes environment value left right hvalue ihValue target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.injectLeft (ihValue target f h))
    (by intro declarations graphTypes environment value left right hvalue ihValue target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.injectRight (ihValue target f h))
    (by intro declarations graphTypes environment value left right hleft hright ihLeft ihRight target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.both (ihLeft target f h) (ihRight target f h))
    (by intro declarations graphTypes environment value ty hvalue ihValue target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.topView (ihValue target f h))
    (by intro declarations graphTypes environment metadata value ty hvalue ihValue target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.view (ihValue target f h))
    (by intro declarations graphTypes environment owners binder body responseType resultType hcontinuation ihContinuation target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.continuation (by simpa only [renameTermValue] using ihContinuation target f h))
    (by intro declarations graphTypes environment body bodyType hbody ihBody target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.typeAbstraction (ihBody _ f h.typeShift))
    (by intro declarations graphTypes environment function body argument hfunction ihFunction target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.typeApplication (ihFunction target f h))
    (by intro declarations graphTypes environment value body hvalue ihValue target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.roll (ihValue target f h))
    (by intro declarations graphTypes environment value ty hvalue ihValue target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.ret (ihValue target f h))
    (by intro declarations graphTypes environment first body firstType resultType hfirst hbody ihFirst ihBody target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.letE (ihFirst target f h) (ihBody _ _ (h.lift _)))
    (by intro declarations graphTypes environment thunk resultType hthunk ihThunk target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.force (ihThunk target f h))
    (by intro declarations graphTypes environment function thunk argumentType resultType hfunction hthunk ihFunction ihThunk target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.call (ihFunction target f h) (ihThunk target f h))
    (by intro declarations graphTypes environment tuple binders body types resultType arity htuple hbody ihTuple ihBody target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons, arity] using PaperComputationTyped.split arity (ihTuple target f h) (ihBody _ _ (h.liftN types)))
    (by intro declarations graphTypes environment value leftBinder left rightBinder right leftType rightType resultType hvalue hleft hright ihValue ihLeft ihRight target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.unionCase (ihValue target f h) (ihLeft _ _ (h.lift _)) (ihRight _ _ (h.lift _)))
    (by intro declarations graphTypes environment value recordType label fieldType hvalue hfield ihValue target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.field (ihValue target f h) hfield)
    (by intro declarations graphTypes environment value recordType label presence fieldType hvalue hfield ihValue target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.lookup (ihValue target f h) hfield)
    (by intro declarations graphTypes environment operation arguments payload declaration resolved arity payloadTyping ihPayload target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.perform resolved arity (ihPayload target f h))
    (by intro declarations graphTypes environment opInstance payload continuation declaration arguments resultType resolved arity instanceEq payloadTyping continuationTyping ihPayload ihContinuation target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.request resolved arity instanceEq (ihPayload target f h) (ihContinuation target f h))
    (by intro declarations graphTypes environment continuation response responseType resultType hcontinuation hresponse ihContinuation ihResponse target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.resume (ihContinuation target f h) (ihResponse target f h))
    (by intro declarations graphTypes environment value body hvalue ihValue target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.unroll (ihValue target f h))
    (by intro declarations graphTypes environment identity typeArguments arguments typeArity formals result body resolved arity argumentsTyping ihArguments target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.template resolved arity (ihArguments target f h))
    (by intro declarations graphTypes environment reason ty target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.fail)
    (by intro declarations graphTypes environment owners binder body responseType resultType hbody ihBody target f h
        simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperContinuationTyped.continuation (ihBody _ _ (h.lift _)))
    derivation target f h


/-- The bound variable is fixed; all free replacements move across one term binder. -/
def liftTermSubstitution (rho : Nat → Value) : Nat → Value
  | 0 => .variable 0
  | n + 1 => renameTermValue Nat.succ (rho n)

def liftTermSubstitutionN : Nat → (Nat → Value) → Nat → Value
  | 0, rho => rho
  | n + 1, rho => liftTermSubstitution (liftTermSubstitutionN n rho)

/-- A type binder shifts every replacement with the shared type substitution. -/
def shiftTermSubstitution (rho : Nat → Value) (n : Nat) : Value :=
  mapPaperValue shiftTypeSubstitution (rho n)

mutual
  def replaceTermValue (rho : Nat → Value) : Value → Value
    | .variable n => rho n
    | .graphReference n => .graphReference n
    | .literal l => .literal l
    | .tuple vs => .tuple (vs.attach.map fun ⟨v, hv⟩ => replaceTermValue rho v)
    | .sequence vs => .sequence (vs.attach.map fun ⟨v, hv⟩ => replaceTermValue rho v)
    | .record fs => .record (fs.attach.map fun ⟨x,hv⟩ => (x.1,x.2.1,replaceTermValue rho x.2.2))
    | .lambda m p n b => .lambda m p n (replaceTermComputation (liftTermSubstitution rho) b)
    | .delay b => .delay (replaceTermComputation rho b)
    | .wrap v a r => .wrap (replaceTermValue rho v)
        (replaceTermComputation (liftTermSubstitution rho) a) (replaceTermComputation (liftTermSubstitution rho) r)
    | .typeAbstraction v => .typeAbstraction (replaceTermValue (shiftTermSubstitution rho) v)
    | .typeApplication v a => .typeApplication (replaceTermValue rho v) a
    | .injectLeft v => .injectLeft (replaceTermValue rho v)
    | .injectRight v => .injectRight (replaceTermValue rho v)
    | .both v => .both (replaceTermValue rho v)
    | .roll v => .roll (replaceTermValue rho v)
    | .topView v => .topView (replaceTermValue rho v)
    | .view m v => .view m (replaceTermValue rho v)
    | .continuation os n b => .continuation os n (replaceTermComputation (liftTermSubstitution rho) b)
    | v => v
  termination_by v => sizeOf v
  decreasing_by all_goals
    first
    | have hs := List.sizeOf_lt_of_mem hv
      have hp := recordValueSize x
      simp +arith at hs hp ⊢ <;> omega
    | have hs := List.sizeOf_lt_of_mem hv
      simp +arith at hs ⊢ <;> omega
    | with_reducible decreasing_trivial

  def replaceTermComputation (rho : Nat → Value) : Computation → Computation
    | .ret v => .ret (replaceTermValue rho v)
    | .letE a b => .letE (replaceTermComputation rho a) (replaceTermComputation (liftTermSubstitution rho) b)
    | .force v => .force (replaceTermValue rho v)
    | .call a b => .call (replaceTermValue rho a) (replaceTermValue rho b)
    | .resume a b => .resume (replaceTermValue rho a) (replaceTermValue rho b)
    | .split v ns b => .split (replaceTermValue rho v) ns (replaceTermComputation (liftTermSubstitutionN ns.length rho) b)
    | .field v l => .field (replaceTermValue rho v) l
    | .lookup v l => .lookup (replaceTermValue rho v) l
    | .unroll v => .unroll (replaceTermValue rho v)
    | .unionCase v ln l rn r => .unionCase (replaceTermValue rho v) ln
        (replaceTermComputation (liftTermSubstitution rho) l) rn (replaceTermComputation (liftTermSubstitution rho) r)
    | .perform op ts v => .perform op ts (replaceTermValue rho v)
    | .template n ts vs => .template n ts (vs.attach.map fun ⟨v,hv⟩ => replaceTermValue rho v)
    | .request op p k => .request op (replaceTermValue rho p) (replaceTermValue rho k)
    | .fail r => .fail r
    | c => c
  termination_by c => sizeOf c
  decreasing_by all_goals
    first
    | have hs := List.sizeOf_lt_of_mem hv
      simp +arith at hs ⊢ <;> omega
    | with_reducible decreasing_trivial
end

def TermSubstitutionTyped (declarations : DeclarationTable) (graphTypes : GraphEnvironment)
    (source target : TypeEnvironment) (rho : Nat → Value) : Prop :=
  ∀ n a, lookupTypeEnvironment source n = some a →
    PaperValueTyped declarations graphTypes target (rho n) a

theorem TermSubstitutionTyped.lift {declarations graphTypes source target rho}
    (h : TermSubstitutionTyped declarations graphTypes source target rho) (a : Ty) :
    TermSubstitutionTyped declarations graphTypes (a :: source) (a :: target) (liftTermSubstitution rho) := by
  intro n b hn
  cases n with
  | zero =>
      have hab : a = b := Option.some.inj hn
      subst b
      exact .variable rfl
  | succ n =>
      exact (h n b hn).termRename (fun i t hi => hi)

theorem TermSubstitutionTyped.liftN {declarations graphTypes source target rho}
    (h : TermSubstitutionTyped declarations graphTypes source target rho) (as : List Ty) :
    TermSubstitutionTyped declarations graphTypes (extendTupleEnvironment as source)
      (extendTupleEnvironment as target) (liftTermSubstitutionN as.length rho) := by
  have aux : ∀ boundTypes : List Ty,
      TermSubstitutionTyped declarations graphTypes (boundTypes ++ source) (boundTypes ++ target)
        (liftTermSubstitutionN boundTypes.length rho) := by
    intro boundTypes
    induction boundTypes with
    | nil => exact h
    | cons a rest ih => exact ih.lift a
  simpa only [extendTupleEnvironment, List.length_reverse] using aux as.reverse

theorem TermSubstitutionTyped.typeShift {declarations graphTypes source target rho}
    (h : TermSubstitutionTyped declarations graphTypes source target rho) :
    TermSubstitutionTyped (mapDeclarationTable shiftTypeSubstitution declarations)
      (mapGraphEnvironment shiftTypeSubstitution graphTypes)
      (mapTypeEnvironment shiftTypeSubstitution source) (mapTypeEnvironment shiftTypeSubstitution target)
      (shiftTermSubstitution rho) := by
  intro n a hn
  rw [lookupTypeEnvironment_subst] at hn
  cases he : lookupTypeEnvironment source n with
  | none => simp [he] at hn
  | some b =>
      have hab : subst shiftTypeSubstitution b = a := by simpa [he] using hn
      subst a
      exact (h n b he).subst_explicit shiftTypeSubstitution

private theorem replaceRecordLabels (rho : Nat → Value) (fs : List (Label × Presence × Value)) :
    ((fs.map fun x => (x.1,x.2.1,replaceTermValue rho x.2.2)).map Prod.fst) = fs.map Prod.fst := by
  simp only [List.map_map, Function.comp_def]

private theorem replaceTermValue_record_eq (rho : Nat → Value) (fields : List (Label × Presence × Value)) :
    replaceTermValue rho (.record fields) =
      .record (fields.map fun x => (x.1,x.2.1,replaceTermValue rho x.2.2)) := by
  simp only [replaceTermValue]
  exact congrArg Value.record (List.attach_map_val (l := fields)
    (f := fun x : Label × Presence × Value => (x.1,x.2.1,replaceTermValue rho x.2.2)))

theorem PaperValueTyped.termReplace {declarations : DeclarationTable} {graphTypes : GraphEnvironment}
    {environment target : TypeEnvironment} {value : Value} {ty : Ty} {rho : Nat → Value}
    (h : TermSubstitutionTyped declarations graphTypes environment target rho)
    (derivation : PaperValueTyped declarations graphTypes environment value ty) :
    PaperValueTyped declarations graphTypes target (replaceTermValue rho value) ty := by
  exact PaperValueTyped.rec
    (motive_1 := fun declarations graphTypes environment values types _ =>
      ∀ target rho, TermSubstitutionTyped declarations graphTypes environment target rho → ValuesTyped declarations graphTypes target (values.map (replaceTermValue rho)) types)
    (motive_2 := fun declarations graphTypes environment values ty _ =>
      ∀ target rho, TermSubstitutionTyped declarations graphTypes environment target rho → ValuesAllTyped declarations graphTypes target (values.map (replaceTermValue rho)) ty)
    (motive_3 := fun declarations graphTypes environment fields ty _ =>
      ∀ target rho, TermSubstitutionTyped declarations graphTypes environment target rho → RecordPayloadsTyped declarations graphTypes target (fields.map fun x => (x.1,x.2.1,replaceTermValue rho x.2.2)) ty)
    (motive_4 := fun declarations graphTypes environment value ty _ =>
      ∀ target rho, TermSubstitutionTyped declarations graphTypes environment target rho → PaperValueTyped declarations graphTypes target (replaceTermValue rho value) ty)
    (motive_5 := fun declarations graphTypes environment computation ty _ =>
      ∀ target rho, TermSubstitutionTyped declarations graphTypes environment target rho → PaperComputationTyped declarations graphTypes target (replaceTermComputation rho computation) ty)
    (motive_6 := fun declarations graphTypes environment continuation response result _ =>
      ∀ target rho, TermSubstitutionTyped declarations graphTypes environment target rho → PaperContinuationTyped declarations graphTypes target (replaceTermValue rho continuation) response result)
    (by intro declarations graphTypes environment target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using ValuesTyped.nil)
    (by intro declarations graphTypes environment value values ty types hvalue hvalues ihValue ihValues target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using ValuesTyped.cons (ihValue target rho h) (ihValues target rho h))
    (by intro declarations graphTypes environment ty target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using ValuesAllTyped.nil)
    (by intro declarations graphTypes environment value values ty hvalue hvalues ihValue ihValues target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using ValuesAllTyped.cons (ihValue target rho h) (ihValues target rho h))
    (by intro declarations graphTypes environment recordType target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using RecordPayloadsTyped.nil)
    (by intro declarations graphTypes label tag value fields recordType presence fieldType environment hfield hvalue hfields ihValue ihFields target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using RecordPayloadsTyped.cons hfield (ihValue target rho h) (ihFields target rho h))
    (by intro declarations graphTypes environment index ty lookup target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using (h index ty lookup))
    (by intro declarations graphTypes environment identity ty lookup target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.graphReference lookup)
    (by intro declarations graphTypes environment literal target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.literal)
    (by intro declarations graphTypes environment values types hvalues ihValues target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.tuple (ihValues target rho h))
    (by intro declarations graphTypes environment values elementType hvalues ihValues target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.sequence (ihValues target rho h))
    (by intro declarations graphTypes environment fields recordType labels required shape unique allRequired hfields ihFields target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.record shape (by simpa only [replaceRecordLabels] using unique) (by simpa only [replaceRecordLabels] using allRequired) (ihFields target rho h))
    (by intro declarations graphTypes environment body resultType hbody ihBody target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.delay (ihBody target rho h))
    (by intro declarations graphTypes environment profile parameter body inputType outputType hbody ihBody target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.valueLambda (ihBody _ _ (h.lift _)))
    (by intro declarations graphTypes environment profile parameter body inputType outputType hbody ihBody target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.computationLambda (ihBody _ _ (h.lift _)))
    (by intro declarations graphTypes environment function argumentAdapter resultAdapter inputType outputType adaptedInputType adaptedOutputType hfunction hargument hresult ihFunction ihArgument ihResult target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.wrap (ihFunction target rho h) (ihArgument _ _ (h.lift _)) (ihResult _ _ (h.lift _)))
    (by intro declarations graphTypes environment value left right hvalue ihValue target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.injectLeft (ihValue target rho h))
    (by intro declarations graphTypes environment value left right hvalue ihValue target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.injectRight (ihValue target rho h))
    (by intro declarations graphTypes environment value left right hleft hright ihLeft ihRight target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.both (ihLeft target rho h) (ihRight target rho h))
    (by intro declarations graphTypes environment value ty hvalue ihValue target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.topView (ihValue target rho h))
    (by intro declarations graphTypes environment metadata value ty hvalue ihValue target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.view (ihValue target rho h))
    (by intro declarations graphTypes environment owners binder body responseType resultType hcontinuation ihContinuation target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.continuation (by simpa only [replaceTermValue] using ihContinuation target rho h))
    (by intro declarations graphTypes environment body bodyType hbody ihBody target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.typeAbstraction (ihBody _ (shiftTermSubstitution rho) h.typeShift))
    (by intro declarations graphTypes environment function body argument hfunction ihFunction target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.typeApplication (ihFunction target rho h))
    (by intro declarations graphTypes environment value body hvalue ihValue target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperValueTyped.roll (ihValue target rho h))
    (by intro declarations graphTypes environment value ty hvalue ihValue target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.ret (ihValue target rho h))
    (by intro declarations graphTypes environment first body firstType resultType hfirst hbody ihFirst ihBody target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.letE (ihFirst target rho h) (ihBody _ _ (h.lift _)))
    (by intro declarations graphTypes environment thunk resultType hthunk ihThunk target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.force (ihThunk target rho h))
    (by intro declarations graphTypes environment function thunk argumentType resultType hfunction hthunk ihFunction ihThunk target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.call (ihFunction target rho h) (ihThunk target rho h))
    (by intro declarations graphTypes environment tuple binders body types resultType arity htuple hbody ihTuple ihBody target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons, arity] using PaperComputationTyped.split arity (ihTuple target rho h) (ihBody _ _ (h.liftN types)))
    (by intro declarations graphTypes environment value leftBinder left rightBinder right leftType rightType resultType hvalue hleft hright ihValue ihLeft ihRight target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.unionCase (ihValue target rho h) (ihLeft _ _ (h.lift _)) (ihRight _ _ (h.lift _)))
    (by intro declarations graphTypes environment value recordType label fieldType hvalue hfield ihValue target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.field (ihValue target rho h) hfield)
    (by intro declarations graphTypes environment value recordType label presence fieldType hvalue hfield ihValue target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.lookup (ihValue target rho h) hfield)
    (by intro declarations graphTypes environment operation arguments payload declaration resolved arity payloadTyping ihPayload target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.perform resolved arity (ihPayload target rho h))
    (by intro declarations graphTypes environment opInstance payload continuation declaration arguments resultType resolved arity instanceEq payloadTyping continuationTyping ihPayload ihContinuation target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.request resolved arity instanceEq (ihPayload target rho h) (ihContinuation target rho h))
    (by intro declarations graphTypes environment continuation response responseType resultType hcontinuation hresponse ihContinuation ihResponse target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.resume (ihContinuation target rho h) (ihResponse target rho h))
    (by intro declarations graphTypes environment value body hvalue ihValue target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.unroll (ihValue target rho h))
    (by intro declarations graphTypes environment identity typeArguments arguments typeArity formals result body resolved arity argumentsTyping ihArguments target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.template resolved arity (ihArguments target rho h))
    (by intro declarations graphTypes environment reason ty target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.fail)
    (by intro declarations graphTypes environment owners binder body responseType resultType hbody ihBody target rho h
        simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperContinuationTyped.continuation (ihBody _ _ (h.lift _)))
    derivation target rho h


mutual
  def supportedTermValue : Value → Bool
    | .variable _ | .graphReference _ | .literal _ => true
    | .tuple vs | .sequence vs => vs.attach.all fun ⟨v,hv⟩ => supportedTermValue v
    | .record fs => fs.attach.all fun ⟨x,hv⟩ => supportedTermValue x.2.2
    | .lambda _ _ _ b | .delay b | .continuation _ _ b => supportedTermComputation b
    | .wrap v a r => supportedTermValue v && supportedTermComputation a && supportedTermComputation r
    | .typeAbstraction v | .typeApplication v _ | .injectLeft v | .injectRight v
    | .both v | .roll v | .topView v | .view _ v => supportedTermValue v
    | _ => false
  termination_by v => sizeOf v
  decreasing_by all_goals
    first
    | have hs := List.sizeOf_lt_of_mem hv
      have hp := recordValueSize x
      simp +arith at hs hp ⊢ <;> omega
    | have hs := List.sizeOf_lt_of_mem hv
      simp +arith at hs ⊢ <;> omega
    | with_reducible decreasing_trivial

  def supportedTermComputation : Computation → Bool
    | .ret v | .force v | .field v _ | .lookup v _ | .unroll v | .perform _ _ v => supportedTermValue v
    | .call a b | .resume a b | .request _ a b => supportedTermValue a && supportedTermValue b
    | .letE a b => supportedTermComputation a && supportedTermComputation b
    | .split v _ b => supportedTermValue v && supportedTermComputation b
    | .unionCase v _ l _ r => supportedTermValue v && supportedTermComputation l && supportedTermComputation r
    | .template _ _ vs => vs.attach.all fun ⟨v,hv⟩ => supportedTermValue v
    | .fail _ => true
    | _ => false
  termination_by c => sizeOf c
  decreasing_by all_goals
    first
    | have hs := List.sizeOf_lt_of_mem hv
      simp +arith at hs ⊢ <;> omega
    | with_reducible decreasing_trivial
end

theorem PaperValueTyped.termSupported {declarations graphTypes environment value ty}
    (derivation : PaperValueTyped declarations graphTypes environment value ty) :
    supportedTermValue value = true := by
  exact PaperValueTyped.rec
    (motive_1 := fun _ _ _ values _ _ => values.all supportedTermValue = true)
    (motive_2 := fun _ _ _ values _ _ => values.all supportedTermValue = true)
    (motive_3 := fun _ _ _ fields _ _ => fields.all (fun x => supportedTermValue x.2.2) = true)
    (motive_4 := fun _ _ _ value _ _ => supportedTermValue value = true)
    (motive_5 := fun _ _ _ computation _ _ => supportedTermComputation computation = true)
    (motive_6 := fun _ _ _ continuation _ _ _ => supportedTermValue continuation = true)
    (by intro declarations graphTypes environment
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment value values ty types hvalue hvalues ihValue ihValues
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment ty
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment value values ty hvalue hvalues ihValue ihValues
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment recordType
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes label tag value fields recordType presence fieldType environment hfield hvalue hfields ihValue ihFields
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment index ty lookup
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment identity ty lookup
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment literal
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment values types hvalues ihValues
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment values elementType hvalues ihValues
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment fields recordType labels required shape unique allRequired hfields ihFields
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment body resultType hbody ihBody
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment profile parameter body inputType outputType hbody ihBody
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment profile parameter body inputType outputType hbody ihBody
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment function argumentAdapter resultAdapter inputType outputType adaptedInputType adaptedOutputType hfunction hargument hresult ihFunction ihArgument ihResult
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment value left right hvalue ihValue
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment value left right hvalue ihValue
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment value left right hleft hright ihLeft ihRight
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment value ty hvalue ihValue
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment metadata value ty hvalue ihValue
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment owners binder body responseType resultType hcontinuation ihContinuation
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment body bodyType hbody ihBody
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment function body argument hfunction ihFunction
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment value body hvalue ihValue
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment value ty hvalue ihValue
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment first body firstType resultType hfirst hbody ihFirst ihBody
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment thunk resultType hthunk ihThunk
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment function thunk argumentType resultType hfunction hthunk ihFunction ihThunk
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment tuple binders body types resultType arity htuple hbody ihTuple ihBody
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment value leftBinder left rightBinder right leftType rightType resultType hvalue hleft hright ihValue ihLeft ihRight
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment value recordType label fieldType hvalue hfield ihValue
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment value recordType label presence fieldType hvalue hfield ihValue
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment operation arguments payload declaration resolved arity payloadTyping ihPayload
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment opInstance payload continuation declaration arguments resultType resolved arity instanceEq payloadTyping continuationTyping ihPayload ihContinuation
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment continuation response responseType resultType hcontinuation hresponse ihContinuation ihResponse
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment value body hvalue ihValue
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment identity typeArguments arguments typeArity formals result body resolved arity argumentsTyping ihArguments
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment reason ty
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    (by intro declarations graphTypes environment owners binder body responseType resultType hbody ihBody
        simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
        all_goals assumption)
    derivation


theorem ValuesTyped.termReplace {d g e t vs ts rho}
    (h : TermSubstitutionTyped d g e t rho) (hv : ValuesTyped d g e vs ts) :
    ValuesTyped d g t (vs.map (replaceTermValue rho)) ts := by
  induction vs generalizing ts with
  | nil => cases hv; exact .nil
  | cons v vs ih => cases hv with
    | cons head tail => exact .cons (head.termReplace h) (ih tail)

theorem ValuesAllTyped.termReplace {d g e t vs a rho}
    (h : TermSubstitutionTyped d g e t rho) (hv : ValuesAllTyped d g e vs a) :
    ValuesAllTyped d g t (vs.map (replaceTermValue rho)) a := by
  induction vs with
  | nil => cases hv; exact .nil
  | cons v vs ih => cases hv with
    | cons head tail => exact .cons (head.termReplace h) (ih tail)

theorem RecordPayloadsTyped.termReplace {d g e t fs a rho}
    (h : TermSubstitutionTyped d g e t rho) (hv : RecordPayloadsTyped d g e fs a) :
    RecordPayloadsTyped d g t (fs.map fun x => (x.1,x.2.1,replaceTermValue rho x.2.2)) a := by
  induction fs with
  | nil => cases hv; exact .nil
  | cons v vs ih => cases hv with
    | cons field head tail => exact .cons field (head.termReplace h) (ih tail)

theorem PaperComputationTyped.termReplace {d g e t c a rho}
    (h : TermSubstitutionTyped d g e t rho) (hc : PaperComputationTyped d g e c a) :
    PaperComputationTyped d g t (replaceTermComputation rho c) a := by
  have ht := (PaperValueTyped.delay hc).termReplace h
  simp only [replaceTermValue] at ht
  cases ht with
  | delay body => exact body

theorem PaperContinuationTyped.termReplace {d g e t v a b rho}
    (h : TermSubstitutionTyped d g e t rho) (hv : PaperContinuationTyped d g e v a b) :
    PaperContinuationTyped d g t (replaceTermValue rho v) a b := by
  cases hv with
  | continuation body => simpa only [replaceTermValue] using
      PaperContinuationTyped.continuation (body.termReplace (h.lift _))

theorem ValuesTyped.termSupported {d g e vs ts} (hv : ValuesTyped d g e vs ts) :
    vs.all supportedTermValue = true := by
  induction vs generalizing ts with
  | nil => rfl
  | cons v vs ih => cases hv with
    | cons head tail => simp [head.termSupported, ih tail]

theorem ValuesAllTyped.termSupported {d g e vs a} (hv : ValuesAllTyped d g e vs a) :
    vs.all supportedTermValue = true := by
  induction vs with
  | nil => rfl
  | cons v vs ih => cases hv with
    | cons head tail => simp [head.termSupported, ih tail]

theorem RecordPayloadsTyped.termSupported {d g e fs a} (hv : RecordPayloadsTyped d g e fs a) :
    fs.all (fun x => supportedTermValue x.2.2) = true := by
  induction fs with
  | nil => rfl
  | cons v vs ih => cases hv with
    | cons field head tail => simp [head.termSupported, ih tail]

theorem PaperComputationTyped.termSupported {d g e c a} (hc : PaperComputationTyped d g e c a) :
    supportedTermComputation c = true := by
  simpa only [supportedTermValue] using (PaperValueTyped.delay hc).termSupported

theorem PaperContinuationTyped.termSupported {d g e v a b} (hv : PaperContinuationTyped d g e v a b) :
    supportedTermValue v = true := by
  cases hv with
  | continuation body => simpa only [supportedTermValue] using body.termSupported

/-- This check inspects syntax only. Omitted constructors fail, including nested ones. -/
def termSubstituteValue (rho : Nat → Value) (v : Value) : Option Value :=
  if supportedTermValue v then some (replaceTermValue rho v) else none

def termSubstituteComputation (rho : Nat → Value) (c : Computation) : Option Computation :=
  if supportedTermComputation c then some (replaceTermComputation rho c) else none

def termSubstituteValues (rho : Nat → Value) (vs : List Value) : Option (List Value) :=
  if vs.all supportedTermValue then some (vs.map (replaceTermValue rho)) else none

def termSubstituteFields (rho : Nat → Value) (fs : List (Label × Presence × Value)) :
    Option (List (Label × Presence × Value)) :=
  if fs.all (fun x => supportedTermValue x.2.2) then
    some (fs.map fun x => (x.1,x.2.1,replaceTermValue rho x.2.2)) else none

theorem PaperValueTyped.termSubstitute {d g e t v a rho}
    (h : TermSubstitutionTyped d g e t rho) (hv : PaperValueTyped d g e v a) :
    ∃ result, termSubstituteValue rho v = some result ∧ PaperValueTyped d g t result a := by
  refine ⟨_, ?_, hv.termReplace h⟩
  simp only [termSubstituteValue, hv.termSupported, Bool.true_eq, ↓reduceIte]

theorem ValuesTyped.termSubstitute {d g e t vs ts rho}
    (h : TermSubstitutionTyped d g e t rho) (hv : ValuesTyped d g e vs ts) :
    ∃ result, termSubstituteValues rho vs = some result ∧ ValuesTyped d g t result ts := by
  refine ⟨_, ?_, hv.termReplace h⟩
  simp only [termSubstituteValues, hv.termSupported, Bool.true_eq, ↓reduceIte]

theorem ValuesAllTyped.termSubstitute {d g e t vs a rho}
    (h : TermSubstitutionTyped d g e t rho) (hv : ValuesAllTyped d g e vs a) :
    ∃ result, termSubstituteValues rho vs = some result ∧ ValuesAllTyped d g t result a := by
  refine ⟨_, ?_, hv.termReplace h⟩
  simp only [termSubstituteValues, hv.termSupported, Bool.true_eq, ↓reduceIte]

theorem RecordPayloadsTyped.termSubstitute {d g e t fs a rho}
    (h : TermSubstitutionTyped d g e t rho) (hv : RecordPayloadsTyped d g e fs a) :
    ∃ result, termSubstituteFields rho fs = some result ∧ RecordPayloadsTyped d g t result a := by
  refine ⟨_, ?_, hv.termReplace h⟩
  simp only [termSubstituteFields, hv.termSupported, Bool.true_eq, ↓reduceIte]

theorem PaperComputationTyped.termSubstitute {d g e t c a rho}
    (h : TermSubstitutionTyped d g e t rho) (hv : PaperComputationTyped d g e c a) :
    ∃ result, termSubstituteComputation rho c = some result ∧ PaperComputationTyped d g t result a := by
  refine ⟨_, ?_, hv.termReplace h⟩
  simp only [termSubstituteComputation, hv.termSupported, Bool.true_eq, ↓reduceIte]

theorem PaperContinuationTyped.termSubstitute {d g e t v a b rho}
    (h : TermSubstitutionTyped d g e t rho) (hv : PaperContinuationTyped d g e v a b) :
    ∃ result, termSubstituteValue rho v = some result ∧ PaperContinuationTyped d g t result a b := by
  refine ⟨_, ?_, hv.termReplace h⟩
  simp only [termSubstituteValue, hv.termSupported, Bool.true_eq, ↓reduceIte]

theorem termSubstituteValue_success {rho v} (h : supportedTermValue v = true) :
    termSubstituteValue rho v = some (replaceTermValue rho v) := by
  simp [termSubstituteValue, h]

theorem termSubstituteValue_failure {rho v} (h : supportedTermValue v = false) :
    termSubstituteValue rho v = none := by
  simp [termSubstituteValue, h]

theorem unsupported_raw_falsifier (rho : Nat → Value) (n : Nat) (ts : List Ty) (vs : List Value)
    (handler : HandlerPlan) (c : Computation) :
    (termSubstituteValue rho (.variant n ts vs)).isSome = false ∧
    (termSubstituteValue rho (.nominal n ts vs)).isSome = false ∧
    (termSubstituteComputation rho (.recursive [] c)).isSome = false ∧
    (termSubstituteComputation rho (.handle c handler)).isSome = false := by
  simp [termSubstituteValue, termSubstituteComputation, supportedTermValue, supportedTermComputation]

theorem capture_avoiding_binder (profile : AdapterMetadata) :
    termSubstituteValue (fun _ => .variable 0)
      (.lambda .value profile 7 (.ret (.variable 1))) =
      some (.lambda .value profile 7 (.ret (.variable 1))) ∧
    termSubstituteValue (fun _ => .variable 0)
      (.continuation [] 8 (.ret (.variable 1))) =
      some (.continuation [] 8 (.ret (.variable 1))) := by
  simp [termSubstituteValue, supportedTermValue, supportedTermComputation, replaceTermValue,
    replaceTermComputation, liftTermSubstitution, renameTermValue]

def swapFormalReplacements : Nat → Value
  | 0 => .variable 1
  | 1 => .variable 0
  | n + 2 => .variable (n + 2)

theorem simultaneous_order_falsifier :
    termSubstituteValue swapFormalReplacements (.tuple [.variable 0, .variable 1]) =
      some (.tuple [.variable 1, .variable 0]) := by
  simp [termSubstituteValue, supportedTermValue, replaceTermValue, swapFormalReplacements]

theorem forall_replacement_shift (rho : Nat → Value) (n : Nat) :
    termSubstituteValue rho (.typeAbstraction (.variable n)) =
      some (.typeAbstraction (mapPaperValue shiftTypeSubstitution (rho n))) := by
  simp [termSubstituteValue, supportedTermValue, replaceTermValue, shiftTermSubstitution]


/-- Composition of simultaneous vectors substitutes each inner replacement once. -/
def composeTermSubstitution (outer inner : Nat → Value) (n : Nat) : Value :=
  replaceTermValue outer (inner n)

theorem TermSubstitutionTyped.compose {d g source middle target inner outer}
    (hi : TermSubstitutionTyped d g source middle inner)
    (ho : TermSubstitutionTyped d g middle target outer) :
    TermSubstitutionTyped d g source target (composeTermSubstitution outer inner) := by
  intro n a hn
  exact (hi n a hn).termReplace ho

theorem TermSubstitutionTyped.graphWeaken {d old new source target rho}
    (hp : GraphLookupPreserved old new) (h : TermSubstitutionTyped d old source target rho) :
    TermSubstitutionTyped d new source target rho := by
  intro n a hn
  exact (h n a hn).graphWeaken hp

/-- Formal order is explicitly de Bruijn order: head replaces index zero. -/
def graphFormalReplacements : List (Nat × Ty) → (Nat → Value) → Nat → Value
  | [], rho, n => rho n
  | (identity, _) :: _, _, 0 => .graphReference identity
  | _ :: rest, rho, n + 1 => graphFormalReplacements rest rho n

theorem graphFormalReplacements_typed {d old new source target rho}
    (formals : List (Nat × Ty)) (hp : GraphLookupPreserved old new)
    (hr : ∀ identity a, (identity,a) ∈ formals → lookupGraphEnvironment new identity = some a)
    (h : TermSubstitutionTyped d old source target rho) :
    TermSubstitutionTyped d new (formals.map Prod.snd ++ source) target
      (graphFormalReplacements formals rho) := by
  induction formals with
  | nil => exact h.graphWeaken hp
  | cons formal rest ih =>
      rcases formal with ⟨identity,a⟩
      intro n b hn
      cases n with
      | zero =>
          have hab : a = b := Option.some.inj hn
          subst b
          exact .graphReference (hr identity a (by simp))
      | succ n => exact ih (fun i t hit => hr i t (List.mem_cons_of_mem _ hit)) n b hn

/-- R27 transports this exact judgment and every tail replacement before substitution. -/
theorem PaperValueTyped.substituteFreshGraphFormals {d old new source target v a rho}
    (formals : List (Nat × Ty)) (hp : GraphLookupPreserved old new)
    (hr : ∀ identity a, (identity,a) ∈ formals → lookupGraphEnvironment new identity = some a)
    (h : TermSubstitutionTyped d old source target rho)
    (hv : PaperValueTyped d old (formals.map Prod.snd ++ source) v a) :
    ∃ result, termSubstituteValue (graphFormalReplacements formals rho) v = some result ∧
      PaperValueTyped d new target result a := by
  exact (hv.graphWeaken hp).termSubstitute (graphFormalReplacements_typed formals hp hr h)

/-- R27 transports this exact judgment and every tail replacement before substitution. -/
theorem ValuesTyped.substituteFreshGraphFormals {d old new source target vs ts rho}
    (formals : List (Nat × Ty)) (hp : GraphLookupPreserved old new)
    (hr : ∀ identity a, (identity,a) ∈ formals → lookupGraphEnvironment new identity = some a)
    (h : TermSubstitutionTyped d old source target rho)
    (hv : ValuesTyped d old (formals.map Prod.snd ++ source) vs ts) :
    ∃ result, termSubstituteValues (graphFormalReplacements formals rho) vs = some result ∧
      ValuesTyped d new target result ts := by
  exact (hv.graphWeaken hp).termSubstitute (graphFormalReplacements_typed formals hp hr h)

/-- R27 transports this exact judgment and every tail replacement before substitution. -/
theorem ValuesAllTyped.substituteFreshGraphFormals {d old new source target vs a rho}
    (formals : List (Nat × Ty)) (hp : GraphLookupPreserved old new)
    (hr : ∀ identity a, (identity,a) ∈ formals → lookupGraphEnvironment new identity = some a)
    (h : TermSubstitutionTyped d old source target rho)
    (hv : ValuesAllTyped d old (formals.map Prod.snd ++ source) vs a) :
    ∃ result, termSubstituteValues (graphFormalReplacements formals rho) vs = some result ∧
      ValuesAllTyped d new target result a := by
  exact (hv.graphWeaken hp).termSubstitute (graphFormalReplacements_typed formals hp hr h)

/-- R27 transports this exact judgment and every tail replacement before substitution. -/
theorem RecordPayloadsTyped.substituteFreshGraphFormals {d old new source target fs a rho}
    (formals : List (Nat × Ty)) (hp : GraphLookupPreserved old new)
    (hr : ∀ identity a, (identity,a) ∈ formals → lookupGraphEnvironment new identity = some a)
    (h : TermSubstitutionTyped d old source target rho)
    (hv : RecordPayloadsTyped d old (formals.map Prod.snd ++ source) fs a) :
    ∃ result, termSubstituteFields (graphFormalReplacements formals rho) fs = some result ∧
      RecordPayloadsTyped d new target result a := by
  exact (hv.graphWeaken hp).termSubstitute (graphFormalReplacements_typed formals hp hr h)

/-- R27 transports this exact judgment and every tail replacement before substitution. -/
theorem PaperComputationTyped.substituteFreshGraphFormals {d old new source target c a rho}
    (formals : List (Nat × Ty)) (hp : GraphLookupPreserved old new)
    (hr : ∀ identity a, (identity,a) ∈ formals → lookupGraphEnvironment new identity = some a)
    (h : TermSubstitutionTyped d old source target rho)
    (hv : PaperComputationTyped d old (formals.map Prod.snd ++ source) c a) :
    ∃ result, termSubstituteComputation (graphFormalReplacements formals rho) c = some result ∧
      PaperComputationTyped d new target result a := by
  exact (hv.graphWeaken hp).termSubstitute (graphFormalReplacements_typed formals hp hr h)

/-- R27 transports this exact judgment and every tail replacement before substitution. -/
theorem PaperContinuationTyped.substituteFreshGraphFormals {d old new source target v a b rho}
    (formals : List (Nat × Ty)) (hp : GraphLookupPreserved old new)
    (hr : ∀ identity a, (identity,a) ∈ formals → lookupGraphEnvironment new identity = some a)
    (h : TermSubstitutionTyped d old source target rho)
    (hv : PaperContinuationTyped d old (formals.map Prod.snd ++ source) v a b) :
    ∃ result, termSubstituteValue (graphFormalReplacements formals rho) v = some result ∧
      PaperContinuationTyped d new target result a b := by
  exact (hv.graphWeaken hp).termSubstitute (graphFormalReplacements_typed formals hp hr h)

theorem freshGraphReference_application {d old source target v a rho identity newType}
    (fresh : identity ∉ old.map Prod.fst)
    (h : TermSubstitutionTyped d old source target rho)
    (hv : PaperValueTyped d old (newType :: source) v a) :
    ∃ result, termSubstituteValue (graphFormalReplacements [(identity,newType)] rho) v = some result ∧
      PaperValueTyped d ((identity,newType)::old) target result a := by
  apply PaperValueTyped.substituteFreshGraphFormals [(identity,newType)]
    (GraphLookupPreserved.freshCons fresh) _ h hv
  intro i t hit
  have he : (i,t) = (identity,newType) := by simpa using hit
  cases he
  simp [lookupGraphEnvironment]

theorem graph_formal_order_falsifier (a b : Ty) :
    termSubstituteValue (graphFormalReplacements [(10,a),(20,b)] Value.variable)
      (.tuple [.variable 0,.variable 1]) = some (.tuple [.graphReference 10,.graphReference 20]) := by
  simp [termSubstituteValue, supportedTermValue, replaceTermValue, graphFormalReplacements]


/-- Success is controlled by the source syntax, independently of any typing derivation. -/
theorem termSubstituteValue_isSome (rho : Nat → Value) (v : Value) :
    (termSubstituteValue rho v).isSome = supportedTermValue v := by
  unfold termSubstituteValue
  cases supportedTermValue v <;> rfl

theorem termSubstituteComputation_isSome (rho : Nat → Value) (c : Computation) :
    (termSubstituteComputation rho c).isSome = supportedTermComputation c := by
  unfold termSubstituteComputation
  cases supportedTermComputation c <;> rfl

/-- Split is the represented tuple-pattern binder; the free replacement crosses both binders. -/
theorem tuple_pattern_binder_capture :
    termSubstituteComputation (fun _ => .variable 0)
      (.split (.variable 0) [7,8] (.ret (.variable 2))) =
      some (.split (.variable 0) [7,8] (.ret (.variable 2))) := by
  simp [termSubstituteComputation, supportedTermComputation, supportedTermValue,
    replaceTermComputation, replaceTermValue, liftTermSubstitutionN, liftTermSubstitution,
    renameTermValue]

/-- Sequentially changing 0 to 1 and then 1 to 0 collapses the pair;
the simultaneous vector instead swaps it, as simultaneous_order_falsifier states. -/
theorem sequential_substitution_falsifier :
    replaceTermValue (fun n => if n = 1 then .variable 0 else .variable n)
      (replaceTermValue (fun n => if n = 0 then .variable 1 else .variable n)
        (.tuple [.variable 0,.variable 1])) = .tuple [.variable 0,.variable 0] ∧
    (.tuple [.variable 0,.variable 0] : Value) ≠ .tuple [.variable 1,.variable 0] ∧
    (.tuple [.graphReference 10,.graphReference 20] : Value) ≠
      .tuple [.graphReference 20,.graphReference 10] := by
  simp [replaceTermValue]

end YulangClosure.PaperTypes
