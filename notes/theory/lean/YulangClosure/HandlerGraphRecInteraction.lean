import YulangClosure.HandlerGraphInteraction
import YulangClosure.HandlerGraphRecAllocation

/-! Actual source recursive allocation is an immutable extension consumed by
root-published handler/graph continuations. This is the primary composition. -/
namespace YulangClosure.HandlerGraph.Combined
open HigherOrder (Ty Context emptyContext extend OperationInstance)
open YulangClosure.HandlerGraph.Extension
variable {R S T U : Type}

mutual
  theorem map_closeValue (f : T → U) (g : R → T) (h : S → T)
      (v : Value R S) :
      YulangClosure.HandlerGraph.Extension.mapValue f (YulangClosure.HandlerGraph.Recursive.closeNamesValue g h v) =
        YulangClosure.HandlerGraph.Recursive.closeNamesValue (fun r => f (g r)) (fun s => f (h s)) v := by
    cases v <;> simp [YulangClosure.HandlerGraph.Extension.mapValue, YulangClosure.HandlerGraph.Recursive.closeNamesValue, map_closeComp, map_closeValue, map_closeAdapter]
  theorem map_closeComp (f : T → U) (g : R → T) (h : S → T)
      (m : Comp R S) :
      YulangClosure.HandlerGraph.Extension.mapComp f (YulangClosure.HandlerGraph.Recursive.closeNamesComp g h m) =
        YulangClosure.HandlerGraph.Recursive.closeNamesComp (fun r => f (g r)) (fun s => f (h s)) m := by
    cases m <;> simp [YulangClosure.HandlerGraph.Extension.mapComp, YulangClosure.HandlerGraph.Recursive.closeNamesComp, map_closeValue, map_closeComp,
      map_closeHandler, map_closeValueArms, map_closeOperationArms]
  theorem map_closeHandler (f : T → U) (g : R → T) (h : S → T)
      (v : Handler R S) :
      YulangClosure.HandlerGraph.Extension.mapHandler f (YulangClosure.HandlerGraph.Recursive.closeNamesHandler g h v) =
        YulangClosure.HandlerGraph.Recursive.closeNamesHandler (fun r => f (g r)) (fun s => f (h s)) v := by
    cases v <;> simp [YulangClosure.HandlerGraph.Extension.mapHandler, YulangClosure.HandlerGraph.Recursive.closeNamesHandler, map_closeValueArms, map_closeOperationArms]
  theorem map_closeValueArms (f : T → U) (g : R → T) (h : S → T)
      (v : ValueArms R S) :
      YulangClosure.HandlerGraph.Extension.mapValueArms f (YulangClosure.HandlerGraph.Recursive.closeNamesValueArms g h v) =
        YulangClosure.HandlerGraph.Recursive.closeNamesValueArms (fun r => f (g r)) (fun s => f (h s)) v := by
    cases v <;> simp [YulangClosure.HandlerGraph.Extension.mapValueArms, YulangClosure.HandlerGraph.Recursive.closeNamesValueArms, map_closeComp, map_closeValueArms]
  theorem map_closeOperationArms (f : T → U) (g : R → T) (h : S → T)
      (v : OperationArms R S) :
      YulangClosure.HandlerGraph.Extension.mapOperationArms f (YulangClosure.HandlerGraph.Recursive.closeNamesOperationArms g h v) =
        YulangClosure.HandlerGraph.Recursive.closeNamesOperationArms (fun r => f (g r)) (fun s => f (h s)) v := by
    cases v <;> simp [YulangClosure.HandlerGraph.Extension.mapOperationArms, YulangClosure.HandlerGraph.Recursive.closeNamesOperationArms,
      map_closeComp, map_closeOperationArms]
  theorem map_closeAdapter (f : T → U) (g : R → T) (h : S → T)
      (v : Adapter R S) :
      YulangClosure.HandlerGraph.Extension.mapAdapter f (YulangClosure.HandlerGraph.Recursive.closeNamesAdapter g h v) =
        YulangClosure.HandlerGraph.Recursive.closeNamesAdapter (fun r => f (g r)) (fun s => f (h s)) v := by
    cases v <;> simp [YulangClosure.HandlerGraph.Extension.mapAdapter, YulangClosure.HandlerGraph.Recursive.closeNamesAdapter, map_closeComp]
end

mutual
  theorem closeNames_idValue (v : Value R Empty) :
      YulangClosure.HandlerGraph.Recursive.closeNamesValue id Empty.elim v = v := by
    cases v with
    | recvar name => cases name
    | _ => simp [YulangClosure.HandlerGraph.Recursive.closeNamesValue, closeNames_idComp,
        closeNames_idValue, closeNames_idAdapter]
  theorem closeNames_idComp (m : Comp R Empty) :
      YulangClosure.HandlerGraph.Recursive.closeNamesComp id Empty.elim m = m := by
    cases m <;> simp [YulangClosure.HandlerGraph.Recursive.closeNamesComp, closeNames_idValue, closeNames_idComp,
      closeNames_idHandler, closeNames_idValueArms, closeNames_idOperationArms]
  theorem closeNames_idHandler (v : Handler R Empty) :
      YulangClosure.HandlerGraph.Recursive.closeNamesHandler id Empty.elim v = v := by
    cases v <;> simp [YulangClosure.HandlerGraph.Recursive.closeNamesHandler, closeNames_idValueArms,
      closeNames_idOperationArms]
  theorem closeNames_idValueArms (v : ValueArms R Empty) :
      YulangClosure.HandlerGraph.Recursive.closeNamesValueArms id Empty.elim v = v := by
    cases v <;> simp [YulangClosure.HandlerGraph.Recursive.closeNamesValueArms, closeNames_idComp, closeNames_idValueArms]
  theorem closeNames_idOperationArms (v : OperationArms R Empty) :
      YulangClosure.HandlerGraph.Recursive.closeNamesOperationArms id Empty.elim v = v := by
    cases v <;> simp [YulangClosure.HandlerGraph.Recursive.closeNamesOperationArms, closeNames_idComp,
      closeNames_idOperationArms]
  theorem closeNames_idAdapter (v : Adapter R Empty) :
      YulangClosure.HandlerGraph.Recursive.closeNamesAdapter id Empty.elim v = v := by
    cases v <;> simp [YulangClosure.HandlerGraph.Recursive.closeNamesAdapter, closeNames_idComp]
end

theorem mapOld_agrees (f : R → T) (v : Value R Empty) :
    YulangClosure.HandlerGraph.Extension.mapValue f v = YulangClosure.HandlerGraph.Recursive.mapOld f v := by
  rw [YulangClosure.HandlerGraph.Recursive.mapOld]
  calc
    YulangClosure.HandlerGraph.Extension.mapValue f v =
        YulangClosure.HandlerGraph.Extension.mapValue f
          (YulangClosure.HandlerGraph.Recursive.closeNamesValue id Empty.elim v) := by rw [closeNames_idValue]
    _ = YulangClosure.HandlerGraph.Recursive.closeNamesValue
        (fun r => f (id r)) (fun s => f (Empty.elim s)) v := map_closeValue f id Empty.elim v
    _ = YulangClosure.HandlerGraph.Recursive.closeNamesValue f Empty.elim v := by
      have h : (fun s : Empty => f (Empty.elim s)) = (Empty.elim : Empty → T) := by
        funext s
        cases s
      rw [h]
      simp only [id_eq]

/-- The actual allocation is an immutable six-sort embedding. Old nodes are
exactly their reference-mapped values; new source code is left untouched. -/
def sourceEmbedding (graph : Graph R) (xi : R → Ty) (nu : Fin n → Ty)
    (capture : Nat → Value R Empty) (rhs : Fin n → Value R Empty) :
    YulangClosure.HandlerGraph.Extension.Embedding graph xi (YulangClosure.HandlerGraph.Recursive.allocate graph (YulangClosure.HandlerGraph.Recursive.sourceFresh capture rhs))
      (YulangClosure.HandlerGraph.Recursive.joinTy xi nu) where
  refs := Sum.inl
  injective := fun {_ _} h => Sum.inl.inj h
  types := fun _ => rfl
  nodes := by
    intro r
    change YulangClosure.HandlerGraph.Recursive.mapOld Sum.inl (graph r) = YulangClosure.HandlerGraph.Extension.mapValue Sum.inl (graph r)
    exact (mapOld_agrees Sum.inl (graph r)).symm

theorem sourceExtension_typed {graph : Graph R} {xi : R → Ty} {nu : Fin n → Ty}
    (hgraph : WellTyped graph xi)
    (rhs : Fin n → Value R Empty)
    (hrhs : ∀ s, ValueTyped xi emptyTy (YulangClosure.HandlerGraph.Recursive.sourceContext nu env) (rhs s) (nu s))
    (capture : Nat → Value R Empty)
    (hcapture : YulangClosure.HandlerGraph.Recursive.CapturesTyped xi env capture) :
    WellTyped (YulangClosure.HandlerGraph.Recursive.allocate graph (YulangClosure.HandlerGraph.Recursive.sourceFresh capture rhs)) (YulangClosure.HandlerGraph.Recursive.joinTy xi nu) :=
  YulangClosure.HandlerGraph.Recursive.source_allocation_typed hgraph hrhs hcapture

def sourceExtension_guarded {graph : Graph R}
    (guard : GuardedValueGraph.Guarded (projectGraph graph))
    (rhs : Fin n → Value R Empty)
    (capture : Nat → Value R Empty)
    (hcycle : YulangClosure.HandlerGraph.Recursive.FreshNoCycle (YulangClosure.HandlerGraph.Recursive.sourceFresh capture rhs)) :
    GuardedValueGraph.Guarded (projectGraph (YulangClosure.HandlerGraph.Recursive.allocate graph (YulangClosure.HandlerGraph.Recursive.sourceFresh capture rhs))) :=
  YulangClosure.HandlerGraph.Recursive.allocationGuard guard _ hcycle

/-- A source-typed simultaneous recursive allocation is directly consumable by
the persistent interaction protocol. The old run and every published record
are transported through the actual inl embedding; no fresh node is chosen by
an oracle. -/
theorem run_source_extension
    {B : Type} {initialGraph : Graph B} {initialTypes : B → Ty}
    {initial : Comp B Empty} {graph : Graph R} {xi : R → Ty}
    {current : Comp R Empty} {arena : List (Saved R)}
    (run : Run B initialGraph initialTypes initial R graph xi current arena)
    (hgraph : WellTyped graph xi)
    (rhs : Fin n → Value R Empty)
    (hrhs : ∀ s, ValueTyped xi emptyTy
      (YulangClosure.HandlerGraph.Recursive.sourceContext nu env) (rhs s) (nu s))
    (capture : Nat → Value R Empty)
    (hcapture : YulangClosure.HandlerGraph.Recursive.CapturesTyped xi env capture) :
    Run B initialGraph initialTypes initial
      (Sum R (Fin n))
      (YulangClosure.HandlerGraph.Recursive.allocate graph
        (YulangClosure.HandlerGraph.Recursive.sourceFresh capture rhs))
      (YulangClosure.HandlerGraph.Recursive.joinTy xi nu)
      (mapComp Sum.inl current)
      (arena.map (Saved.map Sum.inl)) := by
  exact Run.extension (sourceEmbedding graph xi nu capture rhs) run
    (sourceExtension_typed hgraph rhs hrhs capture hcapture)

/-- The interaction invariant discharges typing of every saved continuation
after the source allocation, preserving the original request's response type. -/
theorem run_source_extension_saved_typed
    {B : Type} {initialGraph : Graph B} {initialTypes : B → Ty}
    {initial : Comp B Empty} {graph : Graph R} {xi : R → Ty}
    {current : Comp R Empty} {arena : List (Saved R)} {result : Ty}
    (initialGraphTyped : WellTyped initialGraph initialTypes)
    (initialTyped : CompTyped initialTypes emptyTy emptyContext initial result)
    (run : Run B initialGraph initialTypes initial R graph xi current arena)
    (hgraph : WellTyped graph xi)
    (rhs : Fin n → Value R Empty)
    (hrhs : ∀ s, ValueTyped xi emptyTy
      (YulangClosure.HandlerGraph.Recursive.sourceContext nu env) (rhs s) (nu s))
    (capture : Nat → Value R Empty)
    (hcapture : YulangClosure.HandlerGraph.Recursive.CapturesTyped xi env capture)
    (saved : Saved R) (member : saved ∈ arena) :
    SavedTyped (YulangClosure.HandlerGraph.Recursive.joinTy xi nu)
      (saved.map Sum.inl) result := by
  have extended := run_source_extension run hgraph rhs hrhs capture hcapture
  have invariant := run_invariant initialGraphTyped initialTyped extended
  exact invariant.2.2 _ (List.mem_map.mpr ⟨saved, member, rfl⟩)

/-- A reference to a real source-allocated node can answer an older published
root request. Its reference typing is derived from the allocated graph, whose
node typing in turn came from the source RHS; every prefix uses the actual
guard constructed for this allocation. -/
theorem run_source_answer_old
    {B : Type} {initialGraph : Graph B} {initialTypes : B → Ty}
    {initial : Comp B Empty} {graph : Graph R} {xi : R → Ty}
    {current : Comp R Empty} {arena : List (Saved R)} {result : Ty}
    (initialGraphTyped : WellTyped initialGraph initialTypes)
    (initialTyped : CompTyped initialTypes emptyTy emptyContext initial result)
    (run : Run B initialGraph initialTypes initial R graph xi current arena)
    (hgraph : WellTyped graph xi)
    (guard : GuardedValueGraph.Guarded (projectGraph graph))
    (rhs : Fin n → Value R Empty)
    (hrhs : ∀ s, ValueTyped xi emptyTy
      (YulangClosure.HandlerGraph.Recursive.sourceContext nu env) (rhs s) (nu s))
    (capture : Nat → Value R Empty)
    (hcapture : YulangClosure.HandlerGraph.Recursive.CapturesTyped xi env capture)
    (hcycle : YulangClosure.HandlerGraph.Recursive.FreshNoCycle
      (YulangClosure.HandlerGraph.Recursive.sourceFresh capture rhs))
    (saved : Saved R) (member : saved ∈ arena)
    (slot : Fin n) (responseType : nu slot = saved.operation.responseType) :
    ∀ trace last,
      Prefix
        (YulangClosure.HandlerGraph.Recursive.allocate graph
          (YulangClosure.HandlerGraph.Recursive.sourceFresh capture rhs))
        ((saved.map Sum.inl).resume (.ref (.inr slot))) trace last →
      CompTyped (YulangClosure.HandlerGraph.Recursive.joinTy xi nu)
        emptyTy emptyContext last result ∧
      CanProgress
        (YulangClosure.HandlerGraph.Recursive.allocate graph
          (YulangClosure.HandlerGraph.Recursive.sourceFresh capture rhs)) last := by
  let extended := run_source_extension run hgraph rhs hrhs capture hcapture
  have allocatedTyped := sourceExtension_typed hgraph rhs hrhs capture hcapture
  have answered : Run B initialGraph initialTypes initial
      (Sum R (Fin n))
      (YulangClosure.HandlerGraph.Recursive.allocate graph
        (YulangClosure.HandlerGraph.Recursive.sourceFresh capture rhs))
      (YulangClosure.HandlerGraph.Recursive.joinTy xi nu)
      ((saved.map Sum.inl).resume (.ref (.inr slot)))
      (arena.map (Saved.map Sum.inl)) := by
    apply Run.answer extended
    · exact List.mem_map.mpr ⟨saved, member, rfl⟩
    · exact .matched (s := saved.map Sum.inl) saved.operation rfl (.ref (.inr slot))
    · simpa [YulangClosure.HandlerGraph.Recursive.joinTy, responseType] using
        (ValueTyped.ref (xi := YulangClosure.HandlerGraph.Recursive.joinTy xi nu)
          (.inr slot))
  intro trace last steps
  have safety := run_prefix_safety initialGraphTyped initialTyped answered
    (sourceExtension_guarded guard rhs capture hcycle) steps
  exact ⟨safety.1, safety.2.1⟩

namespace ConcreteSourceRun
open YulangClosure.HandlerGraph.Recursive
open YulangClosure.HandlerGraph.Extension.Demo

def captures : Nat → Value (Fin 1) Empty := fun _ => .unit
def recursiveOperation : OperationInstance := ⟨75, [callableTy], callableTy, unitTy⟩

/-- The value arm forwards the callback's own source recursive reference as
the payload of its later operation. Its de Bruijn index is two beneath the
handler-arm binder and lambda input binder. -/
def recursiveRequestHandler : Handler (Fin 1) Empty :=
  .mk 92 unitTy unitTy
    (.cons (.request recursiveOperation (.var 2)
      (.ret (.inRight (.var 0)))) .nil) .nil

theorem recursiveRequestHandler_typed :
    HandlerTyped oldTypes emptyTy
      (extend (sourceContext (fun _ : Fin 1 => callableTy) emptyContext) (.thunk unitTy))
      recursiveRequestHandler unitTy unitTy :=
  .mk (.cons (.request (.var rfl) (.ret (.inRight (.var rfl)))) .nil) .nil

def recursiveCallback : Value (Fin 1) Empty :=
  .lambda .computation receipt unitTy unitTy unitTy
    (.handle recursiveRequestHandler (.ret .unit)) identityAdapter

theorem recursiveCallback_typed :
    ValueTyped oldTypes emptyTy
      (sourceContext (fun _ : Fin 1 => callableTy) emptyContext)
      recursiveCallback callableTy :=
  .lambdaComputation (.handle recursiveRequestHandler_typed (.ret .unit))
    (.mk (.ret (.var rfl)))

theorem captures_typed : CapturesTyped oldTypes emptyContext captures := by
  intro i a h
  cases h

def recursiveRhs : Fin 1 → Value (Fin 1) Empty := fun _ => recursiveCallback

def recursiveFresh : Fin 1 → Value (Sum (Fin 1) (Fin 1)) Empty :=
  sourceFresh captures recursiveRhs

theorem recursiveFresh_typed (s : Fin 1) :
    ValueTyped (joinTy oldTypes (fun _ : Fin 1 => callableTy)) emptyTy emptyContext
      (recursiveFresh s) callableTy :=
  sourceFresh_typed (fun _ => recursiveCallback_typed) captures_typed s

theorem recursiveFresh_noCycle : FreshNoCycle recursiveFresh :=
  GuardedValueGraph.FiniteDecision.noCycle_of_terminal (fun _ => rfl)

def recursiveGraph : Graph (Sum (Fin 1) (Fin 1)) := allocate old recursiveFresh
def recursiveTypes : Sum (Fin 1) (Fin 1) → Ty := joinTy oldTypes (fun _ => callableTy)

theorem recursiveGraph_typed : WellTyped recursiveGraph recursiveTypes :=
  allocate_typed old_typed _ (fun s => recursiveFresh_typed s)

def recursiveGraph_guard :
    GuardedValueGraph.Guarded (projectGraph recursiveGraph) :=
  allocationGuard
    (GuardedValueGraph.FiniteDecision.guardOfNoCycle _
      (GuardedValueGraph.FiniteDecision.noCycle_of_terminal (fun _ => rfl)))
    recursiveFresh recursiveFresh_noCycle

def recursiveResponse : Value (Sum (Fin 1) (Fin 1)) Empty := .ref (Sum.inr (0 : Fin 1))

theorem recursiveResponse_typed :
    ValueTyped recursiveTypes emptyTy emptyContext recursiveResponse callableTy :=
  .ref (Sum.inr (0 : Fin 1))

/-- The genuinely self-referential source callback can answer the original
published entry through the same source-allocation Run interface. -/
theorem recursive_callback_answers_old_entry :
    Run (Fin 1) old oldTypes saved.suspended
      (Sum (Fin 1) (Fin 1)) recursiveGraph recursiveTypes
      ((saved.map Sum.inl).resume recursiveResponse) [saved.map Sum.inl] := by
  apply Run.answer (Run.extension (sourceEmbedding old oldTypes
    (fun _ : Fin 1 => callableTy) captures recursiveRhs) (.publish saved .start)
    recursiveGraph_typed)
  · exact List.mem_cons.mpr (.inl rfl)
  · exact .matched (s := saved.map Sum.inl) operation rfl recursiveResponse
  · exact recursiveResponse_typed

theorem recursive_callback_prefix_safe
    {trace : List (Event (Sum (Fin 1) (Fin 1)))} {last : Comp (Sum (Fin 1) (Fin 1)) Empty}
    (steps : Prefix recursiveGraph ((saved.map Sum.inl).resume recursiveResponse) trace last) :
    CompTyped recursiveTypes emptyTy emptyContext last unitTy ∧
      CanProgress recursiveGraph last := by
  have safe := run_prefix_safety old_typed saved_actual_request
    recursive_callback_answers_old_entry recursiveGraph_guard steps
  exact ⟨safe.1, safe.2.1⟩

def rhs : Fin 1 → Value (Fin 1) Empty := fun _ => callback
def fresh : Fin 1 → Value (Sum (Fin 1) (Fin 1)) Empty := sourceFresh captures rhs

theorem rhs_typed (s : Fin 1) :
    ValueTyped oldTypes emptyTy (sourceContext (fun _ : Fin 1 => callableTy) emptyContext)
      (rhs s) callableTy := callback_typed

theorem fresh_noCycle : FreshNoCycle fresh :=
  GuardedValueGraph.FiniteDecision.noCycle_of_terminal (fun _ => rfl)

def oldGraphGuard : GuardedValueGraph.Guarded (projectGraph old) :=
  GuardedValueGraph.FiniteDecision.guardOfNoCycle _
    (GuardedValueGraph.FiniteDecision.noCycle_of_terminal (fun _ => rfl))

def graph : Graph (Sum (Fin 1) (Fin 1)) := allocate old fresh
def types : Sum (Fin 1) (Fin 1) → Ty := joinTy oldTypes (fun _ => callableTy)

theorem graph_typed : WellTyped graph types :=
  allocate_typed old_typed _ (sourceFresh_typed rhs_typed captures_typed)

def graph_guard : GuardedValueGraph.Guarded (projectGraph graph) :=
  allocationGuard oldGraphGuard _ fresh_noCycle

def callbackResponse : Value (Sum (Fin 1) (Fin 1)) Empty := .ref (Sum.inr (0 : Fin 1))

theorem callbackResponse_typed : ValueTyped types emptyTy emptyContext callbackResponse callableTy :=
  .ref (Sum.inr (0 : Fin 1))

/-- This source RHS is allocated from its actual handler-bearing syntax; its
fresh graph reference answers the initially published root request. -/
theorem first_answer_run :
    Run (Fin 1) old oldTypes saved.suspended
      (Sum (Fin 1) (Fin 1)) graph types
      ((saved.map Sum.inl).resume callbackResponse) [saved.map Sum.inl] := by
  apply Run.answer (Run.extension (sourceEmbedding old oldTypes (fun _ : Fin 1 => callableTy)
    captures rhs) (.publish saved .start) graph_typed)
  · exact List.mem_cons.mpr (.inl rfl)
  · exact .matched (s := saved.map Sum.inl) operation rfl callbackResponse
  · exact callbackResponse_typed

theorem callback_reaches_later_request :
    Prefix graph ((saved.map Sum.inl).resume callbackResponse)
      [.lookup (.inr 0), .lambdaEntry callbackPlan, .silent, .silent, .silent, .silent]
      laterSaved.suspended := by
  exact .cons .callRef
    (.cons .callLambda
      (.cons (.bind .handleReturn)
        (.cons (.bind .valueCons)
          (.cons (.bind .valueRequest)
            (.cons .bindRequest (.refl _))))))

theorem later_request_published :
    Run (Fin 1) old oldTypes saved.suspended
      (Sum (Fin 1) (Fin 1)) graph types laterSaved.suspended
      [laterSaved, saved.map Sum.inl] :=
  .publish laterSaved (run_internal_prefix first_answer_run callback_reaches_later_request)

def captures2 : Nat → Value (Sum (Fin 1) (Fin 1)) Empty := fun _ => .unit
def rhs2 : Fin 1 → Value (Sum (Fin 1) (Fin 1)) Empty := fun _ => .unit
def fresh2 : Fin 1 → Value (Sum (Sum (Fin 1) (Fin 1)) (Fin 1)) Empty :=
  sourceFresh captures2 rhs2

theorem captures2_typed : CapturesTyped types emptyContext captures2 := by
  intro i a h
  cases h

theorem rhs2_typed (s : Fin 1) :
    ValueTyped types emptyTy (sourceContext (fun _ : Fin 1 => unitTy) emptyContext)
      (rhs2 s) unitTy := .unit

def graph2 : Graph (Sum (Sum (Fin 1) (Fin 1)) (Fin 1)) := allocate graph fresh2
def types2 : Sum (Sum (Fin 1) (Fin 1)) (Fin 1) → Ty :=
  joinTy types (fun _ => unitTy)

theorem graph2_typed : WellTyped graph2 types2 :=
  allocate_typed graph_typed _ (sourceFresh_typed rhs2_typed captures2_typed)

theorem fresh2_noCycle : FreshNoCycle fresh2 :=
  GuardedValueGraph.FiniteDecision.noCycle_of_terminal (fun _ => rfl)

def graph2_guard : GuardedValueGraph.Guarded (projectGraph graph2) :=
  allocationGuard graph_guard _ fresh2_noCycle

/-- A second actual source allocation transports both published entries; the
original request can still be answered by the callback from the first source
allocation, at its transported reference. -/
theorem second_source_extension :
    Run (Fin 1) old oldTypes saved.suspended
      (Sum (Sum (Fin 1) (Fin 1)) (Fin 1)) graph2 types2
      (mapComp Sum.inl laterSaved.suspended)
      [laterSaved.map Sum.inl, (saved.map Sum.inl).map Sum.inl] := by
  simpa [graph2, types2, fresh2] using
    (run_source_extension (nu := fun _ : Fin 1 => unitTy)
      later_request_published graph_typed rhs2 rhs2_typed captures2 captures2_typed)

def callbackResponse2 : Value (Sum (Sum (Fin 1) (Fin 1)) (Fin 1)) Empty :=
  .ref (Sum.inl (Sum.inr 0))

theorem callbackResponse2_typed :
    ValueTyped types2 emptyTy emptyContext callbackResponse2 callableTy :=
  .ref (Sum.inl (Sum.inr 0))

theorem original_entry_reused_after_second_source_allocation :
    Run (Fin 1) old oldTypes saved.suspended
      (Sum (Sum (Fin 1) (Fin 1)) (Fin 1)) graph2 types2
      ((saved.map (fun r => Sum.inl (Sum.inl r))).resume callbackResponse2)
      [laterSaved.map Sum.inl, (saved.map Sum.inl).map Sum.inl] := by
  apply Run.answer second_source_extension
  · exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl)))
  · exact .matched (s := saved.map (fun r => Sum.inl (Sum.inl r)))
      operation rfl callbackResponse2
  · exact callbackResponse2_typed

end ConcreteSourceRun

end YulangClosure.HandlerGraph.Combined
