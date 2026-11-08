import Yulang.CommonRoleOpenPropagation

/-! A state-returning recursive pass over the actual two-endpoint producer.
This is not saturation and does not finalize intermediate ambiguity. The
endpoint allocation remains the explicit boundary described in Propagation.
Every sibling is invoked with the preceding sibling's returned state. After
all descendants return, every immediate sibling and the parent are produced
again using the final state. No no-op recollection premise is used. -/
namespace Yulang.CommonRoleOpenRecursivePass
open CommonRoleSettledConstraints (State)
open CommonRoleOpenProducer (Request Registry Local)
open CommonRoleOpenPropagation (Allocation Produced produce prepare childList)
open CommonRoleOutermostResolver (Frontier Child All₂)

inductive Trace where
  | node (initial : Frontier Request) (children : List Trace)
      (refreshed : List (Frontier Request)) (parent : Frontier Request)

/-- State-gated selected children are actual structural producer children. -/
theorem child_origin (visible) (allocate : Allocation n) (q : Request) (s : State n)
    (child : Request) (member : child ∈ childList (produce visible allocate q s)) :
    Child (Local visible) child q := by
  have produced := (CommonRoleOpenPropagation.produce_exact visible allocate q s _).mp rfl
  cases observed : produce visible allocate q s with
  | pending | rejected | ambiguous => simp [observed, childList] at member
  | selected key cs =>
      simp only [observed, childList] at member
      rw [observed] at produced
      cases produced with
      | valid _ localRule => exact ⟨key, cs, localRule, member⟩

/-- The accessibility recursion returns a state transformer, so the child
state is not fixed in its accessibility proof. -/
def runAcc (registry : Registry) (allocate : Allocation n) (q : Request)
    (accessible : Acc (Child (Local registry.declarations)) q) : State n → Trace × State n :=
  accessible.rec (motive := fun _ _ => State n → Trace × State n)
    fun parent _ recurse s =>
      let current := prepare registry.declarations allocate parent s
      let initial := produce registry.declarations allocate parent s
      let cs := childList initial
      let (outputs, final) := CommonRoleOpenThreading.thread
        (fun child : { c // c ∈ cs } => recurse child.val
          (child_origin registry.declarations allocate parent s child.val child.property))
        cs.attach current
      (.node initial outputs
        (cs.map (fun child => produce registry.declarations allocate child final))
        (produce registry.declarations allocate parent final), final)

/-- No external fuel, rank, frontier exactness or accessibility premise. This
executes one recursive state-returning pass, not a final source resolver. -/
def run (registry : Registry) (allocate : Allocation n) (q : Request) : State n → Trace × State n :=
  runAcc registry allocate q (CommonRoleOpenProducerAccess.accessible registry q)

theorem runAcc_unfold (registry : Registry) (allocate : Allocation n) (q : Request)
    (accessible : Acc (Child (Local registry.declarations)) q) (s : State n) :
    runAcc registry allocate q accessible s =
      let current := prepare registry.declarations allocate q s
      let initial := produce registry.declarations allocate q s
      let cs := childList initial
      let (outputs, final) := CommonRoleOpenThreading.thread
        (fun child : { c // c ∈ cs } => runAcc registry allocate child.val
          (accessible.inv (child_origin registry.declarations allocate q s child.val child.property)))
        cs.attach current
      (.node initial outputs
        (cs.map (fun child => produce registry.declarations allocate child final))
        (produce registry.declarations allocate q final), final) := by
  cases accessible
  rfl

/-- Proof irrelevance makes execution independent of the construction of Acc. -/
theorem runAcc_eq_run (registry : Registry) (allocate : Allocation n) (q : Request)
    (accessible : Acc (Child (Local registry.declarations)) q) :
    runAcc registry allocate q accessible = run registry allocate q := rfl

theorem thread_attach (run : α → State n → β × State n) (xs : List α) (s : State n) :
    CommonRoleOpenThreading.thread (fun x : { x // x ∈ xs } => run x.val) xs.attach s =
      CommonRoleOpenThreading.thread run xs s := by
  have aux (ys : List { x // x ∈ xs }) (s : State n) :
      CommonRoleOpenThreading.thread (fun x : { x // x ∈ xs } => run x.val) ys s =
        CommonRoleOpenThreading.thread run (ys.map Subtype.val) s := by
    induction ys generalizing s with
    | nil => rfl
    | cons y rest ih => simp only [CommonRoleOpenThreading.thread, List.map_cons, ih]
  simpa using aux xs.attach s

/-- Executable recursion equation uses the public entry for every child. -/
theorem run_unfold (registry : Registry) (allocate : Allocation n) (q : Request) (s : State n) :
    run registry allocate q s =
      let current := prepare registry.declarations allocate q s
      let initial := produce registry.declarations allocate q s
      let cs := childList initial
      let (outputs, final) := CommonRoleOpenThreading.thread (run registry allocate) cs current
      (.node initial outputs
        (cs.map (fun child => produce registry.declarations allocate child final))
        (produce registry.declarations allocate q final), final) := by
  unfold run
  rw [runAcc_unfold]
  simp only [runAcc_eq_run, thread_attach]

/-- Independent recursive pass judgment. The state returned by each child is
passed to the next by Thread; final observations use the final shared state.
It mentions neither run nor runAcc. -/
inductive Runs (visible : List CommonRoleSettledSyntax.Declaration) (allocate : Allocation n) :
    Request → State n → Trace → State n → Prop where
  | node : Produced visible allocate q s initial →
      CommonRoleOpenThreading.Thread (Runs visible allocate) (childList initial)
        (prepare visible allocate q s) outputs final →
      All₂ (fun child observation => Produced visible allocate child final observation)
        (childList initial) refreshed →
      Produced visible allocate q final parent →
      Runs visible allocate q s (.node initial outputs refreshed parent) final

/-- Exactness of the recursive PASS only. There is no hypothesis for local
producer exactness or for termination; both were proved for this producer.
This does not assert saturation, order independence, source slot provenance,
or an outer final four-way classification. -/
theorem run_exact (registry : Registry) (allocate : Allocation n) (q : Request)
    (s : State n) (trace : Trace) (final : State n) :
    run registry allocate q s = (trace, final) ↔ Runs registry.declarations allocate q s trace final := by
  have accessible := CommonRoleOpenProducerAccess.accessible registry q
  induction accessible generalizing s trace final with
  | intro q predecessors ih =>
      rw [run_unfold]
      let initial := produce registry.declarations allocate q s
      let cs := childList initial
      have childExact (child : Request) (member : child ∈ cs) (before : State n)
          (result : Trace) (after : State n) :
          run registry allocate child before = (result, after) ↔
            Runs registry.declarations allocate child before result after :=
        ih child (child_origin registry.declarations allocate q s child member) before result after
      have threads (before : State n) (outputs : List Trace) (after : State n) :
          CommonRoleOpenThreading.thread (run registry allocate) cs before = (outputs, after) ↔
            CommonRoleOpenThreading.Thread (Runs registry.declarations allocate) cs before outputs after := by
        have aux (xs : List Request) (subset : ∀ child ∈ xs, child ∈ cs)
            (before : State n) (outputs : List Trace) (after : State n) :
            CommonRoleOpenThreading.thread (run registry allocate) xs before = (outputs, after) ↔
              CommonRoleOpenThreading.Thread (Runs registry.declarations allocate) xs before outputs after := by
          induction xs generalizing before outputs after with
          | nil =>
              constructor
              · intro h; cases h; exact .nil
              · intro h; cases h; rfl
          | cons child rest tailIH =>
              cases first : run registry allocate child before with
              | mk result next =>
                cases remaining : CommonRoleOpenThreading.thread (run registry allocate) rest next with
                | mk results endState =>
                  constructor
                  · intro h
                    simp only [CommonRoleOpenThreading.thread, first, remaining, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    exact .cons ((childExact child (subset child List.mem_cons_self) before result next).mp first)
                      ((tailIH (fun child member => subset child (List.mem_cons_of_mem _ member))
                        next results endState).mp remaining)
                  · intro h
                    cases h with
                    | cons one more =>
                        have firstEq := (childExact child (subset child List.mem_cons_self) ..).mpr one
                        rw [first] at firstEq
                        cases firstEq
                        have restEq := (tailIH (fun child member => subset child (List.mem_cons_of_mem _ member)) ..).mpr more
                        simp only [CommonRoleOpenThreading.thread, first, restEq]
        exact aux cs (fun _ h => h) before outputs after
      change (let (outputs, endState) := (CommonRoleOpenThreading.thread (run registry allocate) cs (prepare registry.declarations allocate q s));
        (Trace.node initial outputs (cs.map (fun child => produce registry.declarations allocate child endState))
          (produce registry.declarations allocate q endState), endState)) = (trace, final) ↔ _
      cases computed : CommonRoleOpenThreading.thread (run registry allocate) cs
          (prepare registry.declarations allocate q s) with
      | mk outputs endState =>
          constructor
          · intro h
            simp only [Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .node ((CommonRoleOpenPropagation.produce_exact ..).mp rfl)
              ((threads ..).mp computed)
              ((CommonRoleOpenThreading.refresh_exact _ _ (CommonRoleOpenPropagation.produce_exact registry.declarations allocate) ..).mp rfl)
              ((CommonRoleOpenPropagation.produce_exact ..).mp rfl)
          · intro h
            cases h with
            | node first children refreshed parent =>
                have firstEq := (CommonRoleOpenPropagation.produce_exact ..).mpr first
                change initial = _ at firstEq
                cases firstEq
                have childrenEq := (threads ..).mpr children
                rw [computed] at childrenEq
                cases childrenEq
                have refreshedEq := (CommonRoleOpenThreading.refresh_exact _ _
                  (CommonRoleOpenPropagation.produce_exact registry.declarations allocate) ..).mpr refreshed
                have parentEq := (CommonRoleOpenPropagation.produce_exact ..).mpr parent
                change cs.map (fun child => produce registry.declarations allocate child final) = _ at refreshedEq
                simp only [refreshedEq, parentEq]

/-- Final models satisfy the original state throughout the entire recursive
pass, not just one layer of children. -/
theorem runs_preserves (visible : List CommonRoleSettledSyntax.Declaration)
    (allocate : Allocation n) (q : Request) (s final : State n) (trace : Trace)
    (derivation : Runs visible allocate q s trace final)
    (assignment : Fin n → Core.PresenceGeneration.Comp Common.model)
    (model : PresenceNormalForm.All Common.model assignment final.atoms) :
    PresenceNormalForm.All Common.model assignment s.atoms := by
  refine Runs.rec
    (motive_1 := fun _ before _ after _ =>
      PresenceNormalForm.All Common.model assignment after.atoms →
        PresenceNormalForm.All Common.model assignment before.atoms)
    (motive_2 := fun _ before _ after _ =>
      PresenceNormalForm.All Common.model assignment after.atoms →
        PresenceNormalForm.All Common.model assignment before.atoms)
    ?_ ?_ ?_ derivation model
  · intro q before initial outputs after refreshed parent _ _ _ _ ih models
    exact ((CommonRoleOpenPropagation.prepare_exact visible allocate q before assignment).mp (ih models)).1
  · intro before models; exact models
  · intro child before result next rest results after _ _ ihFirst ihRest models
    exact ihFirst (ihRest models)

theorem run_preserves (registry : Registry) (allocate : Allocation n)
    (q : Request) (s : State n) (assignment : Fin n → Core.PresenceGeneration.Comp Common.model)
    (model : PresenceNormalForm.All Common.model assignment (run registry allocate q s).2.atoms) :
    PresenceNormalForm.All Common.model assignment s.atoms :=
  runs_preserves registry.declarations allocate q s _ _
    ((run_exact registry allocate q s _ _).mp rfl) assignment model

/-- The final parent and every final sibling observation are checked at the
same returned state. This asserts regeneration, not equality with the old
observations or stabilization of an unrestricted source worklist. -/
theorem run_recollects (registry : Registry) (allocate : Allocation n)
    (q : Request) (s final : State n) (initial parent : Frontier Request)
    (outputs : List Trace) (refreshed : List (Frontier Request))
    (computed : run registry allocate q s = (.node initial outputs refreshed parent, final)) :
    Produced registry.declarations allocate q final parent ∧
      All₂ (fun child observation => Produced registry.declarations allocate child final observation)
        (childList initial) refreshed := by
  have derivation := (run_exact registry allocate q s _ final).mp computed
  cases derivation with
  | node _ _ refreshed parent => exact ⟨parent, refreshed⟩

end Yulang.CommonRoleOpenRecursivePass
