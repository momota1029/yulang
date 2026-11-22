import Yulang.GeneralDeclarativeCompoundBatch338

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCompoundRoutes338
open CommonRoleCanonicalRows (Row)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeEndpointProgram336 (Projection Jobs fields ready)
open GeneralDeclarativeEndpointOverlay336 (Entry receipts)
open GeneralDeclarativeCompoundPattern338 (layout layout_labels)
open GeneralDeclarativeCompoundBatch338 (Ticket minted protectedNames)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleOutermostResolver (All₂)

def key : Projection → Option Nat
  | .field _ label .. => some label
  | .rest .. => none

theorem ordered_fields {shape : List (Nat × Nat)} {lo hi : Row Expr}
    (built : fields arg shape lo hi = some jobs) :
    jobs.map (fun x => key x.2) = shape.map (fun x => some x.1) := by
  induction shape generalizing lo hi jobs with
  | nil => cases lo <;> cases hi <;> simp_all [fields]
  | cons hd tl ih =>
    obtain ⟨label,id⟩ := hd
    cases lo with
    | nil => simp [fields] at built
    | cons left ls =>
      cases hi with
      | nil => simp [fields] at built
      | cons right us =>
        obtain ⟨lk,a⟩ := left
        obtain ⟨hk,b⟩ := right
        by_cases same : lk = label ∧ hk = label
        · obtain ⟨l,r⟩ := same; subst lk; subst hk
          cases step : fields arg tl ls us with
          | none => simp [fields,step] at built
          | some rest =>
            have eq : (id,.field arg label a b)::rest = jobs := by simpa [fields,step] using built
            subst jobs
            change some label :: rest.map (fun x => key x.2) = some label :: tl.map (fun x => some x.1)
            rw [ih step]
        · simp [fields,same] at built

theorem ordered_program {s : State} {p : Supported s done} (t : Ticket p arg fs) :
    t.jobs.map (fun x => key x.2) = fs.map (fun x => some x.1) ++ [none] := by
  cases h : fields arg (layout fs) t.first t.last with
  | none =>
    have no := t.calculated
    simp [ready,h] at no
  | some front =>
    have eq := Option.some.inj (by simpa [ready,h] using t.calculated)
    have fmap := congrArg (List.map some) (layout_labels fs)
    simp only [List.map_map,Function.comp_def] at fmap
    rw [← eq]
    rw [List.map_append,ordered_fields h,fmap]
    rfl

theorem receipt_keys (s : State) (keep : List Nat) (jobs : Jobs) :
    (receipts s keep jobs).map (fun e => key e.1) = jobs.map (fun j => key j.2) := by
  simpa only [receipts,List.map_map,Function.comp_def] using
    congrArg (List.map (fun j => key j.2)) (List.zipIdx_map_fst 0 jobs)

theorem minted_keys {s : State} {p : Supported s done} (t : Ticket p arg fs) :
    (minted s old keep t.jobs).map (fun e => key e.1) = fs.map (fun x => some x.1) ++ [none] :=
  (receipt_keys s _ t.jobs).trans (ordered_program t)

/-- Routing consumes actual emitted receipts in source field order.
It returns the final subtraction route separately from traversed
payloads; the parent layout indices are not returned as binders. -/
def dispatch : Row Pattern → List Entry → Option (List (Entry × Pattern) × Entry)
  | [],[tail] => if key tail.1 = none then some ([],tail) else none
  | (label,p)::rest,e::es => do
    if key e.1 = some label then
      let (later,tail) ← dispatch rest es
      pure ((e,p)::later,tail)
    else none
  | _,_ => none

theorem dispatch_total {rs : List Entry} {fs : Row Pattern}
    (align : rs.map (fun e => key e.1) = fs.map (fun x => some x.1) ++ [none]) :
    ∃ tasks tail, dispatch fs rs = some (tasks,tail) := by
  induction fs generalizing rs with
  | nil =>
    cases rs with
    | nil => simp at align
    | cons e more =>
      cases more with
      | nil => exact ⟨[],e,by simpa [dispatch] using align⟩
      | cons next rest => simp at align
  | cons p more ih =>
    obtain ⟨label,pat⟩ := p
    cases rs with
    | nil => simp at align
    | cons e es =>
      simp only [List.map_cons,List.cons_append,List.cons.injEq] at align
      obtain ⟨tasks,tail,page⟩ := ih align.2
      exact ⟨(e,pat)::tasks,tail,by simp [dispatch,align.1,page]⟩

theorem dispatch_exact {rs : List Entry} {fs : Row Pattern}
    (computed : dispatch fs rs = some (tasks,tail)) :
    tasks.map Prod.snd = fs.map Prod.snd ∧
    rs = tasks.map Prod.fst ++ [tail] ∧
    All₂ (fun task field => task.2 = field.2 ∧ key task.1.1 = some field.1) tasks fs ∧
    key tail.1 = none := by
  induction fs generalizing rs tasks tail with
  | nil =>
    cases rs with
    | nil => simp [dispatch] at computed
    | cons e more =>
      cases more with
      | cons next rest => simp [dispatch] at computed
      | nil =>
        by_cases h : key e.1 = none
        · have eq : (([], e) : List (Entry × Pattern) × Entry) = (tasks,tail) := by simpa [dispatch,h] using computed
          cases eq
          exact ⟨rfl,rfl,.nil,h⟩
        · simp [dispatch,h] at computed
  | cons p more ih =>
    obtain ⟨label,pat⟩ := p
    cases rs with
    | nil => simp [dispatch] at computed
    | cons e es =>
      by_cases h : key e.1 = some label
      · cases loop : dispatch more es with
        | none => simp [dispatch,h,loop] at computed
        | some next =>
          obtain ⟨rest,finish⟩ := next
          have eq : ((e,pat)::rest,finish) = (tasks,tail) := by simpa [dispatch,h,loop] using computed
          cases eq
          obtain ⟨ps,rs',links,endSyntax⟩ := ih loop
          exact ⟨by simp [ps],by simp [rs'],.cons ⟨rfl,h⟩ links,endSyntax⟩
      · simp [dispatch,h] at computed

theorem route {s : State} {p : Supported s done} (ticket : Ticket p arg fs) :
    ∃ tasks tail,
      dispatch fs (minted s old keep ticket.jobs) = some (tasks,tail) ∧
      tasks.map Prod.snd = fs.map Prod.snd ∧
      minted s old keep ticket.jobs = tasks.map Prod.fst ++ [tail] := by
  obtain ⟨tasks,tail,run⟩ := dispatch_total (minted_keys (old := old) (keep := keep) ticket)
  obtain ⟨ps,recs,_,_⟩ := dispatch_exact run
  exact ⟨tasks,tail,run,ps,recs⟩

end Yulang.GeneralDeclarativeCompoundRoutes338
