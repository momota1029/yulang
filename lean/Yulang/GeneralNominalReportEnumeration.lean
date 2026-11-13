import Yulang.GeneralNominalReportErasure
import Yulang.GeneralNominalSharedEnumeration

/-! A finite overapproximation of the real recursive inspector. Bounds come
from a supplied finite source pool; nesting comes only from the query syntax. -/
namespace Yulang.GeneralNominalReportEnumeration
open GeneralNominalRecursiveInspection GeneralNominalReportErasure
open GeneralNominalInspection (Query Bounds)

def intervals (sources : List Nat) : List GeneralSourceState.Interval :=
  sources.flatMap fun lower => sources.map fun upper => (lower,upper)

theorem interval_member (supported : ∀ slot, state.base.source slot ∈ sources) (bounds : Bounds state) :
    interval state bounds ∈ intervals sources :=
  List.mem_flatMap.mpr ⟨_,supported bounds.1,List.mem_map.mpr ⟨_,supported bounds.2,rfl⟩⟩

def captureResult (names : List Nat) (bounds : GeneralSourceState.Interval) (origin : Option Origin) : Data :=
  ⟨names.map (fun name => ⟨name,bounds,origin⟩),[bounds],origin.toList.map (fun ref => (ref,bounds)),[]⟩

def products (first last : List Data) : List Data :=
  first.flatMap fun a => last.map (Data.append a)

theorem product_member (one : first ∈ left) (two : last ∈ right) : first.append last ∈ products left right :=
  List.mem_flatMap.mpr ⟨first,one,List.mem_map.mpr ⟨last,two,rfl⟩⟩

mutual
  def one (sources : List Nat) (query : Query) (bounds : GeneralSourceState.Interval)
      (origin : Option Origin) : List Data :=
    match query with
    | .variables names => [captureResult names bounds origin]
    | .deferred _ => [{}]
    | .scalar expected => [Data.visit bounds origin (.scalar expected) {}]
    | .node expected patterns =>
        ({} :: many sources patterns (fun index => origin.map (fun parent => .structural parent expected index)) 0).map
          (Data.visit bounds origin (.structural expected))
    | .nominal expected patterns =>
        let left := many sources patterns (fun index => some (.nominal (origin.getD (.source bounds.1)) expected index)) 0
        let right := many sources patterns (fun index => some (.nominal (origin.getD (.source bounds.2)) expected index)) 0
        ({} :: (left ++ products left right)).map (Data.visit bounds origin (.nominal expected patterns.length))
  termination_by sizeOf query

  def many (sources : List Nat) : List Query → (Nat → Option Origin) → Nat → List Data
    | [],_,_ => [{}]
    | query :: rest,origins,index => {} ::
        (intervals sources).flatMap (fun bounds => products (one sources query bounds (origins index))
          (many sources rest origins (index+1)))
  termination_by queries _ _ => sizeOf queries
end

private theorem many_empty (sources : List Nat) (queries : List Query) (origins : Nat → Option Origin) (index : Nat) :
    ({} : Data) ∈ many sources queries origins index := by cases queries <;> simp only [many] <;> exact List.mem_cons_self ..

private theorem visited_member {choices : List Data} (member : result ∈ choices) :
    Data.visit bounds origin test result ∈ choices.map (Data.visit bounds origin test) := List.mem_map.mpr ⟨result,member,rfl⟩

private theorem erase_block (state : GeneralNominalState.State) (bounds : Bounds state) : erase state (block bounds) = {} := rfl
private theorem erase_conflict (state : GeneralNominalState.State) (bounds : Bounds state) :
    erase state {conflicts := [bounds]} = {} := rfl
private theorem erase_arity (state : GeneralNominalState.State) (a b : Nat) :
    erase state {arity := [(a,b)]} = {} := rfl

mutual
  theorem inspect_enumerated (state : GeneralNominalState.State) (sources : List Nat)
      (supported : ∀ slot, state.base.source slot ∈ sources) (query : Query)
      (bounds : Bounds state) (origin : Option Origin) :
      erase state (inspect state query bounds origin) ∈ one sources query (interval state bounds) origin := by
    cases query with
    | variables names =>
        simp [inspect,one,erase,captureResult,List.map_map,interval]
    | deferred pattern => simp only [inspect,one,erase_block]; exact List.mem_singleton_self _
    | scalar expected =>
        simp only [inspect,erase_visit,one]
        have finish (report : Report state) (equal : erase state report = {}) :
            Data.visit (interval state bounds) origin (.scalar expected) (erase state report) ∈
              [Data.visit (interval state bounds) origin (.scalar expected) {}] := by rw [equal]; exact List.mem_singleton_self _
        split
        · exact finish _ rfl
        · split
          · split <;> exact finish _ rfl
          · exact finish _ rfl
          · exact finish _ rfl
    | node expected patterns =>
        simp only [inspect,erase_visit,one]
        apply visited_member
        split
        · split
          · exact List.mem_cons_of_mem _ (many_enumerated state sources supported patterns _ _ _)
          · exact List.mem_cons_self ..
        · exact List.mem_cons_self ..
        · exact List.mem_cons_self ..
    | nominal expected patterns =>
        simp only [inspect,erase_visit,one]
        apply visited_member
        split
        · split <;> exact List.mem_cons_self ..
        · split
          · split
            · exact List.mem_cons_self ..
            · split
              · exact List.mem_cons_of_mem _ (List.mem_append_left _ (many_enumerated state sources supported patterns _ _ _))
              · split
                · exact List.mem_cons_self ..
                · split
                  · split
                    · exact List.mem_cons_self ..
                    · rw [erase_append]
                      exact List.mem_cons_of_mem _ (List.mem_append_right _
                        (product_member (many_enumerated state sources supported patterns _ _ _)
                          (many_enumerated state sources supported patterns _ _ _)))
                  · exact List.mem_cons_self ..
          · exact List.mem_cons_self ..
  termination_by sizeOf query

  theorem many_enumerated (state : GeneralNominalState.State) (sources : List Nat)
      (supported : ∀ slot, state.base.source slot ∈ sources) (queries : List Query)
      (bounds : List (Bounds state)) (origins : Nat → Option Origin) (index : Nat) :
      erase state (inspectMany state queries bounds origins index) ∈ many sources queries origins index := by
    cases queries with
    | nil => cases bounds <;> simpa only [inspectMany,erase_arity,erase_empty] using many_empty sources [] origins index
    | cons query queries =>
      cases bounds with
      | nil => simpa only [inspectMany,erase_arity] using many_empty sources (query :: queries) origins index
      | cons head tail =>
        simp only [inspectMany,erase_append,many]
        exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨interval state head,interval_member supported head,
          product_member (inspect_enumerated state sources supported query head (origins index))
            (many_enumerated state sources supported queries tail origins (index+1))⟩)
  termination_by sizeOf queries
end

def lists (values : List α) : Nat → List (List α)
  | 0 => [[]]
  | count+1 => values.flatMap fun head => (lists values count).map (List.cons head)

theorem list_enumerated (values : List α) (entries : List α) (members : ∀ entry ∈ entries, entry ∈ values) :
    entries ∈ lists values entries.length := by
  induction entries with
  | nil => exact List.mem_singleton_self _
  | cons head tail ih =>
      exact List.mem_flatMap.mpr ⟨head,members head (List.mem_cons_self ..),
        List.mem_map.mpr ⟨tail,ih (fun entry member => members entry (List.mem_cons_of_mem _ member)),rfl⟩⟩

def reports (sources : List Nat) (queries : List Query) (arity : Nat) : List Data :=
  (lists (intervals sources) arity).flatMap fun bounds =>
    (many sources queries (fun _ => none) 0).map fun result => {result with checked := bounds ++ result.checked}

theorem report_enumerated (context : GeneralNominalCandidates.Context)
    (declaration : GeneralDeclarations.Declaration) (bounds : List (Bounds context.state))
    (supported : ∀ slot, context.state.base.source slot ∈ sources) :
    erase context.state (GeneralNominalRecursiveCandidates.report context declaration bounds) ∈
      reports sources (GeneralNominalInspection.queries context.state context.interpretation declaration) bounds.length := by
  have listed : bounds.map (interval context.state) ∈ lists (intervals sources) bounds.length := by
    simpa only [List.length_map] using list_enumerated (intervals sources) (bounds.map (interval context.state)) (by
      intro pair member
      obtain ⟨entry,present,rfl⟩ := List.mem_map.mp member
      exact interval_member supported entry)
  refine List.mem_flatMap.mpr ⟨_,listed,List.mem_map.mpr ⟨_,many_enumerated context.state sources supported _ bounds _ 0,?_⟩⟩
  simp [GeneralNominalRecursiveCandidates.report,erase,List.map_append]

end Yulang.GeneralNominalReportEnumeration
