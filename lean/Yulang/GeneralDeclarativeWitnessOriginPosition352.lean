import Yulang.GeneralDeclarativeWitnessMixedRelease352

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessOriginPosition352
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeWitnessOrigins350 (Table Attached visible)
open GeneralDeclarativeWitnessIdentity351 (Owned Key table)
open GeneralDeclarativeWitnessTagSources351 (Ref offer)
open GeneralDeclarativeWitnessMixedRelease352 (Problem Wire Accepted downstream)
open GeneralDeclarativeWitnessTree349 (Report)
open GeneralDeclarativeWitnessForest350 (Fixed)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeEntailment320 (Holds)

def releasedRows (owned : List Owned) (keys : List Key) : List Owned :=
  owned.filter fun w => keys.contains w.key

private theorem visible_zip (xs : List Owned) (keys : List Key) (start : Nat) :
    (((xs.zipIdx start).map (fun (r,i) => (r.equation,i))).filter
      (fun q => ((xs.zipIdx start).filter (fun ref => keys.contains ref.1.key)).map Prod.snd |>.contains q.2)).map Prod.fst =
      (releasedRows xs keys).map Owned.equation := by
  -- zipIdx keys are distinct even when the original rows are identical.
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih =>
    rw [List.zipIdx_cons]
    have beyond {i : Nat} (used : i ∈ (xs.zipIdx (start+1)).map Prod.snd) : start < i := by
      obtain ⟨⟨r,j⟩,present,equal⟩ := List.mem_map.mp used
      subst i
      obtain ⟨n,atIndex⟩ := List.mem_iff_getElem?.mp present
      rw [List.getElem?_zipIdx] at atIndex
      cases src : xs[n]? with
      | none => simp [src] at atIndex
      | some v =>
        simp only [src,Option.map_some,Option.some.injEq,Prod.mk.injEq] at atIndex
        omega
    have restricted (i : Nat) (h : i ∈ (((xs.zipIdx (start+1)).filter (fun ref => keys.contains ref.1.key)).map Prod.snd)) :
        i ∈ (xs.zipIdx (start+1)).map Prod.snd := by
      obtain ⟨q,qin,rfl⟩ := List.mem_map.mp h
      exact List.mem_map_of_mem (List.mem_filter.mp qin).1
    have excluded : (((xs.zipIdx (start+1)).filter (fun ref => keys.contains ref.1.key)).map Prod.snd).contains start = false := by
      cases h : (((xs.zipIdx (start+1)).filter (fun ref => keys.contains ref.1.key)).map Prod.snd).contains start with
      | false => rfl
      | true => exact False.elim ((Nat.lt_irrefl start) (beyond (restricted _ ((List.contains_iff_mem).mp h))))
    have tailFilter :
        (((xs.zipIdx (start+1)).map (fun (r,i) => (r.equation,i))).filter
          (fun q => q.2 == start || (((xs.zipIdx (start+1)).filter (fun ref => keys.contains ref.1.key)).map Prod.snd).contains q.2)) =
        (((xs.zipIdx (start+1)).map (fun (r,i) => (r.equation,i))).filter
          (fun q => (((xs.zipIdx (start+1)).filter (fun ref => keys.contains ref.1.key)).map Prod.snd).contains q.2)) := by
      apply List.filter_congr
      intro q present
      obtain ⟨pair,pairIn,equal⟩ := List.mem_map.mp present
      cases equal
      have before : pair.2 ≠ start := Nat.ne_of_gt (beyond (List.mem_map_of_mem pairIn))
      simp [before]
    cases release : keys.contains x.key
    · simp only [releasedRows,List.map_cons,List.filter_cons,release,Bool.false_eq_true,ite_false,
        excluded]
      exact ih (start+1)
    · have tailRewrite :
          (((xs.zipIdx (start+1)).map (fun (r,i) => (r.equation,i))).filter
            (fun q => (start :: (((xs.zipIdx (start+1)).filter
              (fun ref => keys.contains ref.1.key)).map Prod.snd)).contains q.2)) =
          (((xs.zipIdx (start+1)).map (fun (r,i) => (r.equation,i))).filter
            (fun q => (((xs.zipIdx (start+1)).filter (fun ref => keys.contains ref.1.key)).map Prod.snd).contains q.2)) := by
        simpa only [List.contains_cons] using tailFilter
      simp only [releasedRows,List.map_cons,List.filter_cons,release,ite_true,
        List.contains_cons,beq_self_eq_true,Bool.true_or]
      simp only [List.contains_cons] at tailRewrite
      rw [tailRewrite]
      exact congrArg (List.cons x.equation) (ih (start+1))

theorem visible_exact (authored : List Equation) (owned : List Owned) (keys : List Key) :
    visible (table authored owned keys) = authored ++ (releasedRows owned keys).map Owned.equation := by
  unfold visible table
  simp only
  rw [visible_zip owned keys 0]

inductive Location where
  | authored (equation : Equation)
  | published (owned : Owned)
deriving DecidableEq

def Location.equation : Location → Equation
  | .authored e => e
  | .published w => w.equation

def location (authored : List Equation) (owned : List Owned) (keys : List Key) (index : Nat) :
    Option Location :=
  if index < authored.length then authored[index]?.map .authored
  else (releasedRows owned keys)[index-authored.length]?.map .published

theorem location_exact (authored : List Equation) (owned : List Owned) (keys : List Key) (index : Nat) :
    (location authored owned keys index).map Location.equation = (visible (table authored owned keys))[index]? := by
  rw [visible_exact,List.getElem?_append]
  by_cases h : index < authored.length
  · simp only [location,h,ite_true,Option.map_map]
    cases authored[index]? <;> rfl
  · cases e : (releasedRows owned keys)[index-authored.length]? <;>
      simp [location,h,e,Location.equation,List.getElem?_map]

theorem released_exact {author : List Equation} {owned : List Owned} {keys : List Key} {i : Nat}
    {out : Owned} (atIndex : location author owned keys i = some (.published out)) :
    out ∈ owned ∧ out.key ∈ keys := by
  unfold location at atIndex
  split at atIndex
  · simp at atIndex
  · obtain ⟨e,hit,equal⟩ := Option.map_eq_some_iff.mp atIndex
    cases equal
    obtain ⟨seen,written⟩ := List.mem_filter.mp (List.mem_iff_getElem?.mpr ⟨_,hit⟩)
    exact ⟨seen,(List.contains_iff_mem).mp written⟩

theorem actual_selected_origin {s : State} {t : Table} {own : Attached s t}
    {root : Nat} {w : Ref} {o}
    (accepted : offer own root w = some o) :
    (visible t)[w.index]? = some ⟨o.owner,o.rhs⟩ := by
  unfold offer at accepted
  split at accepted
  · cases accepted
  · rename_i e found
    rw [found]
    cases linked : GeneralDeclarativeWitnessReleased350.link own root e.left w.alias with
    | none => simp [linked] at accepted
    | some eqv =>
      simp only [linked] at accepted
      cases accepted
      cases e
      rfl

/-- A consumed position in the released suffix identifies the independently
computed compiler row, exact owner/version/write/target and original model.
No equality-based search or anonymous release is used. -/
theorem used_released {p : Problem} {active : List GeneralDeclarativeWitnessIdentity351.Stamp}
    {wire : Wire} {report : Report} (a : Accepted p active wire report)
    (root : Nat) (ref : Ref) {o}
    (found : offer a.consumer.global.live root ref = some o)
    (later : p.publisher.authored.length ≤ ref.index)
    (m : Assignment) (fit : Models p.publisher.roles.current m) :
    ∃ row ∈ a.prior.owned, row.key ∈ p.publisher.releases ∧
      row.equation = ⟨o.owner,o.rhs⟩ ∧
      ∃ loc ∈ p.publisher.required, ∃ block ∈ a.prior.producer.diagnostic.fixed,
        block.path = loc.producer.path ∧ block.demand.role = loc.producer.role ∧
        block.equations[loc.ordinal]? = some row.equation ∧
        row.key = ⟨loc.producer.path,loc.producer.role,loc.producer.version,loc.ordinal,row.equation.left⟩ ∧
        Holds m row.equation := by
  have eqn := actual_selected_origin found
  change (visible (table p.publisher.authored a.prior.owned p.publisher.releases))[ref.index]? =
    some ⟨o.owner,o.rhs⟩ at eqn
  have exactLocation := location_exact p.publisher.authored a.prior.owned p.publisher.releases ref.index
  rw [eqn] at exactLocation
  obtain ⟨whereAt,whereFrom,eq⟩ := Option.map_eq_some_iff.mp exactLocation
  cases h : (releasedRows a.prior.owned p.publisher.releases)[ref.index-p.publisher.authored.length]? with
  | none => simp [location,Nat.not_lt_of_ge later,h] at whereFrom
  | some y =>
    have matched : whereAt = .published y := by simpa [location,Nat.not_lt_of_ge later,h] using whereFrom.symm
    subst whereAt
    obtain ⟨member,release⟩ := released_exact whereFrom
    exact ⟨y,member,release,eq,GeneralDeclarativeWitnessMixedRelease352.actual_writes a m fit y member⟩

end Yulang.GeneralDeclarativeWitnessOriginPosition352
