import Yulang.GeneralDictionaryFinishedInspection

/-! Source-preserving refinement of finished finite nominal/variable inspections.
Scalar/structural queries and arbitrary descriptor revision are excluded. -/
namespace Yulang.GeneralDictionaryNestedRefinement
open GeneralNominalInspection (Query Bounds)
open GeneralNominalRecursiveInspection
open GeneralNominalRefinements
open GeneralNominalState (State)
open GeneralDictionaryFinishedRefresh
open GeneralDictionaryRefinementInspectionFacts

mutual
 def NominalOnly : Query → Prop
 | .variables _ => True
 | .nominal _ qs => NominalOnlyMany qs
 | _ => False
 def NominalOnlyMany : List Query → Prop
 | [] => True
 | q :: qs => NominalOnly q ∧ NominalOnlyMany qs
end

def mapBounds (e : Fin a.base.slots → Fin b.base.slots) (x : Bounds a) : Bounds b := (e x.1,e x.2)
def mapCapture (e : Fin a.base.slots → Fin b.base.slots) (x : Capture a) : Capture b :=
  ⟨x.name,mapBounds e x.bounds,x.origin⟩
def mapReport (e : Fin a.base.slots → Fin b.base.slots) (x : Report a) : Report b :=
  ⟨x.captures.map (mapCapture e),x.inspected.map (mapBounds e),x.checked.map (mapBounds e),
   x.blocked.map (mapBounds e),x.conflicts.map (mapBounds e),x.arity,
   x.anchors.map (fun p => (p.1,mapBounds e p.2)),x.tests⟩

variable {a b : State}

theorem map_append (e : Fin a.base.slots → Fin b.base.slots) (x y : Report a) :
 mapReport e (x.append y) = (mapReport e x).append (mapReport e y) := by
 simp [mapReport,Report.append,List.map_append]
theorem map_visit (e : Fin a.base.slots → Fin b.base.slots) (bounds : Bounds a)
 (origin : Option Origin) (test : Test) (x : Report a) :
 mapReport e (Report.visit bounds origin test x) =
 Report.visit (mapBounds e bounds) origin test (mapReport e x) := by
 simp [mapReport,Report.visit,List.map_append,List.map_map,Function.comp_def]

theorem embed_injective (r : Refines a b) : Function.Injective r.base.embed := by
 intro x y eq
 apply a.base.source_injective
 rw [← r.base.source x,← r.base.source y,eq]

theorem typeArguments_map (e : Fin m → Fin n) (xs : List (GeneralNominalState.Parameter m)) :
 typeArguments (xs.map (renameParameter e)) =
 (typeArguments xs).map (List.map (fun p => (e p.1,e p.2))) := by
 induction xs with
 | nil => rfl
 | cons x xs ih =>
   cases x <;> simp [typeArguments,List.mapM_cons,renameParameter] at *
   rw [ih]
   cases h : typeArguments xs <;> simp only [typeArguments] at h <;> rw [h] <;> rfl

mutual
 theorem inspect_refined (a b : State) (r : Refines a b) (q : Query) (bounds : Bounds a)
 (origin : Option Origin) (scope : NominalOnly q) (done : Finished (inspect a q bounds origin)) :
 inspect b q (mapBounds r.base.embed bounds) origin = mapReport r.base.embed (inspect a q bounds origin) := by
 cases q with
 | variables names => simp [inspect,mapReport,mapCapture,mapBounds,List.map_map,Function.comp_def]
 | deferred term => exact False.elim scope
 | scalar base => exact False.elim scope
 | node shape qs => exact False.elim scope
 | nominal name qs =>
   obtain ⟨lower,lo⟩ := finished_nominal_lower a name qs bounds origin done
   obtain ⟨upper,hi⟩ := finished_nominal_upper a name qs bounds origin done
   have low := r.nominals _ _ lo
   have high := r.nominals _ _ hi
   have point : r.base.embed bounds.1 = r.base.embed bounds.2 ↔ bounds.1 = bounds.2 :=
     (embed_injective r).eq_iff
   by_cases ln : lower.declaration.name = name
   · cases argsEq : typeArguments lower.arguments with
     | none => simp [inspect,lo,ln,argsEq,Finished,Report.visit,block] at done
     | some args =>
       by_cases eq : bounds.1 = bounds.2
       · have ih := inspectMany_refined a b r qs args
           (fun i => some (.nominal (origin.getD (.source (a.base.source bounds.1))) name i)) 0 scope
           (by simpa only [inspect,lo,ln,argsEq,ite_eq_left eq,ite_true,finished_visit] using done)
         simp only [inspect,lo,mapBounds,low,renameDescriptor,typeArguments_map,
           point,r.base.source,ln,argsEq,ite_eq_left eq,ite_true,Option.map_some]
         rw [map_visit]
         congr 1
       · by_cases un : upper.declaration.name = name
         · cases targetsEq : typeArguments upper.arguments with
           | none => simp [inspect,lo,hi,ln,argsEq,eq,un,targetsEq,Finished,Report.visit,block] at done
           | some targets =>
             have both := (finished_append _ _).mp (show Finished _ from
               (by simpa only [inspect,lo,hi,ln,argsEq,eq,ite_false,un,targetsEq,ite_true,finished_visit] using done))
             have left := inspectMany_refined a b r qs args
               (fun i => some (.nominal (origin.getD (.source (a.base.source bounds.1))) name i)) 0 scope both.1
             have right := inspectMany_refined a b r qs targets
               (fun i => some (.nominal (origin.getD (.source (a.base.source bounds.2))) name i)) 0 scope both.2
             simp only [inspect,lo,hi,mapBounds,low,high,renameDescriptor,typeArguments_map,
               point,r.base.source,ln,argsEq,eq,un,targetsEq,ite_true,ite_false,Option.map_some]
             rw [map_visit,map_append]
             congr 1
             congr 1
         · simp [inspect,lo,hi,ln,argsEq,eq,un,Finished,Report.visit] at done
   · simp [inspect,lo,ln,Finished,Report.visit] at done
 termination_by sizeOf q
 theorem inspectMany_refined (a b : State) (r : Refines a b) (qs : List Query) (bounds : List (Bounds a))
 (origins : Nat → Option Origin) (index : Nat) (scope : NominalOnlyMany qs)
 (done : Finished (inspectMany a qs bounds origins index)) :
 inspectMany b qs (bounds.map (mapBounds r.base.embed)) origins index =
 mapReport r.base.embed (inspectMany a qs bounds origins index) := by
 cases qs with
 | nil => cases bounds <;> simp [inspectMany,mapReport]
 | cons q qs =>
   cases bounds with
   | nil => simp [inspectMany,mapReport]
   | cons bound bounds =>
     have both := (finished_append _ _).mp (show Finished ((inspect a q bound (origins index)).append (inspectMany a qs bounds origins (index+1))) from (by simpa only [inspectMany] using done))
     rw [List.map_cons,inspectMany,inspectMany,
       inspect_refined a b r q bound (origins index) scope.1 both.1,
       inspectMany_refined a b r qs bounds origins (index+1) scope.2 both.2,map_append]
 termination_by sizeOf qs
end

theorem bindings_map (r : Refines a b) (report : Report a) :
 bindings b (mapReport r.base.embed report) = bindings a report := by
 simp [bindings,mapReport,mapCapture,mapBounds,List.map_map,Function.comp_def,r.base.source]

theorem origins_map (e : Fin a.base.slots → Fin b.base.slots) (report : Report a)
 (current : Capture b) (member : current ∈ (mapReport e report).captures) :
 ∃ old ∈ report.captures, old.name = current.name ∧ old.origin = current.origin := by
 obtain ⟨old,mem,eq⟩ := List.mem_map.mp member
 subst current
 exact ⟨old,mem,rfl,rfl⟩

theorem finished_map (e : Fin a.base.slots → Fin b.base.slots) (report : Report a) :
 Finished (mapReport e report) ↔ Finished report := by
 simp [Finished,mapReport]

theorem bindings_refined (a b : State) (r : Refines a b) (qs : List Query)
 (bounds : List (Bounds a)) (origins : Nat → Option Origin) (index : Nat)
 (scope : NominalOnlyMany qs) (done : Finished (inspectMany a qs bounds origins index)) :
 bindings b (inspectMany b qs (bounds.map (mapBounds r.base.embed)) origins index) =
 bindings a (inspectMany a qs bounds origins index) := by
 rw [inspectMany_refined a b r qs bounds origins index scope done,bindings_map]

theorem origins_refined (a b : State) (r : Refines a b) (qs : List Query)
 (bounds : List (Bounds a)) (origins : Nat → Option Origin) (index : Nat)
 (scope : NominalOnlyMany qs) (done : Finished (inspectMany a qs bounds origins index))
 (current : Capture b)
 (member : current ∈ (inspectMany b qs (bounds.map (mapBounds r.base.embed)) origins index).captures) :
 ∃ old ∈ (inspectMany a qs bounds origins index).captures,
 old.name = current.name ∧ old.origin = current.origin := by
 rw [inspectMany_refined a b r qs bounds origins index scope done] at member
 exact origins_map _ _ _ member

end Yulang.GeneralDictionaryNestedRefinement
