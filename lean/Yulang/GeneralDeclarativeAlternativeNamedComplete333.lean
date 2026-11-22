import Yulang.GeneralDeclarativeAlternativeNamed333

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAlternativeNamedComplete333
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeAlternativeView333 (Index)
open GeneralDeclarativeAlternativeNeeds333 (Need Planned Eventually eventually_pair eventually_one eventually_step finiteIndex)
open GeneralDeclarativeAlternativeNamed333 (Result Arguments named namedArgs alternate branch source_shape Shape)
open GeneralDeclarativeTrace321 (Trace TraceArgs Occurrence)

abbrev Present (src : Index s) (h : Trace s mode arg code seen) :=
  Eventually (fun f => (⟨seen,h⟩ : Result s mode arg code) ∈ named src f mode arg code)
abbrev PresentArgs (src : Index s) (h : TraceArgs s mode args code seen) :=
  Eventually (fun f => (⟨seen,h⟩ : Arguments s mode args code) ∈ namedArgs src f mode args code)

/-- Keep the old exact named observer as an independent source rule.
All its authorized spellings are recovered in a finite packet too,
including a named record whose captured residual is still opaque. -/
theorem named_plan {s : State} (trace : Trace s mode arg code seen) :
    Planned (fun src : Index s => Present src trace) := by
  refine Trace.rec
    (motive_1 := fun _ _ _ _ h => Planned (fun src => Present src h))
    (motive_2 := fun _ _ _ _ h => Planned (fun src => PresentArgs src h))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ trace
  · intro mode n binder
    exact Planned.pure fun _ => eventually_one fun _ => List.mem_cons_self
  · intro name owner tag mode args targets seen link stored prior ih
    let needed : Need s := ⟨name,⟨owner,(Shape.primitive tag args).raw,link,stored⟩⟩
    refine ih.add needed (fun src listed available => eventually_step available fun f hw => ?_)
    unfold named
    refine List.mem_flatMap.mpr ⟨needed.2,listed,?_⟩
    change _ ∈ alternate (named src f) (namedArgs src f) mode _ needed.2
    simp only [alternate,needed,source_shape,branch]
    exact List.mem_map.mpr ⟨⟨seen,prior⟩,hw,rfl⟩
  · intro name owner tag args targets seen mode link stored prior ih
    let needed : Need s := ⟨name,⟨owner,(Shape.nominal tag args).raw,link,stored⟩⟩
    refine ih.add needed (fun src listed available => eventually_step available fun f hw => ?_)
    unfold named
    refine List.mem_flatMap.mpr ⟨needed.2,listed,?_⟩
    change _ ∈ alternate (named src f) (namedArgs src f) mode _ needed.2
    simp only [alternate,needed,source_shape,branch]
    exact List.mem_map.mpr ⟨⟨seen,prior⟩,hw,rfl⟩
  · intro name owner tag a b mode one xs two ys link stored prior last ih jh
    let needed : Need s := ⟨name,⟨owner,(Shape.record tag a b).raw,link,stored⟩⟩
    refine (ih.both jh).add needed (fun src listed ready =>
      eventually_step (eventually_pair ready.1 ready.2) fun f hw => ?_)
    unfold named
    refine List.mem_flatMap.mpr ⟨needed.2,listed,?_⟩
    change _ ∈ alternate (named src f) (namedArgs src f) mode _ needed.2
    simp only [alternate,needed,source_shape,branch]
    exact List.mem_flatMap.mpr ⟨⟨xs,prior⟩,hw.1,List.mem_map.mpr ⟨⟨ys,last⟩,hw.2,rfl⟩⟩
  · intro name owner tag a mode exp seen link stored prior ih
    let needed : Need s := ⟨name,⟨owner,(Shape.variant tag a).raw,link,stored⟩⟩
    refine ih.add needed (fun src listed available => eventually_step available fun f hw => ?_)
    unfold named
    refine List.mem_flatMap.mpr ⟨needed.2,listed,?_⟩
    change _ ∈ alternate (named src f) (namedArgs src f) mode _ needed.2
    simp only [alternate,needed,source_shape,branch]
    exact List.mem_map.mpr ⟨⟨seen,prior⟩,hw,rfl⟩
  · intro name owner a b mode one xs two ys link stored prior last ih jh
    let needed : Need s := ⟨name,⟨owner,(Shape.join a b).raw,link,stored⟩⟩
    refine (ih.both jh).add needed (fun src listed ready =>
      eventually_step (eventually_pair ready.1 ready.2) fun f hw => ?_)
    unfold named
    refine List.mem_flatMap.mpr ⟨needed.2,listed,?_⟩
    change _ ∈ alternate (named src f) (namedArgs src f) mode _ needed.2
    simp only [alternate,needed,source_shape,branch]
    exact List.mem_flatMap.mpr ⟨⟨xs,prior⟩,hw.1,List.mem_map.mpr ⟨⟨ys,last⟩,hw.2,rfl⟩⟩
  · intro mode
    exact Planned.pure fun _ => eventually_one fun _ => List.mem_cons_self
  · intro mode n target xs ns targets ys h k ih jh
    apply (ih.both jh).map
    intro src ready
    apply eventually_step (eventually_pair ready.1 ready.2)
    intro f both
    unfold namedArgs
    exact List.mem_flatMap.mpr ⟨⟨xs,h⟩,both.1,List.mem_map.mpr ⟨⟨ys,k⟩,both.2,rfl⟩⟩

theorem named_finite {s : State} (trace : Trace s mode arg code seen) :
    ∃ packet : List (Need s), Present (finiteIndex packet) trace :=
  (named_plan trace).finite

end Yulang.GeneralDeclarativeAlternativeNamedComplete333
