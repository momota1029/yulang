import Yulang.GeneralMixedFullControlCertificate306
import Yulang.GeneralFiniteRawPresentation306

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedFullControlPresentation306
open GeneralMixedFullControlCode306 (Code code)
open GeneralMixedFullControlUnlabelled306 (codes targets all_codes raw_exact classify)
open GeneralMixedFullControlMinimalRaw306 (Reach RawBisim raw_classes_bisim any_raw_bisim_respects_classes)
open GeneralMixedFullControlModelClasses306 (key key_bisim key_preserves_models necessary phase_iff_models)
open GeneralMixedFullControlCompiledQuotient306 (code_closed uncolored colored)
open GeneralDictionaryOutputDepth252 (roles initial registry root)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralFiniteRawPresentation306 (Presentation StrongRaw)

theorem present {β : Type} (obs : Code → β) :
    Presentation Reach (Step registry root) code (fun s => obs (code s)) targets obs codes := by
  refine ⟨code_closed,(fun s _ => all_codes (code s)),?_,(fun _ _ => rfl),?_⟩
  · rintro s t ⟨n,before⟩ action
    exact ⟨n+1,.more before action⟩
  · rintro s ⟨n,before⟩ goal
    unfold targets
    rw [List.mem_filter]
    exact ⟨fun h => (raw_exact before goal).mp h.2,
      fun h => ⟨all_codes goal,(raw_exact before goal).mpr h⟩⟩

theorem erase_color {β : Type} {obs : State roles → β} {rel : State roles → State roles → Prop}
    (strong : StrongRaw Reach (Step registry root) obs rel) : RawBisim rel :=
  fun s t hs ht h => (strong s t hs ht h).2

theorem uncolored_exact {s t : State roles} (hs : Reach s) (ht : Reach t) :
    uncolored.project (code s) = uncolored.project (code t) ↔ classify (code s) = classify (code t) := by
  constructor
  · intro h
    have b := GeneralFiniteRawPresentation306.stable (present (fun _ => ()))
    exact any_raw_bisim_respects_classes (erase_color b) hs ht h
  · intro h
    have b : StrongRaw Reach (Step registry root) (fun _ => ())
        (fun a b => classify (code a) = classify (code b)) :=
      fun a b ha hb same => ⟨rfl,raw_classes_bisim a b ha hb same⟩
    exact GeneralFiniteRawPresentation306.minimal (present (fun _ => ())) b hs ht h

theorem colored_exact {s t : State roles} (hs : Reach s) (ht : Reach t) :
    colored.project (code s) = colored.project (code t) ↔ key (code s) = key (code t) := by
  constructor
  · intro h
    have b := GeneralFiniteRawPresentation306.stable (present Code.installed)
    apply necessary (erase_color b) ?_ hs ht h
    intro a b ha hb eq
    obtain ⟨na,ha⟩ := ha
    obtain ⟨nb,hb⟩ := hb
    exact (phase_iff_models ha hb).mp
      (GeneralFiniteRawPresentation306.color_preserved (present Code.installed) ⟨na,ha⟩ ⟨nb,hb⟩ eq)
  · intro h
    have b : StrongRaw Reach (Step registry root) (fun a => (code a).installed)
        (fun a b => key (code a) = key (code b)) :=
      fun a b ha hb same => ⟨congrArg Prod.fst same,key_bisim a b ha hb same⟩
    exact GeneralFiniteRawPresentation306.minimal (present Code.installed) b hs ht h

end Yulang.GeneralMixedFullControlPresentation306
