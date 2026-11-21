import Yulang.GeneralDeclarativeTermWalk322
import Yulang.GeneralDeclarativeSourceNames321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTermOccurrences322
open GeneralDeclarativeTermWalk322 (Occurrence Walk WalkMany)
open GeneralDeclarativeTraceNames321 (names namesMany)
open GeneralNominalMaterialization (Mode)

def Positions (mode : Mode) (seen : List Occurrence) (expected : List Nat) : Prop :=
  seen.map Occurrence.binder = expected ∧
    ∀ use ∈ seen, use.mode = mode ∨ use.mode = .actual

theorem Positions.append {mode : Mode} {s t : List Occurrence} {a b : List Nat}
    (first : Positions mode s a) (last : Positions mode t b) :
    Positions mode (s++t) (a++b) := by
  refine ⟨by rw [List.map_append,first.1,last.1],?_⟩
  intro use seen
  exact (List.mem_append.mp seen).elim (first.2 use) (last.2 use)

theorem positions (walk : Walk mode source pattern seen) : Positions mode seen (names pattern) :=
  Walk.rec
    (motive_1 := fun mode _ pattern seen _ => Positions mode seen (names pattern))
    (motive_2 := fun mode _ patterns seen _ => Positions mode seen (namesMany patterns))
    (by
      intro mode source name
      exact ⟨rfl,(fun _ h => by cases List.mem_singleton.mp h; exact .inl rfl)⟩)
    (fun _ ih => ih)
    (fun _ ih => ⟨ih.1,fun use h => .inr ((ih.2 use h).elim id id)⟩)
    (fun _ _ ih jh => ih.append jh)
    (fun _ ih => ih)
    (fun _ _ ih jh => ih.append jh)
    (by exact ⟨rfl,fun _ h => by cases h⟩)
    (fun _ _ ih jh => ih.append jh)
    walk

theorem actual_positions (read : Walk .actual source code seen) :
    seen.map Occurrence.binder = names code ∧ ∀ o ∈ seen, o.mode = .actual :=
  ⟨(positions read).1,fun o h => ((positions read).2 o h).elim id id⟩

theorem source_binders {p : GeneralDeclarationPatterns.Pattern}
    (translation : GeneralNominalCenteredHeadMatExpressions.translate c interp p = some code)
    (read : Walk .actual source code seen) :
    seen.map Occurrence.binder = p.variables ∧
      ∀ name ∈ p.variables, ∃ found ∈ seen, found.binder = name ∧ found.mode = .actual := by
  have elems : seen.map Occurrence.binder = p.variables :=
    (actual_positions read).1.trans (GeneralDeclarativeSourceNames321.actual_names p translation)
  refine ⟨elems,?_⟩
  intro name h
  rw [← elems] at h
  obtain ⟨found,member,name⟩ := List.mem_map.mp h
  exact ⟨found,member,name,(actual_positions read).2 found member⟩

end Yulang.GeneralDeclarativeTermOccurrences322
