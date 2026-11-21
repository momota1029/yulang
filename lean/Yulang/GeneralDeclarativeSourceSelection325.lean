import Yulang.GeneralDeclarativeFrameReadback325
import Yulang.GeneralDeclarativeNFClassify324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeSourceSelection325
open GeneralDeclarations (Checked Declaration Registry)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativePriority321 (Local Visible Candidates selected_generated)
open GeneralDeclarativeFrameReadback325 (Recorded sourceNames complete_read)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeOutputRequests323 (child_declared)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeNFComplete324 (local_sound produces)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralNominalInspection (Interpretation)
open CommonRoleOutermostResolver (Frontier Tree Dictionary Classify Resolves Summarizes All₂ Result)

def Source (s : State) (r : Registry) (i : Interpretation)
    {complete : Nat → Prop} (support : Supported s complete) (d : Demand)
    (impl : Declaration) (kids : List Demand) : Prop :=
  ∃ base place, Recorded s r i support d impl base place ∧
    children impl (sourceNames impl place base) place = kids

abbrev Rule (s : State) (r : Registry) (i : Interpretation)
    {complete : Nat → Prop} (support : Supported s complete) (tests : Candidates) :=
  Local s r i support tests (Source s r i support)

theorem map_generated (change : ∀ d impl, Visible r d impl → ∀ kids, first d impl kids → last d impl kids)
    (given : Local s r i support tests first d result) :
    Local s r i support tests last d result := by
  cases given with
  | unsupported h k => exact .unsupported h k
  | recursive h k => exact .recursive h k
  | unresolved h k w => exact .unresolved h k w
  | noCandidate h k w n => exact .noCandidate h k w n
  | ambiguous h k w a b two => exact .ambiguous h k w a b two
  | selected h k w win unique g => exact .selected h k w win unique (change _ _ win.1 _ g)

theorem agrees_if_covered (coverage : ∀ d impl, Visible r d impl →
      ∀ kids, first d impl kids ↔ last d impl kids) :
    Local s r i support tests first d result ↔ Local s r i support tests last d result :=
  ⟨map_generated (fun d decl v kids => (coverage d decl v kids).mp),
   map_generated (fun d decl v kids => (coverage d decl v kids).mpr)⟩

theorem approved_priority_unchanged {s : State} {support : Supported s complete} (checked : Checked r)
    (selected : Rule s r i support tests d result) :
    GeneralDeclarativeNFClassify324.Rule s r i support tests d result := by
  apply map_generated ?_ selected
  rintro demand impl ⟨visible,_⟩ kids ⟨base,place,source,fixed⟩
  obtain ⟨read,body,_⟩ := complete_read checked visible source
  exact ⟨sourceNames impl place base,place,fixed,read,body⟩

theorem actual_local_compiler {s : State} {support : Supported s complete} (checked : Checked r)
    (declared : Declared r d) (chosen : Rule s r i support tests d (.selected key kids)) :
    ∃ impl names place, impl.id = key ∧ impl ∈ r.declarations ∧ children impl names place = kids ∧
      GeneralDeclarativeCompileLists321.Result s
        (GeneralDeclarativeNFComplete324.facts r i names.input impl d kids) := by
  obtain ⟨impl,rfl,⟨⟨visible,role⟩,_⟩,base,place,source,rfl⟩ := selected_generated chosen
  obtain ⟨read,body,stable⟩ := complete_read checked visible source
  exact ⟨impl,sourceNames impl place base,place,rfl,visible,rfl,
    produces checked visible role declared body read stable⟩

mutual
theorem tree {s : State} {support : Supported s complete}
    (checked : Checked r) (declared : Declared r d) (valid : Models s m)
    (diag : Tree) (dict : Dictionary) (ran : Resolves (Rule s r i support tests) d diag)
    (done : Summarizes diag (.selected dict)) : Evidence r i m d dict := by
  cases ran with
  | pending _ => cases done
  | rejected _ => cases done
  | ambiguous _ => cases done
  | selected own childrenRead =>
    obtain ⟨impl,rfl,⟨⟨visible,role⟩,_⟩,base,place,source,rfl⟩ := selected_generated own
    obtain ⟨read,body,stable⟩ := complete_read checked visible source
    cases done with
    | selected summaries combined =>
      cases combined with
      | selected linked =>
        subst_vars
        exact .node ⟨impl,(sourceNames impl place base).input,rfl,
          local_sound checked visible role declared body read stable m valid⟩
          (forest checked (fun _ used => child_declared checked visible used) valid _ _ childrenRead summaries)
termination_by sizeOf diag

theorem forest {s : State} {support : Supported s complete}
    (checked : Checked r) (declared : ∀ d ∈ ds, Declared r d) (valid : Models s m)
    (diags : List Tree) (dicts : List Dictionary)
    (ran : All₂ (Resolves (Rule s r i support tests)) ds diags)
    (done : All₂ Summarizes diags (dicts.map Result.selected)) : All₂ (Evidence r i m) ds dicts := by
  cases dicts with
  | nil => cases done; cases ran; exact .nil
  | cons first rest =>
    cases done with
    | cons won future =>
      cases ran with
      | cons firstRead restRead =>
        exact .cons (tree checked (declared _ List.mem_cons_self) valid _ _ firstRead won)
          (forest checked (fun d h => declared d (List.mem_cons_of_mem _ h)) valid _ _ restRead future)
termination_by sizeOf diags
end

/-- On this source slice, stability of a whole external relation and
an abstract compiled-body coverage are no longer inputs. Each frame
contains a genuine ordinary result of its normalized source emission. -/
theorem sound {s : State} {support : Supported s complete} (checked : Checked r)
    (declared : Declared r d) (valid : Models s m)
    (chosen : Classify (Rule s r i support tests) d (.selected dict)) : Evidence r i m d dict := by
  obtain ⟨diag,ran,done⟩ := chosen
  exact tree checked declared valid diag dict ran done

end Yulang.GeneralDeclarativeSourceSelection325
