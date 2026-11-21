import Yulang.GeneralDeclarativeHiddenWhere324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeHiddenWhereProof324
open GeneralDeclarativeHiddenWhere324
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation raw normal normCode empty normal_compiles)
open GeneralDeclarativeHiddenState324 (direct)
open GeneralDeclarativeHiddenProbe324 (root_bounds)
open GeneralDeclarativeExampleSource320 (point int)
open GeneralDeclarativeNFHead324 (Scan produces fact)
open GeneralDeclarativeNFComplete324 (ReadBack local_sound)
open GeneralDeclarativeNFNode324 (BodyCoverage)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeAssembly320 (Meaning)
open GeneralDeclarativeHead320 (Models Equation)
open GeneralDeclarativeEntailment320 (literal)
open GeneralDeclarativeModelStable324 (StableUnder stable_exact)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeRecordWalk323 (closed_record)
open GeneralDeclarativeExactWalk323 (of_rigid)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (record emptyRecord)
open CommonRoleOutermostResolver (All₂ Dictionary)

theorem root_read : ReadBack state registry interpretation root parent capture place := by
  refine ⟨.cons ⟨root_bounds _ _,?_⟩ .nil,fun _ _ => root_bounds _ 3,
    fun _ bad => False.elim (List.not_mem_nil bad),?_⟩
  · have view : Scan state catalogue interpretation (point 0) raw [⟨0,.actual,.variable 3⟩] :=
      ⟨root_bounds _ _,direct,normCode,literal List.mem_cons_self,normal_compiles,
        closed_record (xs := [(7,.variable 3)]) (ys := [(7,.variable 0)])
          (.cons (of_rigid .capture) .nil) (by simp)⟩
    apply produces view
    intro m _ v there
    cases List.mem_singleton.mp there
    exact eqv_refl (m 3).1
  · intro c member
    cases List.mem_singleton.mp member
    exact where_read

theorem child_read : ReadBack state registry interpretation child implementation capture place := by
  refine ⟨.cons ⟨root_bounds _ 3,⟨[⟨3,.variable 3⟩],rfl,?_⟩⟩ .nil,fun _ _ => root_bounds _ 3,
    fun _ bad => False.elim (List.not_mem_nil bad),fun _ bad => False.elim (List.not_mem_nil bad)⟩
  intro row here m _
  cases List.mem_singleton.mp here
  exact eqv_refl _

theorem root_declared : Declared registry root := by intro out h; cases List.mem_singleton.mp h; exact ⟨none,rfl⟩
theorem child_declared : Declared registry child := by intro out h; cases List.mem_singleton.mp h; exact ⟨none,rfl⟩

theorem root_covered : BodyCoverage registry interpretation root parent := by
  intro out there body source
  cases List.mem_singleton.mp there
  cases source with
  | explicit eq present _ => cases List.mem_singleton.mp present; trivial
  | default rhs _ impossible =>
    change some (none : Option Yulang.Roles.Term) = some (some rhs) at impossible
    cases Option.some.inj impossible

theorem child_covered : BodyCoverage registry interpretation child implementation := by
  intro out there body source
  cases List.mem_singleton.mp there
  cases source with
  | explicit eq present _ =>
    cases List.mem_singleton.mp present
    exact ⟨trivial,⟨⟨⟨[],4⟩,rfl,rfl,.inl ⟨.emptyRecord,rfl,rfl⟩⟩,trivial⟩⟩
  | default rhs _ impossible =>
    change some (none : Option Yulang.Roles.Term) = some (some rhs) at impossible
    cases Option.some.inj impossible

theorem root_stable : StableUnder state (SourceEquation registry interpretation root parent capture.input) := by
  apply stable_exact.mpr
  rintro eq ⟨out,there,body,source,nf,written,rfl⟩
  cases List.mem_singleton.mp there
  cases source with
  | explicit eq used _ =>
    cases List.mem_singleton.mp used
    have same : .variable 0 = nf := Option.some.inj written
    subst nf
    exact literal (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  | default rhs _ impossible =>
    change some (none : Option Yulang.Roles.Term) = some (some rhs) at impossible
    cases Option.some.inj impossible

theorem child_stable : StableUnder state (SourceEquation registry interpretation child implementation capture.input) := by
  apply stable_exact.mpr
  rintro eq ⟨out,there,body,source,nf,written,rfl⟩
  cases List.mem_singleton.mp there
  cases source with
  | explicit eq used _ =>
    cases List.mem_singleton.mp used
    have same : normCode = nf := Option.some.inj written
    subst nf
    exact literal (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  | default rhs _ impossible =>
    change some (none : Option Yulang.Roles.Term) = some (some rhs) at impossible
    cases Option.some.inj impossible

abbrev dict : Dictionary := .node parent.id [.node implementation.id []]

theorem receiver (m : Assignment) (valid : Models state m) :
    Evidence registry interpretation m root dict := by
  have rootMeaning := local_sound checked List.mem_cons_self rfl root_declared root_covered root_read root_stable m valid
  rw [exact_emission] at rootMeaning
  have childMeaning := local_sound checked (List.mem_cons_of_mem _ List.mem_cons_self) rfl
    child_declared child_covered child_read child_stable m valid
  exact .node ⟨parent,capture.input,rfl,rootMeaning⟩
    (.cons (.node ⟨implementation,capture.input,rfl,childMeaning⟩ .nil) .nil)

def model : Assignment := fun n =>
  (if n = 0 ∨ n = 55 then record 7 int emptyRecord else int,Common.rowEmpty)

theorem inhabited : Models state model ∧ Evidence registry interpretation model root dict := by
  have valid : Models state model := by
    refine ⟨⟨PresenceNormalForm.all_nil _ _,fun _ bad => False.elim (List.not_mem_nil bad)⟩,?_⟩
    intro row there
    change row ∈ [⟨0,direct⟩,⟨3,.primitive (.scalar .int) []⟩,⟨6,.variable 3⟩,
      GeneralDeclarativeHiddenWhere324.row] at there
    simp only [List.mem_cons,List.not_mem_nil,or_false] at there
    rcases there with rfl|rfl|rfl|rfl <;> exact eqv_refl _
  exact ⟨valid,receiver model valid⟩

end Yulang.GeneralDeclarativeHiddenWhereProof324
