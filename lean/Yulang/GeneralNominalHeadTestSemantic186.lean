import Yulang.GeneralNominalHeadCandidateSemantic186

/-! Actual head tests transport along semantic centers, including empty
projection observation sets. Historical head validity is enough; candidate
head equations and syntactic center equality are not premises. -/
namespace Yulang.GeneralNominalHeadTestSemantic186
open GeneralNominalRecursiveInspection GeneralNominalMaterialization GeneralNominalOriginTerms
open GeneralNominalInspection (Query)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalHeadSchemaSemantic186 (Related related_symm structural_related nominal_related)
variable {model : Assignment}

theorem related_head (related : Related model first last) (valid : Head model first test) :
    Head model last test := by
  rcases related with equal | same
  · obtain ⟨value,seen⟩ := valid.1
    exact ⟨⟨value,(equal value).mp seen⟩,fun other observed => valid.2 other ((equal other).mpr observed)⟩
  · exact GeneralNominalHeadSemanticTransport185.head_transport same valid

mutual
 theorem schema_tests (query : Query) (first last : Origin) (mode : Mode)
    (related : Related model first last) (test : Origin × Test)
    (member : test ∈ (schema query first mode).tests) :
    ∃ other ∈ (schema query last mode).tests,
      test.2 = other.2 ∧ Related model test.1 other.1 := by
  cases query with
  | variables names => simp [schema] at member
  | deferred reason => simp [schema] at member
  | scalar base =>
    simp only [schema,List.mem_singleton] at member
    subst test
    exact ⟨(last,.scalar base),by simp [schema],rfl,related⟩
  | node shape children =>
    simp only [schema,List.mem_cons] at member ⊢
    rcases member with rfl | nested
    · exact ⟨(last,.structural shape),Or.inl rfl,rfl,related⟩
    · obtain ⟨other,present,equal,corresponding⟩ := schemas_tests children _ _ mode 0
        (fun index => structural_related related shape index) test nested
      exact ⟨other,Or.inr present,equal,corresponding⟩
  | nominal name children =>
    simp only [schema,List.mem_cons] at member ⊢
    rcases member with rfl | nested
    · exact ⟨(last,.nominal name children.length),Or.inl rfl,rfl,related⟩
    · obtain ⟨other,present,equal,corresponding⟩ := schemas_tests children _ _ .actual 0
        (fun index => nominal_related related name index) test nested
      exact ⟨other,Or.inr present,equal,corresponding⟩
 termination_by sizeOf query

 theorem schemas_tests (queries : List Query) (first last : Nat → Origin) (mode : Mode)
    (offset : Nat) (related : ∀ index, Related model (first index) (last index))
    (test : Origin × Test) (member : test ∈ (schemas queries first mode offset).tests) :
    ∃ other ∈ (schemas queries last mode offset).tests,
      test.2 = other.2 ∧ Related model test.1 other.1 := by
  cases queries with
  | nil => simp [schemas] at member
  | cons query rest =>
    simp only [schemas,Schema.append,List.mem_append] at member ⊢
    rcases member with here | later
    · obtain ⟨other,present,equal,origins⟩ := schema_tests query _ _ mode (related offset) test here
      exact ⟨other,Or.inl present,equal,origins⟩
    · obtain ⟨other,present,equal,origins⟩ := schemas_tests rest first last mode (offset+1) related test later
      exact ⟨other,Or.inr present,equal,origins⟩
 termination_by sizeOf queries
end

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadWFBoundary (boundary)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem head_tests (first last : Plan roles)
    (declaration : first.packet.declaration = last.packet.declaration)
    (constructors : first.packet.context.state.constructors = last.packet.context.state.constructors)
    (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
    (centers : ∀ index : Nat,
      Same model (.source ((List.ofFn first.input.center)[index]?.getD 0))
        (.source ((List.ofFn last.input.center)[index]?.getD 0)))
    (test : Origin × Test) (member : test ∈ first.headSchema.tests) :
    ∃ other ∈ last.headSchema.tests,
      test.2 = other.2 ∧ Related model test.1 other.1 := by
  have queries : GeneralNominalInspection.queries first.packet.context.state
      first.packet.context.interpretation first.packet.declaration =
      GeneralNominalInspection.queries last.packet.context.state
        last.packet.context.interpretation last.packet.declaration := by
    simp only [GeneralNominalInspection.queries,constructors,interpretation,declaration]
  unfold Plan.headSchema at member ⊢
  rw [← queries]
  exact schemas_tests _ _ _ .actual 0 (fun index => Or.inr (centers index)) test member

/-- Historical validity transfers every candidate head test at the same numeric
invocation, not only tests on the initial root. -/
theorem candidate_tests (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (registered : candidate.input ∈ state.core.sites)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (current : candidate.packet.context = state.core.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (model : Assignment) (valid : Models state model)
    (test : Origin × Test) (present : test ∈ candidate.headSchema.tests) : Head model test.1 test.2 := by
  have centers := GeneralNominalHeadIdentityCenters186.registered_identity_centers_same
    checked reachable candidate.input historical.input registered
    (GeneralNominalHeadCandidateReadback185.wf_registered_input reachable historical member)
    ((congrArg Occurrence.identity candidate.input_exact).trans
      (identity.trans (congrArg Occurrence.identity historical.input_exact).symm)) model valid
  have config := GeneralNominalHeadReadback185.wf_registered_configuration reachable historical member
  obtain ⟨other,found,testEq,related⟩ := head_tests candidate historical declaration
    ((congrArg (fun context : GeneralNominalCandidates.Context => context.state.constructors) current).trans config.2.1.symm)
    ((congrArg (fun context : GeneralNominalCandidates.Context => context.interpretation) current).trans config.2.2.symm)
    centers test present
  rw [testEq]
  exact related_head (related_symm related) ((valid.1.2.2 historical member).2.2.1.1 other found)

end Yulang.GeneralNominalHeadTestSemantic186
