import Yulang.GeneralVersionedHeadFromSharing313

set_option backward.isDefEq.respectTransparency false
/-! The constructor tests and actual-variable rows of a translated head
never read beyond roots already supplied by the site's actual center tuple. -/
namespace Yulang.GeneralVersionedSchemaOrigins313
open GeneralNominalMaterialization GeneralNominalRecursiveInspection GeneralNominalCenters
open GeneralNominalInspection (Query)
open GeneralNominalCenteredModelExtension (originSource)

def Contained (safe : Nat → Prop) (report : Schema) : Prop :=
  (∀ test ∈ report.tests, safe (originSource test.1)) ∧
  (∀ use ∈ report.variables, safe (originSource use.origin))

theorem appended {safe : Nat → Prop} (left : Contained safe a) (right : Contained safe b) :
    Contained safe (a.append b) :=
  ⟨fun _ h => (List.mem_append.mp h).elim (left.1 _) (right.1 _),
   fun _ h => (List.mem_append.mp h).elim (left.2 _) (right.2 _)⟩

mutual
 theorem one (safe : Nat → Prop) (query : Query) (origin : Origin) (mode : Mode)
    (root : safe (originSource origin)) : Contained safe (schema query origin mode) := by
  cases query <;> rw [schema]
  case variables names =>
    refine ⟨(by intro a m; cases m),?_⟩
    intro use member
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp member
    exact root
  case scalar base =>
    refine ⟨?_,(by intro a m; cases m)⟩
    intro test member
    cases List.mem_singleton.mp member
    exact root
  case deferred _ => exact ⟨(by intro a m; cases m),(by intro a m; cases m)⟩
  case node shape children =>
    have child := many safe children (fun i => .structural origin shape i) mode 0 (fun _ => root)
    refine ⟨?_,child.2⟩
    intro test member
    rcases List.mem_cons.mp member with eq|later
    · cases eq; exact root
    · exact child.1 test later
  case nominal name children =>
    have child := many safe children (fun i => .nominal origin name i) .actual 0 (fun _ => root)
    refine ⟨?_,child.2⟩
    intro test member
    rcases List.mem_cons.mp member with eq|later
    · cases eq; exact root
    · exact child.1 test later
 termination_by sizeOf query

 theorem many (safe : Nat → Prop) (queries : List Query) (origin : Nat → Origin) (mode : Mode) (start : Nat)
    (roots : ∀ i, safe (originSource (origin i))) :
    Contained safe (schemas queries origin mode start) := by
  cases queries <;> rw [schemas]
  case nil => exact ⟨(by intro a m; cases m),(by intro a m; cases m)⟩
  case cons query rest =>
    exact appended (one safe query (origin start) mode (roots start))
      (many safe rest origin mode (start+1) roots)
 termination_by sizeOf queries
end

theorem centers (p : Plan roles) (safe : Nat → Prop)
    (outsideArity : safe 0)
    (actual : ∀ i : Fin (roles p.input.occurrence.demand.role).arity, safe (p.input.center i)) :
    ∀ n ∈ GeneralVersionedHeadFromSharing313.origins p, safe n := by
  have covered : Contained safe p.headSchema := by
    apply many
    intro index
    by_cases within : index < (roles p.input.occurrence.demand.role).arity
    · simpa only [originSource,List.getElem?_ofFn,within,↓reduceDIte,Option.getD_some] using actual ⟨index,within⟩
    · simpa only [originSource,List.getElem?_ofFn,within,↓reduceDIte,Option.getD_none] using outsideArity
  intro n member
  rcases List.mem_append.mp member with a|b
  · obtain ⟨test,present,rfl⟩ := List.mem_map.mp a
    exact covered.1 test present
  · obtain ⟨use,present,rfl⟩ := List.mem_map.mp b
    exact covered.2 use present

end Yulang.GeneralVersionedSchemaOrigins313
