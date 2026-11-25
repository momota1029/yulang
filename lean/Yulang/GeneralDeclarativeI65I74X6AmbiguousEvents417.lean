import Yulang.GeneralDeclarativeI65I74PlainMergedEntry416

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.X6Ambiguous417
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWitnessDeclaredState357 (point authoredRegistry)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open GeneralNominalCenteredHeadMatExpressions (Expr translate translateMany application)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeWhere319 (Capture)
open PlainMerged416 (PlainRows sourceX6 mergedCode chosenPoint416)

structure Candidate (s : I72.State) (q : I72.Request) where
  decl : Declaration
  ordinal : Nat
  authored : (authoredRegistry s.core.current).declarations[ordinal]? = some decl
  found : decl ∈ visible s.core q
  role : ∃ r ∈ s.core.current.environment.source.roles.rows, r.role = q.demand.role
  rolesValid : GeneralSourceMetadataRoles291.Valid s.core.current.environment.source.roles
  covered : DeclarationCovered s.core.current.environment decl
  signature : decl.Signature (authoredRegistry s.core.current).roles
  noBinders : decl.outputBinders = []
  noAssociated : decl.associated = []
  noWhere : decl.requirements = []

def Candidate.frame {s q} (d : Candidate s q) (f : Nat → Capture) :
    AuthoredBodyFrame393 s.core q :=
  ⟨d.ordinal,d.decl,d.authored,d.found,unusedPlacement403,f⟩

theorem exact_capture_port417 {s q} (d : Candidate s q) (f : Nat → Capture) (n : Nat) :
    (d.frame f).names.input n = f n := by
  simp [AuthoredBodyFrame393.names,Candidate.frame,GeneralDeclarativeFrameReadback325.sourceNames,
    GeneralDeclarativeProducedNames325.table,Declaration.outputNames,d.noBinders]

def groundSyntax (tag intName : Nat) : Pattern := .variant tag (.app intName [])
def groundCode (tag : Nat) : Expr := .variant tag (.primitive (.scalar .int) [])

structure PlainHit {s q} (rows : PlainRows s q) where
  candidate : Candidate s q
  first : Nat
  second : Nat
  unlike : first ≠ second
  head : candidate.decl.head = [sourceX6 rows.tag first second]

structure GroundHit {s q} (rows : PlainRows s q) where
  candidate : Candidate s q
  intName : Nat
  head : candidate.decl.head = [groundSyntax rows.tag intName]
  kind : application (authoredRegistry s.core.current).constructors
    (interpretation s.core.current.environment.source.snapshot) intName [] =
      some (.primitive (.scalar .int) [])

def PlainHit.originalHead {s q} {rows : PlainRows s q} (h : PlainHit rows) :
    SourceHead s.core q h.candidate.decl := by
  let capture := chosenPoint416 h.first h.second rows.payload
  let code : Expr := .join (.variant rows.tag (.variable h.first))
    (.variant rows.tag (.variable h.second))
  have built : translate (authoredRegistry s.core.current).constructors
      (interpretation s.core.current.environment.source.snapshot)
      (sourceX6 rows.tag h.first h.second) = some code := rfl
  refine .ordered capture ?_
  rw [rows.requested,h.head]
  have same1 := (PlainMerged416.two_binders_use_identical_actual_point416 h.first h.second rows.payload).1
  have same2 := (PlainMerged416.two_binders_use_identical_actual_point416 h.first h.second rows.payload).2
  refine .cons (.ordinary ⟨⟨.refl _, .refl _⟩,code,built,.direct (.structural ?_)⟩) .nil
  refine .join rows.selfRow (.variant rows.rootRow (.capture ?_ ?_))
    (.variant rows.rootRow (.capture ?_ ?_))
  · simpa [capture,same1,point,GeneralDeclarativeHead320.byMode] using
      GeneralDeclarativeBounds319.Bound.refl rows.payload
  · simpa [capture,same1,point,GeneralDeclarativeHead320.byMode] using
      GeneralDeclarativeBounds319.Bound.refl rows.payload
  · simpa [capture,same2,point,GeneralDeclarativeHead320.byMode] using
      GeneralDeclarativeBounds319.Bound.refl rows.payload
  · simpa [capture,same2,point,GeneralDeclarativeHead320.byMode] using
      GeneralDeclarativeBounds319.Bound.refl rows.payload

def GroundHit.originalHead {s q} {rows : PlainRows s q} (h : GroundHit rows) :
    SourceHead s.core q h.candidate.decl := by
  have built : translate (authoredRegistry s.core.current).constructors
      (interpretation s.core.current.environment.source.snapshot)
      (groundSyntax rows.tag h.intName) = some (groundCode rows.tag) := by
    simp [groundSyntax,groundCode,translate,translateMany,h.kind]
  refine .ordered (fun _ => emptyCapture403) ?_
  rw [rows.requested,h.head]
  refine .cons (.ordinary ⟨⟨.refl _, .refl _⟩,groundCode rows.tag,built,.direct (.structural ?_)⟩) .nil
  exact .variant rows.rootRow (.primitive (n := 0) (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i) rows.intRow (fun i => Fin.elim0 i))

def PlainHit.event {s q} {rows : PlainRows s q} (h : PlainHit rows) : Event s q :=
  ⟨h.candidate.frame (chosenPoint416 h.first h.second rows.payload),h.originalHead,fun i => by
    have bound := i.isLt
    simp [rows.noOutputs] at bound⟩

def GroundHit.event {s q} {rows : PlainRows s q} (h : GroundHit rows) : Event s q :=
  ⟨h.candidate.frame (fun _ => emptyCapture403),h.originalHead,fun i => by
    have bound := i.isLt
    simp [rows.noOutputs] at bound⟩

theorem plain_has_both_captures_on_actual_payload417 {s q} {rows : PlainRows s q} (h : PlainHit rows) :
    h.event.frame.names.input h.first = point rows.payload ∧
    h.event.frame.names.input h.second = point rows.payload := by
  change (h.candidate.frame _).names.input _ = _ ∧ (h.candidate.frame _).names.input _ = _
  rw [exact_capture_port417,exact_capture_port417]
  exact PlainMerged416.two_binders_use_identical_actual_point416 _ _ _

theorem the_two_candidate_heads_hold_in_the_very_same_model417
    {s q} {r : PlainRows s q} (p : PlainHit r) (g : GroundHit r) (m : I72.Model) (fit : Fits s m) :
    HeadModel s.core m q p.candidate.decl p.originalHead ∧
      HeadModel s.core m q g.candidate.decl g.originalHead := by
  exact ⟨source_head_sound p.originalHead m fit, source_head_sound g.originalHead m fit⟩

end Yulang.GeneralDeclarativeI65.I72.X6Ambiguous417
