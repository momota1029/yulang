import Yulang.GeneralNominalExposureSources

/-! Source-labelled projections through named actual centers. A projection
selects a subtree of an explicit parent; an opaque leaf has no such subtree.
All selected labels keep the original syntax keys and current hole scope. -/
namespace Yulang.GeneralNominalLabelledOriginClosure
open GeneralDeclarationPatterns GeneralNominalOriginTerms GeneralNominalRecursiveInspection
open GeneralNominalIndexedHoleReadback GeneralNominalHoleElimination GeneralNominalOpenPatternLabels
open GeneralNominalUniformHoleLabels GeneralNominalSourceLabelVocabulary
open GeneralNominalFiniteMeaning GeneralNominalSourcePatternParts GeneralNominalSubtermOrder

variable {models : GeneralNominalCommonBridge.Assignment → Prop}
variable {origins : Nat → Origin} {remaining keys : List Nat}

structure Value (models : GeneralNominalCommonBridge.Assignment → Prop)
    (context : GeneralNominalCandidates.Context) (origins : Nat → Origin)
    (remaining keys : List Nat) (root : Origin) where
  pattern : Pattern
  term : Expr Nat
  labelled : Labelled models context origins remaining root pattern term
  allowed : Allowed keys remaining pattern

def Value.alias (value : Value models context origins remaining keys first)
    (same : ∀ model, models model → Same model first last) : Value models context origins remaining keys last :=
  ⟨value.pattern,value.term,alias_labelled value.labelled same,value.allowed⟩

def Value.restrict (value : Value before context origins remaining keys root)
    (included : ∀ model, after model → before model) : Value after context origins remaining keys root :=
  ⟨value.pattern,value.term,restrict_labelled value.labelled included,value.allowed⟩

def source_value (member : hole ∈ remaining)
    (same : ∀ model, models model → Same model root (origins hole)) :
    Value models context origins remaining keys root where
  pattern := .var hole
  term := .leaf hole
  labelled := ⟨⟨rfl,by simp only [GeneralNominalInspection.translate,GeneralNominalCompoundReadback.quote],True.intro⟩,same,by
    intro name present
    cases List.mem_singleton.mp present
    exact member⟩
  allowed := ⟨.var _,by
    intro name present
    cases List.mem_singleton.mp present
    exact member⟩

def frontier_value (member : Origin.source identity ∈ frontier) :
    Value models context (GeneralNominalIndexedHoleReadback.origin frontier)
      (holes frontier) keys (.source identity) where
  pattern := .var (index frontier identity)
  term := .leaf (index frontier identity)
  labelled := ⟨⟨rfl,by simp only [GeneralNominalInspection.translate,GeneralNominalCompoundReadback.quote],True.intro⟩,
    source_leaf member⟩
  allowed := ⟨.var _,by
    intro name present
    cases List.mem_singleton.mp present
    exact List.mem_range.mpr (List.idxOf_lt_length_of_mem member)⟩

def initial_value (source : GeneralNominalSourceFormation.InitialSource registry context (root : GeneralSourceDictionaries.Occurrence roles))
    (position : Fin (roles root.demand.role).arity) :
    Value models context (GeneralNominalIndexedHoleReadback.origin (GeneralNominalSourceFrontier.frontier context.state))
      (holes (GeneralNominalSourceFrontier.frontier context.state)) keys (.source (root.demand.arguments position).1) :=
  frontier_value (GeneralNominalSourceFrontier.initial_inputs source position).1

theorem follows_readback (path : Follows root term endpoint part)
    (known : Readback models origins remaining root term) :
    Readback models origins remaining endpoint part := by
  induction path with
  | root => exact known
  | child test children position prior ih => exact GeneralNominalIndexedHoleReadback.project ih position

theorem follows_below (path : Follows root term endpoint part) : Below part term := by
  induction path with
  | root => exact .refl
  | child test children position prior ih => exact .trans (.child test children position .refl) ih

/-- The finite source label is selected syntactically, before any model is
supplied. It is also a subterm for every future global substitution. -/
theorem followed_value (value : Value models context origins remaining keys root)
    (path : Follows root value.term endpoint part) :
    ∃ result : Value models context origins remaining keys endpoint,
      result.term = part ∧ Part value.pattern result.pattern ∧ Below result.term value.term := by
  obtain ⟨pattern,source,label⟩ := GeneralNominalOpenReification.followed_source_label path value.labelled.1
  exact ⟨⟨pattern,part,⟨label,follows_readback path value.labelled.2⟩,allowed_part source value.allowed⟩,
    rfl,source,follows_below path⟩

theorem named_projection (value : Value models context origins remaining keys parent)
    (explicit : value.term = .node test children) (position : Fin (arity test))
    (center : ∀ model, models model → Same model (GeneralNominalOriginTerms.project parent test position) (.source identity)) :
    ∃ result : Value models context origins remaining keys (.source identity),
      result.term = children position ∧ Part value.pattern result.pattern ∧ Below result.term value.term := by
  have path : Follows parent value.term (GeneralNominalOriginTerms.project parent test position) (children position) :=
    .child test children position (explicit ▸ Follows.root)
  obtain ⟨result,equal,part,below⟩ := followed_value value path
  exact ⟨result.alias center,equal,part,below⟩

theorem follows_leaf {term : Expr Nat} (path : Follows root term endpoint part)
    (equal : term = .leaf hole) : endpoint = root ∧ part = .leaf hole := by
  induction path with
  | root => exact ⟨rfl,equal⟩
  | child test children position prior ih =>
    have impossible := ih.2
    cases impossible

theorem opaque_path (path : Follows root (.leaf hole : Expr Nat) endpoint part) :
    endpoint = root ∧ part = .leaf hole := follows_leaf path rfl

/-- Named centers do not erase the distinction between projection from an
explicit term and refinement of an opaque source hole. -/
theorem opaque_has_no_constructor (path : Follows root (.leaf hole : Expr Nat) endpoint (.node test children)) : False := by
  have impossible := (opaque_path path).2
  cases impossible

end Yulang.GeneralNominalLabelledOriginClosure
