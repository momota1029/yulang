import Yulang.GeneralDeclarativeI65Selection367

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeInspect321 (Visit PatternK2)
open GeneralDeclarativeGraphRows321 (observed structural shapeOf pending_nominal_self_cycle)
open GeneralDeclarativeK2Alias321 (AliasCycle cycle_in_alias_graph)
open GeneralDeclarativeK2Graph321 (View)
open GeneralDeclarativeOrigins321 (Supported Backed backed_iff pending_only)
open GeneralDeclarativeLowerKnown321 (alias_refl)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeK2Graph321 (Shape)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarations (Declaration)

/-- Every actual supported prefix step is also in the unfiltered
ordinary graph. The converse is deliberately unavailable. -/
theorem lift_prefix_visit {first next : View} {root site : Nat} {code : Expr}
    (lift : ∀ n head,first n head → next n head)
    (visit : Visit first root code site) : Visit next root code site := by
  induction visit with
  | here node => exact .here node
  | primitive recorded option slot _ tail =>
    exact .primitive (lift _ _ recorded) option slot tail
  | nominal recorded option slot _ tail =>
    exact .nominal (lift _ _ recorded) option slot tail
  | field recorded member inspected _ tail =>
    exact .field (lift _ _ recorded) member inspected tail
  | variant recorded _ tail => exact .variant (lift _ _ recorded) tail

/-- Support-only aliases track each actual backing equation. In
particular this does not use mutual bounds in the unfiltered ordinary
normal form: those bounds may themselves depend on unfinished outputs.
This fragment can later be extended with independently backed bounds. -/
inductive BackAlias {s : GeneralDeclarativeHead320.State} {complete : Nat → Prop}
    (origin : Supported s complete) : Nat → Nat → Prop where
  | refl (n : Nat) : BackAlias origin n n
  | written : Backed origin (⟨a,.variable b⟩ : Equation) → BackAlias origin a b
  | reverse : Backed origin (⟨b,.variable a⟩ : Equation) → BackAlias origin a b
  | next : BackAlias origin a b → BackAlias origin b c → BackAlias origin a c

theorem backed_alias_is_ordinary {s : GeneralDeclarativeHead320.State} {complete : Nat → Prop}
    {origin : Supported s complete} {a b : Nat} (proof : BackAlias origin a b) : GeneralDeclarativeLowerKnown321.Alias s a b := by
  induction proof with
  | refl n => exact alias_refl n
  | written h =>
    obtain ⟨originKind, exactOrigin, _⟩ := h
    exact .forward (origin.ordinary exactOrigin)
  | reverse h =>
    obtain ⟨originKind, exactOrigin, _⟩ := h
    exact .backward (origin.ordinary exactOrigin)
  | next _ _ a b => exact .trans a b

def backedView {s : GeneralDeclarativeHead320.State} {complete : Nat → Prop}
    (support : Supported s complete) : View :=
  fun n shape => ∃ source written, BackAlias support n source ∧
    Backed support (⟨source,written⟩ : Equation) ∧ shapeOf written = some shape

theorem backed_view_is_ordinary {s : GeneralDeclarativeHead320.State} {complete : Nat → Prop}
    {support : Supported s complete} {n : Nat} {shape : Shape}
    (read : backedView support n shape) : structural s n shape := by
  obtain ⟨source,written,alias,⟨_,origin,_⟩,literal⟩ := read
  exact ⟨source,backed_alias_is_ordinary alias,written,support.ordinary origin,literal⟩

/-- Evidence for one positively reached ordinary position, even
if this exact visible candidate never finishes. Descent can use
only supported heads; the reached site's cycle is checked against
the ordinary graph (with unfinished equations intact).
This is the existing normalized named ordinary fragment only. -/
structure AuthoredOrdinaryPrefix (s : State) (q : Request) (row : Declaration) where
  visibleNow : row ∈ visible s q
  index : Nat
  input : Capture
  atInput : q.demand.arguments[index]? = some input
  pattern : Pattern
  atHead : row.head[index]? = some pattern
  code : Expr
  written : translate (authoredRegistry s.current).constructors
    (interpretation s.current.environment.source.snapshot) (normalize pattern) = some code
  complete : Nat → Prop
  source : Supported s.current.ordinary complete
  knownFirst : ∃ shape, backedView source input.lower shape
  reached : Nat
  visited : Visit (backedView source) input.lower code reached

theorem authored_ordinary_prefix_k2 {s : State} {q : Request} {row : Declaration}
    (p : AuthoredOrdinaryPrefix s q row)
    (cycle : AliasCycle s.current.ordinary (observed s.current.ordinary) p.reached) :
    PatternK2 s.current.ordinary p.input.lower p.code := by
  exact ⟨p.reached,lift_prefix_visit (fun _ _ read => backed_view_is_ordinary read) p.visited,cycle⟩

/-- Negative evidence for a selected/ambiguous frontier must also
cover prefixes in a different visible row. No successful head,
quiet scan, or winning declaration is used here. -/
theorem ordinary_prefix_veto_independent_of_choice {s : State} {q : Request} {row : Declaration}
    (p : AuthoredOrdinaryPrefix s q row)
    (cycle : AliasCycle s.current.ordinary (observed s.current.ordinary) p.reached) :
    ¬(∀ d ∈ visible s q, ∀ pre : AuthoredOrdinaryPrefix s q d,
        ¬PatternK2 s.current.ordinary pre.input.lower pre.code) := by
  intro claims
  exact claims row p.visibleNow p (authored_ordinary_prefix_k2 p cycle)

/-- The same concrete equation is unavailable as independent input
support yet can force a K2 veto at a genuinely reached site. No
hypothesis asserts successful candidate completion. -/
theorem pending_equation_at_reached_site_has_k2 {s : State} {q : Request} {row : Declaration}
    (p : AuthoredOrdinaryPrefix s q row) (tag owner : Nat)
    (derived : p.source.derivesFrom
      (⟨p.reached,.nominal tag [.variable p.reached]⟩ : Equation) (.output owner))
    (onlyPending : ∀ k, p.source.derivesFrom
      (⟨p.reached,.nominal tag [.variable p.reached]⟩ : Equation) k →
        ∃ i,k = .output i ∧ ¬p.complete i) :
    ¬Backed p.source (⟨p.reached,.nominal tag [.variable p.reached]⟩ : Equation) ∧
      PatternK2 s.current.ordinary p.input.lower p.code := by
  refine ⟨fun authorized => pending_only p.source _ onlyPending ((backed_iff p.source _).mpr authorized),?_⟩
  have cycle := pending_nominal_self_cycle p.source owner derived
  exact authored_ordinary_prefix_k2 p (cycle_in_alias_graph cycle)

end Yulang.GeneralDeclarativeI65
