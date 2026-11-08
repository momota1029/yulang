import Yulang.CommonEffectMixedFamilyAllocation
import Yulang.CommonEffectMixedFormula

/-!
Actual finite constraint generation for resolved invariant effect-family
arguments of both kinds. Allocation is computed from the original input;
every occurrence uses the same fresh slot precisely when its original
row/family/argument position agrees. All original lower/upper checks and all
same-position cross comparisons are emitted as ordinary formula syntax.

The finite metadata table records the kinds of the admitted invariant
positions. It does not resolve source names or derive declaration variance.
The result is a constraint generator, not a general quantified solver or an
existential search for role/dispatch substitutions.
-/
namespace Yulang.CommonEffectMixedFamilyConstraints
open Core.PresenceGeneration (TyTerm CompTerm)
open CommonEffectRequestGeneration (Computation RowExpr)
open CommonEffectKindedFormula (Formula Names localEnv andAll andAll_exact)
open CommonEffectMixedFamilyAllocation
open CommonEffectInvariantIntervals
open CommonEffectRowIntervalConstraints (Bounds)

abbrev Families := List (List Kind)

/-- Admission uses the exact resolved family and argument positions. It does
not search for a signature with satisfiable arguments. -/
def declared (families : Families) (occurrence : Occurrence scopes α) : Bool :=
  match families[occurrence.slot.family]? with
  | none => false
  | some signature => signature[occurrence.slot.argument]? == some occurrence.argument.kind

inductive Declared (families : Families) (occurrence : Occurrence scopes α) : Prop where
  | intro (signature : List Kind) :
      families[occurrence.slot.family]? = some signature →
      signature[occurrence.slot.argument]? = some occurrence.argument.kind →
      Declared families occurrence

theorem declared_exact (families : Families) (occurrence : Occurrence scopes α) :
    declared families occurrence = true ↔ Declared families occurrence := by
  cases found : families[occurrence.slot.family]? with
  | none =>
    simp only [declared, found, Bool.false_eq_true, false_iff]
    intro admitted
    cases admitted with
    | intro signature lookup _ => simp [found] at lookup
  | some signature =>
    simp only [declared, found, beq_iff_eq]
    constructor
    · exact Declared.intro signature found
    · intro admitted
      cases admitted with
      | intro other lookup kinded =>
        have same : other = signature := Option.some.inj (lookup.symm.trans found)
        simpa only [same] using kinded

def argumentMember (assignment : α → Computation) (actual : Computation) : Argument scopes α → Prop
  | .value bounds => Value.Member (bounds.eval assignment) actual.1
  | .row bounds => EffectRow.Member (bounds.eval assignment) actual.2

/-- This interpretation is stated on the original occurrences and arbitrary
semantic assignments, independently of the finite allocator and generator. -/
def Member (assignment : α → Computation) (values : Slot → Common.Ty)
    (effects : Slot → Common.Row) (occurrence : Occurrence scopes α) : Prop :=
  argumentMember assignment (values occurrence.slot, effects occurrence.slot) occurrence.argument

def Reconciles (families : Families) (occurrences : List (Occurrence scopes α))
    (assignment : α → Computation) : Prop :=
  ∃ values effects, ∀ occurrence ∈ occurrences,
    Declared families occurrence ∧ Member assignment values effects occurrence

def renameRow (names : α → β) (row : RowExpr scopes α) : RowExpr scopes β :=
  CommonEffectFormula.rowSubst (fun name => CompTerm.var (names name)) row

theorem eval_renameRow (names : α → β) (row : RowExpr scopes α) (assignment : β → Computation) :
    (renameRow names row).eval assignment = row.eval (assignment ∘ names) := by
  simp only [renameRow, CommonEffectFormula.rowSubst_eval, CompTerm.eval_var, Function.comp_def]

def renameBounds (names : α → β) (bounds : Bounds scopes α) : Bounds scopes β :=
  ⟨bounds.lower.map (renameRow names), bounds.upper.map (renameRow names)⟩

theorem eval_renameBounds (names : α → β) (bounds : Bounds scopes α) (assignment : β → Computation) :
    (renameBounds names bounds).eval assignment = bounds.eval (assignment ∘ names) := by
  unfold renameBounds Bounds.eval
  congr 1 <;> funext occurrence <;> apply propext
  · constructor
    · rintro ⟨endpoint, included, holds⟩
      obtain ⟨original, member, rfl⟩ := List.mem_map.mp included
      exact ⟨original, member, (congrFun (eval_renameRow names original assignment) occurrence).mp holds⟩
    · rintro ⟨endpoint, included, holds⟩
      exact ⟨renameRow names endpoint, List.mem_map.mpr ⟨endpoint, included, rfl⟩,
        (congrFun (eval_renameRow names endpoint assignment) occurrence).mpr holds⟩
  · simp only [List.forall_mem_map, eval_renameRow]

/-- The original interval check remains explicit alongside its shared
argument comparisons. No semantic predicate is a formula atom. -/
def emitArgument (argument : Argument scopes α) (names : α → β) (actual : CompTerm β) :
    Formula scopes β :=
  match argument with
  | .value bounds => .and (.old ((bounds.check (scopes := scopes)).rename names))
      (.and (.tyLe (bounds.lower.rename names) actual.ty) (.tyLe actual.ty (bounds.upper.rename names)))
  | .row bounds => .and (.old (CommonEffectRowIntervalConstraints.check (renameBounds names bounds)))
      (.old (CommonEffectRowIntervalConstraints.contains (renameBounds names bounds)
        (RowExpr.fromPresence actual.row)))

theorem emitArgument_exact (argument : Argument scopes α) (names : α → β) (actual : CompTerm β)
    (assignment : β → Computation) :
    (emitArgument argument names actual).Holds assignment ↔
      argumentMember (assignment ∘ names) (actual.eval Common.model assignment) argument := by
  cases argument with
  | value bounds =>
    change ((bounds.check (scopes := scopes)).rename names).Holds assignment ∧
      Common.Subtype ((bounds.lower.rename names).eval Common.model assignment) (actual.ty.eval Common.model assignment) ∧
      Common.Subtype (actual.ty.eval Common.model assignment) ((bounds.upper.rename names).eval Common.model assignment) ↔ _
    simp only [CommonEffectFormula.Formula.holds_rename, ValueTerms.check_exact, TyTerm.eval_rename]
    change Value.Consistent (bounds.eval (assignment ∘ names)) ∧
      Value.Member (bounds.eval (assignment ∘ names)) (actual.eval Common.model assignment).1 ↔ _
    exact ⟨And.right, fun member => ⟨Common.subtype_trans member.1 member.2, member⟩⟩
  | row bounds =>
    change (CommonEffectRowIntervalConstraints.check (renameBounds names bounds)).Holds assignment ∧
      (CommonEffectRowIntervalConstraints.contains (renameBounds names bounds)
        (RowExpr.fromPresence actual.row)).Holds assignment ↔ _
    rw [CommonEffectRowIntervalConstraints.check_exact, CommonEffectRowIntervalConstraints.contains_exact,
      eval_renameBounds, RowExpr.eval_fromPresence]
    exact ⟨And.right, fun member => ⟨Common.rowLe_trans member.1 member.2, member⟩⟩

abbrev LocalNames (occurrences : List (Occurrence scopes α)) :=
  α ⊕ Names (slots .value occurrences).length (slots .row occurrences).length

def emitOccurrence (occurrences : List (Occurrence scopes α)) (occurrence : Occurrence scopes α) :
    Formula scopes (LocalNames occurrences) :=
  match occurrence.argument with
  | .value bounds =>
    match locate (slots .value occurrences) occurrence.slot with
    | none => .core .bot
    | some index => emitArgument (.value bounds) Sum.inl (CompTerm.var (.inr (.inl index)))
  | .row bounds =>
    match locate (slots .row occurrences) occurrence.slot with
    | none => .core .bot
    | some index => emitArgument (.row bounds) Sum.inl (CompTerm.var (.inr (.inr index)))

theorem emitOccurrence_exact (occurrences : List (Occurrence scopes α))
    (occurrence : Occurrence scopes α) (included : occurrence ∈ occurrences)
    (assignment : α → Computation) (locals : Assignment occurrences) :
    (emitOccurrence occurrences occurrence).Holds (localEnv assignment locals) ↔
      Member assignment (valueAt occurrences locals) (rowAt occurrences locals) occurrence := by
  cases occurrence with
  | mk slot origin argument =>
    cases argument with
    | value bounds =>
      have present := occurrence_slot occurrences ⟨slot, origin, .value bounds⟩ included
      change slot ∈ slots .value occurrences at present
      simp only [emitOccurrence, locate_present _ _ present, emitArgument_exact,
        CommonEffectKindedFormula.localEnv_comp_inl, Member, argumentMember,
        CompTerm.eval_var, localEnv, valueAt_present _ _ _ present]
    | row bounds =>
      have present := occurrence_slot occurrences ⟨slot, origin, .row bounds⟩ included
      change slot ∈ slots .row occurrences at present
      simp only [emitOccurrence, locate_present _ _ present, emitArgument_exact,
        CommonEffectKindedFormula.localEnv_comp_inl, Member, argumentMember,
        CompTerm.eval_var, localEnv, rowAt_present _ _ _ present]

/-- Both directions of every same-position pair occur in the outer product.
Different row locations are not cross-compared merely for sharing a family. -/
def cross (first last : Occurrence scopes α) : Formula scopes α :=
  if first.slot = last.slot then
    match first.argument, last.argument with
    | .value left, .value right => .tyLe left.lower right.upper
    | .row left, .row right => .old (CommonEffectRowIntervalConstraints.crossChecks left right)
    | _, _ => .core .top
  else .core .top

theorem cross_of_members (first last : Occurrence scopes α) (assignment : α → Computation)
    (values : Slot → Common.Ty) (effects : Slot → Common.Row)
    (firstIn : Member assignment values effects first) (lastIn : Member assignment values effects last) :
    (cross first last).Holds assignment := by
  by_cases same : first.slot = last.slot
  · simp only [cross, same, ↓reduceIte]
    cases first with
    | mk firstSlot firstOrigin firstArgument =>
      cases last with
      | mk lastSlot lastOrigin lastArgument =>
        change firstSlot = lastSlot at same
        subst lastSlot
        cases firstArgument <;> cases lastArgument
        · exact Common.subtype_trans firstIn.1 lastIn.2
        · exact True.intro
        · exact True.intro
        · exact (CommonEffectRowIntervalConstraints.cross_checks_exact _ _ _).mpr
            (Common.rowLe_trans firstIn.1 lastIn.2)
  · simp only [cross, same, ↓reduceIte, Formula.holds_core, Core.PresenceGeneration.Formula.Holds]

def crosses (occurrences : List (Occurrence scopes α)) : Formula scopes α :=
  andAll (occurrences.flatMap (fun first => occurrences.map (cross first)))

theorem crosses_of_members (occurrences : List (Occurrence scopes α)) (assignment : α → Computation)
    (values : Slot → Common.Ty) (effects : Slot → Common.Row)
    (members : ∀ occurrence ∈ occurrences, Member assignment values effects occurrence) :
    (crosses occurrences).Holds assignment := by
  simp only [crosses, andAll_exact, List.forall_mem_flatMap, List.forall_mem_map]
  intro first firstIn last lastIn
  exact cross_of_members first last assignment values effects (members first firstIn) (members last lastIn)

def generate (families : Families) (occurrences : List (Occurrence scopes α)) : Formula scopes α :=
  if occurrences.all (declared families) = true then
    .and (crosses occurrences)
      (.existsLocals (slots .value occurrences).length (slots .row occurrences).length
        (andAll (occurrences.map (emitOccurrence occurrences))))
  else .core .bot

/-- The actual finite allocator and generator are exact on every original
occurrence. There is no allocation oracle, successful-kind premise, external
support condition, or restriction on the semantic argument assignments. -/
theorem generate_exact (families : Families) (occurrences : List (Occurrence scopes α))
    (assignment : α → Computation) :
    (generate families occurrences).Holds assignment ↔ Reconciles families occurrences assignment := by
  by_cases admitted : occurrences.all (declared families) = true
  · have declaredAll : ∀ occurrence ∈ occurrences, Declared families occurrence := by
      simpa only [List.all_eq_true, declared_exact] using admitted
    simp only [generate, ite_eq_left admitted, Formula.Holds, andAll_exact, List.forall_mem_map]
    constructor
    · rintro ⟨_, locals, constraints⟩
      refine ⟨valueAt occurrences locals, rowAt occurrences locals, ?_⟩
      intro occurrence included
      exact ⟨declaredAll occurrence included,
        (emitOccurrence_exact occurrences occurrence included assignment locals).mp (constraints occurrence included)⟩
    · rintro ⟨values, effects, members⟩
      refine ⟨crosses_of_members occurrences assignment values effects (fun occurrence included =>
        (members occurrence included).2), encode occurrences values effects, ?_⟩
      intro occurrence included
      apply (emitOccurrence_exact occurrences occurrence included assignment _).mpr
      have present := occurrence_slot occurrences occurrence included
      cases occurrence with
      | mk slot origin argument =>
        cases argument with
        | value bounds =>
          change slot ∈ slots .value occurrences at present
          simpa only [Member, argumentMember, valueAt_encode _ _ _ _ present] using
            (members ⟨slot, origin, .value bounds⟩ included).2
        | row bounds =>
          change slot ∈ slots .row occurrences at present
          simpa only [Member, argumentMember, rowAt_encode _ _ _ _ present] using
            (members ⟨slot, origin, .row bounds⟩ included).2
  · simp only [generate, ite_eq_right admitted, Formula.holds_core, Core.PresenceGeneration.Formula.Holds, false_iff]
    rintro ⟨_, _, members⟩
    apply admitted
    simp only [List.all_eq_true, declared_exact]
    exact fun occurrence included => (members occurrence included).1

end Yulang.CommonEffectMixedFamilyConstraints
