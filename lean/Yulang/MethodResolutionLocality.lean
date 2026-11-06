import Yulang.FrozenMethods

/-!
# Local, once-per-site resolution after SCC facts are frozen

The operation being scheduled below is the existing `MethodResolution.resolve`.
An answer retains all three results (missing, unique, ambiguous), rather than
discarding diagnostics through `freeze`. Site IDs are stable across schedules.

The input table contains the final receiver knowledge, visible role scope, and
typed fallback of each SCC. No global resolution state is consulted when a
site is processed. The theorems show exactly which local queries may change
without changing a result, and that resolving any collection of frozen SCCs
in any order gives the same per-site answers. They do not compute the SCCs or
prove that constraint solving has already stabilized these input facts.
-/

namespace Yulang.MethodResolutionLocality

open MethodResolution
open Methods (Selection)

variable {Row : Type}

/-- Only the queried method name matters in an unknown receiver's scope.
For a known receiver, only field presence and the fallback on absence matter;
the field's payload and all hidden/unqueried fields may be different. -/
def SameFacts (left right : Site Row) : Prop :=
  left.name = right.name ∧
    match left.receiver, right.receiver with
    | none, none => ∀ role declaration,
        Candidate left.scope left.name role declaration ↔
          Candidate right.scope right.name role declaration
    | some first, some last =>
        (first.lookup left.name).isSome = (last.lookup right.name).isSome ∧
          (first.lookup left.name = none → left.typedFallback = right.typedFallback)
    | _, _ => False

/-- Other names, unrelated role declarations, and unobserved field payloads
do not influence this site's actual three-way selection result. -/
theorem resolve_local (left right : Site Row) (same : SameFacts left right) :
    resolve left = resolve right := by
  obtain ⟨name, facts⟩ := same
  unfold resolve
  cases first : left.receiver with
  | none =>
      cases last : right.receiver with
      | none =>
          have candidates : ∀ role declaration,
              Candidate left.scope left.name role declaration ↔
                Candidate right.scope left.name role declaration := by
            simpa only [SameFacts, first, last, ← name] using facts
          simpa only [name] using unknown_scope_ext left.scope right.scope left.name candidates
      | some type => simp only [first, last] at facts
  | some firstType =>
      cases last : right.receiver with
      | none => simp only [first, last] at facts
      | some lastType =>
          simp only [first, last] at facts
          cases firstField : firstType.lookup left.name with
          | none =>
              have fallback := facts.2 firstField
              cases lastField : lastType.lookup right.name with
              | none => simp only [known, firstField, lastField, fallback]
              | some value => simp [firstField, lastField] at facts
          | some value =>
              cases lastField : lastType.lookup right.name with
              | none => simp [firstField, lastField] at facts
              | some other =>
                  simp only [known, firstField, lastField]
                  exact congrArg (fun label => Selection.unique (Reference.field label)) name

theorem freeze_local (left right : Site Row) (same : SameFacts left right) :
    freeze left = freeze right := by
  simp only [freeze, resolve_local left right same]

/-- The actual elaborated frozen artifact is invariant too; this is equality
of the selected reference and receiver, before any later instantiation. -/
theorem finalize_local (left right : Site Row) (same : SameFacts left right)
    (receiver : FrozenMethods.CoreExpr) :
    FrozenMethods.finalize left receiver = FrozenMethods.finalize right receiver := by
  simp only [FrozenMethods.finalize, freeze_local left right same]

universe u v
variable {SiteId : Type u} {SCC : Type v} [DecidableEq SiteId]

abbrev Answers (SiteId : Type u) := SiteId → Option (Selection Reference)

def resolveOne (sites : SiteId → Site Row) (site : SiteId) (answers : Answers SiteId) : Answers SiteId :=
  fun current => if current = site then some (resolve (sites site)) else answers current

def run (sites : SiteId → Site Row) : List SiteId → Answers SiteId → Answers SiteId
  | [], answers => answers
  | site :: rest, answers => run sites rest (resolveOne sites site answers)

/-- The scheduled loop writes exactly the queried site's existing result.
Repeated occurrences are idempotent; absence preserves the initial entry. -/
theorem run_apply (sites : SiteId → Site Row) (order : List SiteId)
    (answers : Answers SiteId) (site : SiteId) :
    run sites order answers site =
      if site ∈ order then some (resolve (sites site)) else answers site := by
  induction order generalizing answers with
  | nil => simp [run]
  | cons first rest ih =>
      rw [run, ih]
      by_cases later : site ∈ rest
      · simp [later]
      · by_cases same : site = first
        · subst site
          simp [resolveOne, later]
        · simp [resolveOne, later, same]

theorem run_same_sites (sites : SiteId → Site Row) (left right : List SiteId)
    (same : ∀ site, site ∈ left ↔ site ∈ right) (answers : Answers SiteId) :
    run sites left answers = run sites right answers := by
  funext site
  simp only [run_apply, same site]

theorem run_permutation (sites : SiteId → Site Row) (left right : List SiteId)
    (permutation : left.Perm right) (answers : Answers SiteId) :
    run sites left answers = run sites right answers :=
  run_same_sites sites left right (fun _ => permutation.mem_iff) answers

theorem run_append (sites : SiteId → Site Row) (first last : List SiteId) (answers : Answers SiteId) :
    run sites (first ++ last) answers = run sites last (run sites first answers) := by
  induction first generalizing answers with
  | nil => rfl
  | cons site rest ih => exact ih _

/-- Each SCC supplies its own list of sites. There is no rescan of the sites
belonging to other SCCs and no global repeat-until-stable loop. -/
def runSCCs (sites : SiteId → Site Row) (owned : SCC → List SiteId) :
    List SCC → Answers SiteId → Answers SiteId
  | [], answers => answers
  | component :: rest, answers => runSCCs sites owned rest (run sites (owned component) answers)

theorem runSCCs_flatMap (sites : SiteId → Site Row) (owned : SCC → List SiteId)
    (order : List SCC) (answers : Answers SiteId) :
    runSCCs sites owned order answers = run sites (order.flatMap owned) answers := by
  induction order generalizing answers with
  | nil => rfl
  | cons component rest ih =>
      simpa only [runSCCs, List.flatMap_cons, run_append] using ih (run sites (owned component) answers)

theorem runSCCs_apply (sites : SiteId → Site Row) (owned : SCC → List SiteId)
    (order : List SCC) (answers : Answers SiteId) (site : SiteId) :
    runSCCs sites owned order answers site =
      if ∃ component ∈ order, site ∈ owned component then some (resolve (sites site)) else answers site := by
  simp only [runSCCs_flatMap, run_apply, List.mem_flatMap]

/-- Every pair of SCC schedules covering the same SCC IDs produces exactly
the same answers. The schedules may permute or repeat completed SCCs. The
input snapshots are fixed; no source typing or solver-success premise occurs. -/
theorem scc_order_independent (sites : SiteId → Site Row) (owned : SCC → List SiteId)
    (left right : List SCC) (same : ∀ component, component ∈ left ↔ component ∈ right)
    (answers : Answers SiteId) :
    runSCCs sites owned left answers = runSCCs sites owned right answers := by
  rw [runSCCs_flatMap, runSCCs_flatMap]
  apply run_same_sites
  intro site
  simp only [List.mem_flatMap, same]

theorem scc_permutation (sites : SiteId → Site Row) (owned : SCC → List SiteId)
    (left right : List SCC) (permutation : left.Perm right) (answers : Answers SiteId) :
    runSCCs sites owned left answers = runSCCs sites owned right answers :=
  scc_order_independent sites owned left right (fun _ => permutation.mem_iff) answers

/-- Each covered entry agrees with the existing independent selection
judgment, including the field/role priority at its actual frozen receiver. -/
theorem resolved_site_exact (sites : SiteId → Site Row) (owned : SCC → List SiteId)
    (order : List SCC) (answers : Answers SiteId) (site : SiteId)
    (covered : ∃ component ∈ order, site ∈ owned component) (reference : Reference) :
    runSCCs sites owned order answers site = some (.unique reference) ↔ Selects (sites site) reference := by
  simp only [runSCCs_apply, covered, ↓reduceIte, Option.some.injEq]
  exact resolve_exact _ _

theorem unprocessed_site_unchanged (sites : SiteId → Site Row) (owned : SCC → List SiteId)
    (order : List SCC) (answers : Answers SiteId) (site : SiteId)
    (outside : ¬ ∃ component ∈ order, site ∈ owned component) :
    runSCCs sites owned order answers site = answers site := by
  simp only [runSCCs_apply, outside, ↓reduceIte]

/-- Even changing every other SCC's snapshot is harmless for this run, as
long as each processed site's local queries are unchanged. -/
theorem scc_input_locality (left right : SiteId → Site Row) (owned : SCC → List SiteId)
    (order : List SCC) (answers : Answers SiteId)
    (same : ∀ component ∈ order, ∀ site ∈ owned component, SameFacts (left site) (right site)) :
    runSCCs left owned order answers = runSCCs right owned order answers := by
  funext site
  rw [runSCCs_apply, runSCCs_apply]
  by_cases covered : ∃ component ∈ order, site ∈ owned component
  · obtain ⟨component, scheduled, member⟩ := covered
    simp only [show (∃ component ∈ order, site ∈ owned component) from
      ⟨component, scheduled, member⟩, ↓reduceIte]
    exact congrArg some (resolve_local _ _ (same component scheduled site member))
  · simp only [covered, ↓reduceIte]

end Yulang.MethodResolutionLocality
