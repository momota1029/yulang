import Yulang.GeneralDeclarativeNestedRun332

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNestedSound332
open GeneralDeclarativeNestedSyntax332 (Node Nodes Fields Tail)
open GeneralDeclarativeNestedRun332 (run runArgs runFields tailRun tagId tagId_exact)
open GeneralDeclarativeNestedView332 (Sources expand expand_is literalRows literalRows_sound)
open GeneralDeclarativeInlineTrace331 (Read Args)
open GeneralDeclarativeOrderedRecord326 (order)
open GeneralDeclarativeRecordMaterial330 (tailExpr)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalMaterialization (Mode)
open GeneralDeclarativeTermWalk322 (Occurrence)
open CommonRoleCanonicalRows (normalize)

theorem tail_sound (passed : tailRun mode raw tail = some uses) : Read s mode raw tail.code uses := by
  cases tail with
  | capture n =>
    have one := Option.some.inj passed
    cases one
    exact .capture
  | width =>
    cases raw <;> try cases passed
    case primitive tag args =>
      cases tag <;> cases args <;> try cases passed
      exact .primitive .nil
  | exactEnd =>
    cases raw <;> try cases passed
    case primitive tag args =>
      cases tag <;> cases args <;> try cases passed
      exact .primitive .nil

theorem before_expand {src : Sources s} {target : Node}
    (notBinder : target.observable) (hit : Read s mode (expand src input) target.code uses) :
    Read s mode input target.code uses := by
  rcases expand_is src input with same|⟨n,owner,rfl,linked,stored⟩
  · exact same ▸ hit
  · exact .expose (target.not_binder notBinder) linked stored hit

/-- The actual computed list is the same list certified by the
independent source Read. No witness is selected from a model, from a
child proposal, or from the result of resolution. -/
theorem sound (src : Sources s) (target : Node) (passed : run src mode input target = some uses) :
    Read s mode input target.code uses := by
  refine Node.rec
    (motive_1 := fun target => ∀ mode input uses, run src mode input target = some uses →
      Read s mode input target.code uses)
    (motive_2 := fun target => ∀ mode input uses, runArgs src mode input target = some uses →
      Args s mode input target.codes uses)
    (motive_3 := fun target => ∀ mode input uses, runFields src mode input target = some uses →
      GeneralDeclarativeInlineTrace331.Fields s mode input target.codes uses)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ target mode input uses passed
  · intro binder mode raw uses passed
    have eq := Option.some.inj passed
    cases eq
    exact .capture
  · intro tag targets ih mode raw uses passed
    apply before_expand (target := .primitive tag targets) trivial
    cases expanded : expand src raw with
    | primitive observed children =>
      by_cases same : tagId observed = tagId tag
      · have eq := tagId_exact same
        cases eq
        exact .primitive (ih mode children uses (by simpa [run,expanded] using passed))
      · simp [run,expanded,same] at passed
    | «variable» | nominal | record | variant | join => simp [run,expanded] at passed
  · intro tag targets ih mode raw uses passed
    apply before_expand (target := .nominal tag targets) trivial
    cases expanded : expand src raw with
    | nominal observed children =>
      by_cases same : observed = tag
      · subst observed
        exact .nominal (ih .actual children uses (by simpa [run,expanded] using passed))
      · simp [run,expanded,same] at passed
    | «variable» | primitive | record | variant | join => simp [run,expanded] at passed
  · intro tag target ih mode raw uses passed
    apply before_expand (target := .variant tag target) trivial
    cases expanded : expand src raw with
    | variant observed child =>
      by_cases same : observed = tag
      · subst observed
        exact .variant (ih mode child uses (by simpa [run,expanded] using passed))
      · simp [run,expanded,same] at passed
    | «variable» | primitive | nominal | record | join => simp [run,expanded] at passed
  · intro first last ih jh mode raw uses passed
    apply before_expand (target := .join first last) trivial
    cases expanded : expand src raw with
    | join a b =>
      cases gotFirst : run src mode a first with
      | none => simp [run,expanded,gotFirst] at passed
      | some xs =>
        cases gotLast : run src mode b last with
        | none => simp [run,expanded,gotFirst,gotLast] at passed
        | some ys =>
          have eq : xs++ys = uses := by simpa [run,expanded,gotFirst,gotLast] using passed
          subst uses
          exact .join (ih mode a xs gotFirst) (jh mode b ys gotLast)
    | «variable» | primitive | nominal | record | variant => simp [run,expanded] at passed
  · intro wanted tail ih mode raw uses passed
    by_cases good : wanted.keys ≠ [] ∧ wanted.keys.Nodup
    · apply before_expand (target := .record wanted tail) good.1
      cases closed : literalRows src.spines (expand src raw) with
      | none => simp [run,good,closed] at passed
      | some out =>
        obtain ⟨fields,terminal⟩ := out
        cases chosen : order (normalize fields) wanted.keys with
        | none => simp [run,good,closed,chosen] at passed
        | some picked =>
          cases first : runFields src mode picked wanted with
          | none => simp [run,good,closed,chosen,first] at passed
          | some children =>
            cases last : tailRun mode (tailExpr fields wanted.keys terminal) tail with
            | none => simp [run,good,closed,chosen,last] at passed
            | some suffix =>
              have eq : children++suffix = uses := by simpa [run,good,closed,chosen,first,last] using passed
              subst uses
              exact .record (literalRows_sound src _ closed) good.2 good.1 chosen
                (ih mode picked children first) tail.code_ok (tail_sound last)
    · simp [run,good] at passed
  · intro mode raw uses passed
    cases raw with
    | nil =>
      have eq : [] = uses := by simpa [runArgs] using passed
      subst uses
      exact .nil
    | cons => simp [runArgs] at passed
  · intro first rest ih jh mode raw uses passed
    cases raw with
    | nil => simp [runArgs] at passed
    | cons a as =>
      cases first : run src mode a first with
      | none => simp [runArgs,first] at passed
      | some children =>
        cases last : runArgs src mode as rest with
        | none => simp [runArgs,first,last] at passed
        | some suffix =>
          have eq : children++suffix = uses := by simpa [runArgs,first,last] using passed
          subst uses
          exact .cons (ih mode a children first) (jh mode as suffix last)
  · intro mode raw uses passed
    cases raw with
    | nil =>
      have eq : [] = uses := by simpa [runFields] using passed
      subst uses
      exact .nil
    | cons => simp [runFields] at passed
  · intro label target tail ih jh mode raw uses passed
    cases raw with
    | nil => simp [runFields] at passed
    | cons a as =>
      obtain ⟨key,body⟩ := a
      by_cases same : label = key
      · subst key
        cases first : run src mode body target with
        | none => simp [runFields,first] at passed
        | some children =>
          cases last : runFields src mode as tail with
          | none => simp [runFields,first,last] at passed
          | some suffix =>
            have eq : children++suffix = uses := by simpa [runFields,first,last] using passed
            subst uses
            exact .cons (ih mode body children first) (jh mode as suffix last)
      · simp [runFields,same] at passed

end Yulang.GeneralDeclarativeNestedSound332
