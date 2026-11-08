import Yulang.CommonRoleFiniteAssociatedStable
import Yulang.CommonRoleAssociatedDeclarationExact

/-! Independent declaration semantics for arbitrary finite scalar source graphs.
This removes the executable `Computed` premise from graph derivations, but does
not supply dynamic where-child generation or general interval knownness. -/
namespace Yulang.CommonRoleFiniteAssociatedDeclaration
open CommonRoleFiniteAssociatedClosure
open CommonRoleAssociatedDeclarationExact
open CommonRoleSettledConstraints (State)
open CommonRoleOrdinaryKnownness (Evidence)

/-- Declaration-only graph closure. No resolver execution or saturation occurs
in this judgment; its associated step uses independent declaration derivations. -/
inductive DeclarativeDerives (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (p : Source n) (s : State n) : Fact n → Prop
  | initial {slot head} : Evidence s.atoms slot head →
      DeclarativeDerives env roles p s (slot, head)
  | identity {source target head} : p.identity source = p.identity target →
      DeclarativeDerives env roles p s (source, head) →
      DeclarativeDerives env roles p s (target, head)
  | associated {q head output} : q ∈ p.occurrences →
      DeclarativeDerives env roles p s (q.receiver, head) →
      DeclarativeComputed env roles (request q head) output →
      DeclarativeDerives env roles p s (q.output, output)

/-- Both directions hold for every fact of every finite graph and old state,
under the explicit core and associated-declaration well-formedness premises. -/
theorem derives_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Source n) (s : State n) (fact : Fact n) :
    Derives env roles wf p s fact ↔ DeclarativeDerives env roles p s fact := by
  constructor
  · intro h
    induction h with
    | initial h => exact .initial h
    | identity same _ ih => exact .identity same ih
    | associated member _ computed ih =>
      exact .associated member ih ((computed_iff_declarative env roles wf awf ..).mp computed)
  · intro h
    induction h with
    | initial h => exact .initial h
    | identity same _ ih => exact .identity same ih
    | associated member _ computed ih =>
      exact .associated member ih ((computed_iff_declarative env roles wf awf ..).mpr computed)

/-- Soundness and completeness of the actual finite saturator, without a
successful-run or enough-fuel hypothesis. The source graph remains explicit. -/
theorem saturate_declaration_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Source n) (s : State n) (fact : Fact n) :
    fact ∈ saturate env roles wf p s ↔ DeclarativeDerives env roles p s fact :=
  (saturate_exact ..).trans (derives_exact env roles wf awf p s fact)

/-- Exactness survives the actual emission into the ordinary constraint state. -/
theorem run_declaration_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Source n) (s : State n) (slot : Fin n) (head : Inference.Base) :
    Evidence (CommonRoleFiniteAssociatedModels.run env roles wf p s).atoms slot head ↔
      DeclarativeDerives env roles p s (slot, head) :=
  (CommonRoleFiniteAssociatedStable.run_evidence ..).trans
    (derives_exact env roles wf awf p s (slot, head))

/-- Reordering or duplicating occurrence declarations does not change the
independent closure, provided membership and source identity equality agree. -/
theorem declaration_congr (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (p q : Source n) (s : State n)
    (identities : ∀ a b, p.identity a = p.identity b ↔ q.identity a = q.identity b)
    (occurrences : ∀ r, r ∈ p.occurrences ↔ r ∈ q.occurrences) (fact : Fact n) :
    DeclarativeDerives env roles p s fact ↔ DeclarativeDerives env roles q s fact := by
  constructor
  · intro h
    induction h with
    | initial h => exact .initial h
    | identity same _ ih => exact .identity ((identities ..).mp same) ih
    | associated member _ computed ih =>
      exact .associated ((occurrences _).mp member) ih computed
  · intro h
    induction h with
    | initial h => exact .initial h
    | identity same _ ih => exact .identity ((identities ..).mpr same) ih
    | associated member _ computed ih =>
      exact .associated ((occurrences _).mpr member) ih computed

/-- Extensional order independence of the computed fact cache. This compares
membership, not list order or dictionaries, and assumes no frontier outcome. -/
theorem saturate_membership_congr (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p q : Source n) (s : State n)
    (identities : ∀ a b, p.identity a = p.identity b ↔ q.identity a = q.identity b)
    (occurrences : ∀ r, r ∈ p.occurrences ↔ r ∈ q.occurrences) (fact : Fact n) :
    fact ∈ saturate env roles wf p s ↔ fact ∈ saturate env roles wf q s :=
  (saturate_declaration_exact env roles wf awf p s fact).trans
    ((declaration_congr env roles p q s identities occurrences fact).trans
      (saturate_declaration_exact env roles wf awf q s fact).symm)

/-- Independent declaration closure is stable under restarting from the actual
emitted state. No extra facts are obtained by a second graph saturation. -/
theorem declaration_stable (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (p : Source n) (s : State n) (fact : Fact n) :
    DeclarativeDerives env roles p (CommonRoleFiniteAssociatedModels.run env roles wf p s) fact ↔
      DeclarativeDerives env roles p s fact :=
  (derives_exact env roles wf awf p _ fact).symm.trans
    ((CommonRoleFiniteAssociatedStable.derives_stable env roles wf p s fact).trans
      (derives_exact env roles wf awf p s fact))

end Yulang.CommonRoleFiniteAssociatedDeclaration
