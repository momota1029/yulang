# Symbolic typed-family lifecycle transport audit

Date: 2026-10-02
Branch: `research/simple-sub-intrusion`
Status: conditional relational lemmas; solver/source correspondence remains open

## Requirement and scope

The user requires typed-family argument invariance to remain symbolic through
solving, residualization, generalization, fresh instantiation, and intrusion.
It must not be reconstructed from concrete materialized rows. This audit checks
whether the coupled-interface draft distinguishes formula transport from
preservation of the complete solution fiber at each phase.

## Review result

The `Rel_C` carrier with symbolic predicates `K` and incidence bookkeeping
`D` remains the smallest coherent mathematical presentation reviewed so far.
Typed-family denotation and source-owned sharing are semantic; occurrence IDs,
owner labels, and `D` present and transport those dependencies. Row support is
only a projection. The draft already keeps its scope conditional: source rules
must construct the correct ownership groups, and concrete solver operations
must preserve the relation before the lifecycle is certified.

Three M3 audits agreed that the phase obligations should remain distinct while
sharing the same carrier:

| Phase | Conditional result recorded in the draft | Evidence still required |
|---|---|---|
| Solve | Structural substitution preserves formula satisfaction for target assignments factoring through the substitution; `FamAgree_A` and its occurrence groups remain in `K`. | Prove every relevant source solution has an observationally equivalent factorization through the actual polarized solver substitution. Equality-MGU completeness does not prove this for subtype solving. |
| Residualization | Handler images transport symbolic formulas and incidence; injective naturality can commute with the complete image. | Source transition/search adequacy, complete output-witness coverage, and a least finite representable image preserving all dependent fibers. |
| Generalization | A fixed view packages its owned binders, formula, and interface together while keeping outer identities fixed. | Correct source view/binder selection and exact fixed-outer projection, including scheduler/root-version behavior. |
| Fresh instantiation | One injective map consistently renames all owned identities, occurrences, groups, formulas, and boundary identities. | Prove the source use events are independent and the implementation carries the complete namespace. |
| Injective intrusion | Equivariance transports the full relation under a bijective identity map. | Show the actual parent/boundary construction satisfies the equivariance premises. |
| Non-injective intrusion | A quotient is valid only if every source observation has an observationally equivalent parent-constant representative; a point-fragment sufficient condition is stated. | Define the client observation and prove the quotient/fiber property. Shared interval inhabitation alone is insufficient. |

These are transport and completeness obligations, not one universal “rename”
lemma. An independently projected pair of marginals cannot be rejoined unless
the source relation is losslessly represented; a joint receiver constraint
may correlate uses even when their local fresh ranges are disjoint.

## Corrections from adversarial review

The compiler-referee found that the handler-image commutation statement had
only forward equations for already mapped output witnesses. It allowed an
extra target transition/output with no source preimage, contradicting the
claimed relational-image equality. The draft now requires backward lifting of
every target successor and output observation in the transported image.
Delta review confirmed that this closes the countermodel.

The non-injective quotient equations also mixed a source-coordinate assignment
with an interface already rewritten to parent coordinates, and omitted
assignments for retained local variables. The draft now defines a target
assignment over `range(P)` (parents plus retained locals), its pullback `P*μ`
to all source coordinates, and separate source/target observation functions.
For a fixed source presentation it evaluates the original formula under
`P*μ`; for varying interfaces it takes the existential direct image over all
source presentations. A compiler-referee delta review closed both namespace
and backward-lifting findings. The direct-image clarification was closed by
primary inspection as a minor notation repair.

## Remaining gate

The audit does not prove that the current or successor solver retains `K,D`,
that the source relation creates the right ownership batches, or that a
finite principal representation exists. In particular, a materialized empty
row does not authorize deleting a family predicate whose owner remains
observable through an arm, continuation, root, or later use. Conversely, an
unobservable owned coordinate may be existentially projected only with a
fiber-preservation proof.

The next independent proof target is the actual solution-factorization and
handler-image lifting condition for one precisely chosen finite fragment,
followed by source-generation correspondence. The concrete nested-receiver
policy is still unresolved; it must not be guessed from Oracle routing. No
compiler code or tests were changed or run. `git diff --check` is the only
mechanical check for this record and design slice.
