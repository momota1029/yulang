# SCC intrusion denotation boundary audit

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Classification: architecture review; no denotational theorem established

## Finding

The abstract-semantics draft defines an operational subtype-constraint closure
for its finite graph fragment. Closure transport under injective renaming does
not define satisfaction, solution sets, or a principal-solution order. The
current draft therefore cannot yet prove that parent intrusion preserves
solutions or that projection/use overlays remain principal.

An independent architecture review recommends splitting the next proof work:

1. Define assignments for local vertices with enclosing identities fixed, a
   subtype satisfaction relation for an already selected regular member graph,
   and a solution preorder that gives “principal” a precise meaning. Prove
   soundness and principality for the proposed projection and use overlays.
2. Separately prove that Oracle root/epoch preparation, evidence selection,
   failure handling, root ordering, finalization, and incoming uses produce a
   graph covered by that mathematical model.

The draft now proposes principality as exact equality between a member scheme's
instantiation-and-subsumption relation and the upward closure of root values
realized by satisfying local assignments, for each fixed environment
assignment. The multi-use relation includes each root result and use-site
constraint, uses a separate local assignment per use, and shares the environment
assignment. This is a candidate criterion, not a theorem; finite-scheme
representability and one-sided erasure remain open. The draft now names
identity correlation, `Top` erasure for `any -> int`, independent Q/R with
shared B, and fresh guarded-recursive assignments as concrete Oracle checks
for the criterion, without treating those fixtures as proof.

The required choices remain unresolved: regular-recursion interpretation;
meaning of `Bottom`, `Top`, unions, intersections, Functions, and nominal
constructors; assignment domain and environment-anchor semantics; the exact
principal-solution order; and the treatment of unguarded cycles and
polarity-only recursive collapse. No option is selected here. Oracle's
evidence-sensitive lower-edge decision belongs in the operational
correspondence proof, not implicitly in bare graph satisfaction.

The Oracle represents recursive scheme bounds operationally as a side-table
TypeVar and neutral bound graph. On incoming use, it freshens that variable,
projects lower/upper bounds, and reinstalls them as subtype constraints. This
is visible in frozen `a58eefc3` `crates/poly/src/types.rs:17-34`,
`crates/infer/src/instantiate.rs:620-634` for per-use freshening, and
`instantiate.rs:1002-1026` for bound projection/reinstallation. It is evidence
for recursive identity and constraint reinstatement, not a definition of
equi-recursive type equality or a denotation for recursive solutions.

The Oracle locator check supports this separation: frozen `a58eefc3`
`compact/surface.rs:12-24` starts a projection round and maps returned query
errors through a default root; `compact/collect/mod.rs:816-881` selects lower
edges via a scoped query and latches errors; and
`constraints/structural_kernel/access.rs:862-895` distinguishes Excluded,
Unclaimed, and Included records with evidence.

## Retired Python detour

The earlier assistant-authored finite Python model was removed from active
research artifacts. Its checks did not execute Rust or the Oracle, so its
claimed closure/projection/overlay outputs are withdrawn as Gate B/C evidence.
Historical progress records now label that detour explicitly. Current
characterization must use the Rust inference path and the frozen Oracle, or a
complete mathematical proof.

## Status

The abstract-semantics draft and `tasks/current.md` now record the separation
and unresolved decisions. The draft now also proves a conditional solution-set
bijection for injective fresh-parent renaming when finite endpoints interpret
variable/back-edge references by direct assignment lookup; environment anchors
remain fixed, and root observations must be extensional in interpreted values.
It does not prove an unfolding interpretation, root projection, edge selection,
erasure, or principality. No compiler code changed. No tests were run; this
slice changed research records only. The active objective remains incomplete.
