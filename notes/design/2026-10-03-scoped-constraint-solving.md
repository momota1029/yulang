# Scoped rational equality and closed structural subtype solving

Status: Draft
Date: 2026-10-03
Scope: finite regular equality quotient and closed structural comparison
Reviewed-by: M3 semantic and conformance review (2026-10-03), no findings
Implementation authority: none
Supersedes: none

## 1. Governing relation and input boundary

[Charter §§10–12, 20, 22–23](2026-09-29-scc-intrusion-redesign-charter.md)
retain symbolic joint constraints, request witness identity and variable-only
lexical scope. The [structural projection package §§2 and 6](2026-10-03-scoped-structural-projection.md)
supplies the finite contractive regular grammar and its structural subtype
relation: atoms, Functions, finite mandatory unique-label Records, and
fixed-arity labelled constructors with declared variance. This package adds
an effective solver slice for that mathematical fragment, not source policy.

Equality means equality of regular constructor unfoldings, with corresponding
Record label sets identical; graph sharing/presentation need not be identical. Flexible
inference variables may be assigned regular constructor graphs; rigid names
remain symbolic and cannot be bound. Each flexible variable has a finite set
of permitted rigid names from the fixed opening frontier. These sets come from
lexical ownership, not just numeric depth: sibling binders at the same depth
remain distinct. A valid solution mentions only permitted names, including
through transitive graph dependencies. Intersections can therefore be
non-prefix sets.
Constructor heads have no levels. All same-name rigid occurrences retain their
original binder identity; equal numeric depths do not identify different names.

The input is a finite graph and finite equality ledger. Constructor cycles
are contractive; pure alias cycles collapse to one unconstrained class.
Regular equality permits a constructor-guarded occurrence cycle such as
`X=Function(Int,X)`, unlike the earlier acyclic equality kernel. It permits
no lattice laws, arbitrary declared bounds, open rows or effectful equality.
Original `Eq` clauses and symbolic `K,D` stay retained jointly; representation
of equality by a quotient does not delete their evidence or endpoints.

## 2. Equality quotient and permission propagation

Maintain equivalence classes of input nodes, descriptors for atoms/constructor
heads, and a worklist of required equalities. Quotient aliases first. Merging
classes intersects any permission sets imposed on them. If both classes
have descriptors, distinct constructor heads, different Record label sets,
or different rigid/primitive atoms reject the uniform equality obligation.
Matching descriptors enqueue corresponding child equalities, independent of
variance: equality requires all corresponding children equal. A descriptor
and a descriptor-free flexible class may merge without choosing new syntax.

Propagate every permission restriction along descriptor children and alias
classes. Each merge or parent-to-child propagation intersects finite allowed-
name sets. A rigid leaf outside a propagated set rejects; a free class merely
retains the narrower set. Requeue dependents when a merge or permission decrease changes
their obligations. Process descriptor pairs with canonical identities so a
constructor cycle closes on an already processed pair rather than unfolding.
No occurs rejection is applied to a contractive constructor cycle. Alias-only
cycles leave a free class; accepted descriptor cycles remain contractive.
Caps restrict variable classes, not constructor heads. When a variable becomes
determined or references restricted, stage and process every derived cap
constraint before successful publication. This extends the reviewed variable-
cap equality kernel to productive regular cycles, not to arbitrary subtype
bounds.

**Preservation.** Each merge records an existing required equality. Any
solution assigns its merged classes the same regular unfolding, so matching
heads force corresponding child equalities and descriptor clashes cannot be
repaired. Every child dependency of a class is a dependency of that class;
permission intersection/propagation therefore records a necessary restriction.
Conversely each satisfying assignment of the quotient unfolds the matching
descriptors to equal regular trees and respects every propagated permission.
Restricting it to original roots satisfies the original equations and scopes.
A rigid equality failure is not a per-instance semantic disequality fact.

**Relative most-general result.** Assign any scope-respecting regular graphs
to the descriptor-free residual classes. The quotient's finite guarded equations
then define the descriptor classes, preserving shared roots and regular cycles.
Every such assignment extends to an original equality solution. Conversely
an original solution is constant on each quotient class and supplies those
residual assignments; its descriptor roots are exactly their guarded unfolding.
Thus every solution factors through the quotient by further scope-respecting
instantiation. The quotient is an MGU representation relative to this regular
constructor equality fragment, not a most-general solution of arbitrary bounds.
The result is modulo consistent fresh-name transport and graph bisimulation;
productive recursion is essential to its guarded unfolding claim.
Any additional `Phi`, including original joint `K,D`, remains conjoined under
the same assignments; free-class assignments must satisfy it separately.

There are finitely many class merges, each reducing class count. If `V` is the
number of variable classes and `H` the number of rigid names in the fixed
frontier, at most `V*H` permission bits can be removed. Between changes the canonical
node-pair worklist is finite. Descriptor and permission dependencies are finite,
so exhaustive quotient construction terminates. This selects no compiler cache,
resource limit or numerical runtime bound.

## 3. Closed subtype saturation on a fixed quotient

For closed roots in the resulting finite graph, fix its quotient and let `N`
be its node count. Closed here means no unsolved flexible head; rigid atoms
remain opaque symbols. Solve structural `s <= t` by the greatest relation on
ordered node pairs, not by accepting a circular assumption unconditionally.

Every queried and derived pair first enters the same generation-time scope
guard before any rigid/head outcome. For `(kappa_l,Int)`, report scope escape
before head mismatch under §22. Exact identity remains reflexive when admitted
by the selected discipline; no constructor receives a stored level.

Start with all `N^2` pairs provisionally present. Atom pairs survive only for
matching atoms; different heads fail. Function pairs require the reversed
argument pair and ordinary result pair. Record pairs require all expected
upper labels in the lower record and comparisons only for those fields.
Declared-variance constructor pairs require same heads and their same/reversed
child pairs; invariant coordinates require both child directions. Register
reverse dependencies and remove a pair whenever a local head/label condition
or required child pair fails. A deduplicated failure worklist propagates each
removed pair once for this fixed graph; at most `N^2` pairs are removed.

At quiescence the surviving pairs form a post-fixed structural simulation,
so every surviving queried pair belongs to the greatest structural relation.
Conversely any simulation survives deletion: its heads/labels satisfy local
rules and all required children stay in that simulation. Induction over
removals shows none of its pairs can be deleted. Therefore a surviving finite
certificate exists iff the closed comparison is valid; deletion refutes every
structural simulation of that pair. Regular back-edges need no unfolding.
This is the structural relation theorem conditional on successful scope
certification of the required pairs. Guard failure is a separate outcome;
it does not itself refute every structural simulation or prove unsatisfiability.

Equality construction and this closed solve are separate phases; a changed
quotient invalidates this fixed-pair theorem's input. Their finite bounds are
quotient/permission-bit decreases plus a finite `N^2` pair phase, not whole flexible
solver termination. Equal projection profiles never establish invariant
`Eq(X,Y)`: retain original endpoints and use actual admitted equality or
mutual-comparison obligations. Source `K,D` are not reconstructed from bits.

## 4. Why closed substitutions alone cannot express an open bound

Consider only `X <= {}` in the mandatory fixed-label grammar, without unions,
Top, Bottom or row variables. Its closed solutions include `{}` and every
finite record with additional mandatory fields and arbitrary closed children.
A closed substitution for `X` fixes its Record labels. Further instantiation
of children cannot add a label, so no one such substitution factors all these
solutions. Leaving `X` unconstrained admits atoms or Functions that violate
the bound. Thus closed-substitution output alone is not principal for this
open constraint; even a fixed record skeleton with free children cannot cover
all admissible label sets in this grammar.

This does **not** refute a finite principal residual bound graph. The single
edge `X <= {}` already is an exact finite residual representation: its
solutions are precisely the intended record assignments, including all label
extensions. It is neither a class-3 non-finiteness result nor a reason to add
row variables, selectors or a source restriction. A residual SCC bound graph
is a compatible candidate target, pending a principal residual factorization
proof when composing aliases, scope restrictions and structural projection.
Actual Yulang row constraints and union forms remain characterization and
solver research outside this closed-substitution counterexample.

## 5. Exact residual clauses without residual acceptance

The solver slice uses the original graph, symbolic equations and common
structural relation. Quotient root maps and projected outputs remain correlated
to original endpoints and the same package witness. Neither successful closed
comparison nor the equality MGU proves acceptance of arbitrary residual bounds.
No equality/evidence is discharged merely because a profile matches, and no
caller-private equation becomes a generic-arm assumption.

Subtype edges with holes remain in a finite residual `ConstraintGraph`, with
scoped binders, original `Phi`, family equality and `K,D` attached jointly.
This is an exact finite relational presentation of the retained clauses, not
a satisfiability/principality proof for them or an SCC lifecycle theorem.

## 6. Provenance and current ownership evidence

Pure structural equality/subtyping have the Simple-sub baseline in the
[pinned audit](../progress/2026-09-30-simple-sub-paper-mlsub-audit.md).
Variable levels and rigid existential scopes are user-selected Yulang
extensions; rational scoped quotient and residual coupling are new successor
theorem candidates awaiting review.

Bounded current-worktree inspection gives this ownership map, as feasibility
evidence rather than an approved implementation plan:

| Responsibility | Owner |
|---|---|
| Resolved expressions | `crates/yu-hir/src/module.rs::ResolvedExpr`: Lambda, Integer, Name, Error only |
| Constraint collection/SCC planning | `crates/yu-solver/src/lib.rs` |
| Live bound mutation/extrusion | `InferenceSession::{constrain_live,extrude}` |
| Component generalization | `crates/yu-solver/src/f5c_generalization.rs::F5cGeneralizer` |
| Incoming closed-scheme instantiation | `InferenceSession::instantiate_and_route_closed_inner`, using `yu-types` |

Ordinary calls/effects/profiles are absent from the resolved expression surface.
The successor cannot be implemented solely by changing the generalizer;
front-end surfaces and joint source/solver contracts need their own gates.
This inspection establishes no acceptance of the illustrative source skeleton.

## 7. Exact next gate

Next solve open-head and Record-extension residual constraints with principal
factorization, retaining permission/frontier restrictions and projection
summaries jointly with original `Eq,K,D`. Prove residual composition across
alias merges and feedback rather than independently guessing closed profiles.
Full source generation, general effectful Function/operation compatibility,
declared bounds, family/lifecycle transport and compiler implementation remain
later gates. This package grants no source-semantic approval or implementation
authority and does not narrow the source support envelope.
