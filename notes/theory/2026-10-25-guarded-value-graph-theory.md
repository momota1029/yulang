# Guarded immutable value graphs: candidate theory

Status: primary Lean checks passed for the candidate; fresh independent review pending.
Author: `/root/guarded_value_graph_astra_r1`; requested gpt-6-astra/medium;
observed model/effort UNKNOWN. No descendants. Original author freeze had no coauthor; primary is a coauthor of subsequent elaboration repairs.
Authority: PARALLEL-THEORY-20261025/r1, SHA-256
`0751276e8eedf50d113475a0ef1c41b27b7ffd77cc4ccc28761e3cc9e792ff76`.
This is an implementation-independent research model, with no production authority.

## Parent and exact represented domain

The parent is ENV-GRAPH-1 and the immutable graph-extension/value-forms claims in
`docs/yulang-operational-type-safety-ja.tex`, lines 150–196, 258–267, 980–1010.
The paper requires finite immutable reference graphs, cycles guarded by genuine
data/lambda/delay constructors, finite outer-constructor observation, simultaneous
rec allocation preserving old typing, canonical elimination forms and absence of
closed bottom values. ENV-GRAPH-1 also requires native recursive/shared graph
readback, including preallocated uninitialized cells. That native part remains OPEN.

`GuardedValueGraph.lean` deliberately names a separate namespace and syntax. Its
types are unit, bottom, binary product, arrow and thunk. Concrete graph nodes are
unit, pair, lambda with body, delay with body, alias, metadata-bearing view,
roll marker and metadata-bearing evidence. Bodies contain references, variables,
unit, application and force. Lambda bodies have one explicit argument slot;
delay bodies have none. Node fields and bodies store references, so graph
recursion is actual reference recursion, not recursive meta-level Lean objects.
`FiniteGraph n` uses `Fin n`; allocating m names gives the finite disjoint domain
`Sum (Fin n) (Fin m)`. General helper lemmas also work for arbitrary reference
sorts equipped with the same bounded rank certificate.

**This is not the complete paper grammar or an embedding of HigherOrderSyntax.**
The accepted HigherOrderSyntax import supplies the existing library environment;
no theorem or syntactic identification with its values is assumed. In particular:

- `roll` is an identity-typed transparent marker. There is no μ type and no proof
  that a real roll/unroll pair changes between μA and its unfolded body correctly.
- Views and evidence preserve the identical type. Metadata is retained as a Nat,
  with no interpretation theorem. Type-changing evidence, type abstraction and
  application, polymorphism, union/intersection/top introductions are absent.
- Pairs represent one genuine data form. Records, required/optional fields,
  sequences, nominal tags and arities, arbitrary literals, continuations and
  handlers are absent.
- Lambda entry modes, receipts, adapters, result consumers, wrappers, dynamic
  Call's delayed carrier protocol, request binders and full computation syntax
  are absent. The body substitution theorem covers the explicitly given Term
  grammar, not the accepted core's mutual Value/Comp/Adapter grammar.

These omissions keep the original parents OPEN; they do not narrow their claims.

## Concrete guard and finite observation

`Node.next` returns exactly the target of alias/view/roll/evidence and returns
none for unit/pair/lambda/delay. A `Guarded g` certificate consists of numeric
ranks, a finite ceiling and the local inequalities rank(s) < rank(r) for every
transparent edge r→s. There is no decrease condition on pair fields or references
inside lambda/delay bodies. This is a local arithmetic condition on actual node
constructors, not a supplied observation theorem or assumed canonical form.

`finite_observation` inducts on a strict upper bound for the starting rank. A
transparent edge decreases that bound; a node with no transparent edge ends the
observation. `TransparentPath` and `transparent_path_rank` reject every nonempty
transparent cycle. Thus the whole graph may have cycles, provided no cycle is
entirely transparent. The rank certificate is sufficient for the paper's desired
finite observation, but **rank existence from the paper's syntactic cycle
condition is not proved**. A finite transparent-subgraph topological ranking or a
complete guard checker remains GVG-GUARD-COMPLETE-1. No graph-wide DAG hypothesis
is used or proposed as a language restriction.

`transparent_type` derives preservation of the exact type along each transparent
edge by node-typing inversion. `observation_typed` transports typing through the
finite observation. `terminal_canonical` then inverts only actual terminal
constructors. `reference_canonical` combines these results. `no_bottom_reference`
follows because no terminal constructor introduces bottom. It does not claim
that computations cannot have bottom type or that recursive computation terminates.

## Allocation and application to the parent

`allocate g fresh` injects old names with `Sum.inl` and fresh names with `Sum.inr`.
It maps references inside old nodes without changing their content; the old
subgraph gains no edge to a fresh node. `joinTy` preserves every old assignment
exactly. `fresh_no_collision` derives disjointness of old and new names.
`node_map`, `allocation_old_node`, `allocation_old_type` and
`allocation_observation` provide typing/content/observation preservation under
this explicit renaming. No mutable cell update is modeled.

All fresh names are available simultaneously to all fresh nodes. `allocate_typed`
requires individual fresh-node derivations against the joined assignment and
constructs the whole resulting graph typing. It does not assume post-graph
welltypedness. Lambda body typing checks its actual Term, and delay body typing
likewise checks the body. The arbitrary-node premise is still a premise: no
claim is made that paper/source rec constructors already supply those derivations.

`allocate_guard` constructs the post-graph ranks. Old rank stays rank_old; fresh
rank becomes ceiling_old + rank_fresh. An old edge stays old. A fresh-to-old
edge decreases because every old rank is below ceiling_old. A fresh-to-fresh
transparent edge decreases by the local rec rank check. The resulting ceiling is
ceiling_old + ceiling_fresh. Thus the post-graph guard is derived rather than
assumed, and mutually referring fresh guarded nodes need no allocation order.

`typed_subst` proves simultaneous replacement of reference and variable leaves
by typed Terms by induction on the body typing. `closeBody_typed` replaces all
recursive variables by fresh references in one substitution;
`old_body_weakening` preserves old derivations under the joined assignment.
`rec_extension` consumes all these lemmas and returns post-graph typing, finite
typed canonical observation at every old/new reference, and the typed closed
rec body. This discharges the corresponding restricted research-model implication
in the primary-checked construction; it is a concrete application to the parent proof
step, not closure of the paper or native ENV-GRAPH-1 claim.

## Distinguishing constructions and falsifiers

- `mutualLambda` has two lambdas whose bodies call one another. Both ranks are
  zero. `allocatedMutual` allocates them simultaneously into an empty old graph;
  per-node typing, the combined guard and observations are constructed.
- `sharedPair` has two fields pointing to the same unit node, also with equal
  zero ranks. Sharing and guarded edges are not rejected by a DAG requirement.
- `transparentCycle` consists of a view edge and a roll edge back to its start.
  It has a node-typing assignment with bottom everywhere but has no Guarded
  certificate. Hence graph node typing alone cannot justify bottom exclusion.
- `badFresh` allocates a fresh self-alias with bottom typing. Freshness and every
  individual new-node typing premise hold; `badAllocation_unguarded` rejects the
  resulting graph. The local new transparent-edge guard is essential.
- `no_transparent_self` rejects alias, view, roll or evidence self-loops uniformly;
  `no_transparent_two_cycle` and `no_transparent_cycle` cover mixed/longer loops.
- Replacing an old node's type is excluded by `allocation_old_type`; allocating a
  new name equal to an old one contradicts `fresh_no_collision`.

These are theorem constructions in the candidate, not executed tests and not
observations of actual compiler constructors.

## Remaining owners and mutual TODOs

GVG-CHECK-1 — primary: elaborate the frozen Lean file, inspect its theorem/axiom
boundary, repair only after author STOP, and obtain independent review. Falsifier:
any elaboration failure, admitted proof, forbidden axiom, or quantified conclusion
that fails for the represented constructor domain.

GVG-GUARD-COMPLETE-1 — next graph proof allocation: construct a bounded rank from
an explicit finite graph with no all-transparent directed cycle. Falsifier: a
finite cycle-guarded graph for which the proposed construction fails to assign a
strictly decreasing transparent rank. This direction is currently OPEN.

GVG-FORMS-1 — next full-paper graph proof allocation: add the actual missing
constructors and type-changing roll/view/type-evidence rules, then establish the
correct elimination-specific typed observations. Falsifier: a well-typed guarded
μ/view/type-application graph for which transparent traversal changes the type
without preserving the eliminator evidence. Keep this separate from the local
identity-typed `transparent_type` lemma.

GVG-REC-RHS-1 — full paper syntax owner: derive fresh-node typing from the original
rec RHS derivations under simultaneous binder-aware substitution, including all
lambda/adapter/request binders. Current node_map and Term substitution are usable
sublemmas only in their stated domain. Falsifier: capture or a missing recursive
reference in any represented full-paper RHS constructor.

ENV-GRAPH-1 — Luna/source intake: graph readback and original typing from actual
machine local/global initialization, current cells, Lambda/Callee/ValueEntry and
lookup/extend owners, including preallocation and uninitialized states. This
assignment performs no native audit and makes no native correspondence claim.
The existing constructor-map and native-environment notes are used only to retain
that obligation and ownership, not as evidence of graph realization. No production
implementation TODO is authorized or needed by this independent theory packet.

All original Simple-sub generation, accumulation, propagation, levels, extrusion,
intrusion, generalization and F1/FK1/foreign-continuation quantifiers remain
unchanged and OPEN outside their independently established premises.

## Frozen evidence and resources

Lean artifact SHA-256:
`4d2c3b17d0ab8d12606c875638426167ce596492167cecf042eb222436229f55`.
Paper dependency: `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.
HigherOrderSyntax: `ea727d33692bdcbe6b40245b960d01225b556b5334ffab649eea2699930d5972`.
Higher-order design: `50eb7ebd2ed2d155dfeca2e3ce99f3f5b990cc4f1bf101663949a04d8d4b748f`.
Toolchain: `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`.
Lakefile: `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194`.
Manifest: `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.

No historical proof is generalized beyond its premises; no historical failed
construction is revived. This file contains a new candidate construction.
No Lean/test/build/checker call was run by the author. Primary owns all checking.
Only the Lean file, this note and the assigned inbox are written. No scratch
paths, compiler/config edits, Git, network, descendants or background processes.
The assignment has a 600-second cap; exact dispatch time is UNKNOWN within the
primary's 06:36:20.860946Z–06:36:43.352751Z interval. The final inbox records freeze
time and conservative elapsed usage. Author stops writing at that freeze.

## Primary verification intake

Both authors stopped before primary takeover. Primary is a coauthor of elaboration repairs; all failed checker rows and original author handoffs remain intact. Safety repairs apply context induction hypotheses to the supplied typing derivation, type existential contexts explicitly, and use trace induction with generalized typing indices. Graph repairs rename a reserved binder, eliminate Empty dependently, expose the observed successor and give explicit joined reference types. No theorem premise or operational rule was weakened. Primary records final module/query hashes and axiom reports in `tasks/agent-loop/inbox/20261025-parallel-theory-r1-verification.jsonl`; fresh nonauthor review remains required. No compiler/native tests ran.
