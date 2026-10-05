# Constructive coverage of the finite monomorphic SCC source graph

Date: 2026-10-05
Status: unreviewed research derivation; conditional source coverage; frozen on handoff
Implementation authority: none
Baseline: `a4cfe9babacd0a7094d25beeec73104613b74b95`
Method: constructor-by-constructor translation and finite graph partition; logical independence witnesses for missing scheme premises
Exclusive lease: this file only

## 1. Objective, input and claim class

Determine which premises of the reviewed conditional SCC-instance bridge
follow from the supplied monomorphic pure structural generator, and which
still need source rules. The input is a **supplied finite derivation graph**
whose nodes belong to the table in source-generated structural theorems §5,
with finite guarded annotation schemas and a supplied lexical resolution map.
This input assumption is not raw-source acceptance, a grammar decision, or a
claim that every Yulang construct already has this derivation.

The result is a conditional construction of a finite initial graph, including
every node and use of that supplied fragment. It strengthens the bridge's
local-generation premise and separates monomorphic lexical references from
external scheme instantiation. It does not establish the complete four-premise
SCC-instance theorem for the replacement, source-wide context closure,
principal projection, or implementation conformance.

Only the SCC foundation has Authoritative status, in its declared F0–F2
scope. The structural table is a reviewed theorem-scoped generator. The
finite-context draft supplies conditional closure requirements. None supplies
an approved generalization/freshening semantics for this structural fragment.

## 2. Exact inspected dependencies

All mathematical inputs were read from the pinned commit, rather than mutable
task, theory, index or question-board records. The SCC foundation was read in
full: **Oracle invariant**, **Lightweight-port boundary**, **Phase and fact
ownership**, **Construction sequence F0–F2**, **Required structural witnesses**,
**Complexity and measurements**, **Stop conditions**, and **Deferred semantic
gates** are the governing sections used here. The structural package's §5 was
read exactly; a preceding full-file read also exposed its scope header and
other sections, but their callback and structural-completion theorems are not
premises of this construction. Finite-context §§1–6 and the SCC-instance
bridge's **Premises**, **Derivation** and **Scope boundary** were read in full.
The three required repository rules were read in full and their working-tree
bytes were checked equal to the pinned versions.

| Dependency | Pinned Git blob |
|---|---|
| `notes/design/2026-09-20-constraint-collection-scc-foundation-draft.md` | `4768a9869d4dd12861d292d71a56570102f370df` |
| `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` | `ab212217cd404991cded2b8fd529a1e731a806b3` |
| `notes/design/2026-10-03-source-context-finite-closure.md` | `658b106c18da450a2514c54496a12d840cd9d6c4` |
| `notes/progress/2026-10-05-source-scc-instance-finiteness-bridge.md` | `a1abc32ee7b5b9a536f2c5595c7df26b416ba426` |
| `rules/research-lab.md` | `69860b70bc96a5a60bab3bf9ec667ea25bc6578c` |
| `rules/design-authority.md` | `466da7e03855d3f5dd7f2b5dc438cccc9b1c76d8` |
| `rules/git-concurrency.md` | `a55f967648dc057e111d56b2e6556d05c1edcfe3` |

The bridge's older baseline `757c90564` is provenance, not this assignment's
baseline. Its four premises are evaluated as written at the pinned commit.

## 3. Constructive coverage relation

Let `S` be the finite supplied source graph. Let `I` contain its expression
and binder identities; let `F_S` contain all explicitly present source fields
and child references; let `A` be the disjoint union of the finite annotation
schema graphs. Measure `|A|` by nodes plus explicit edges/field entries, so
large Record schemas are accounted for even when many fields share one node.
A name occurrence has a supplied resolved lexical binder
`rho(e)` in `I`. Recursive references point to an existing binder identity;
they are not recursively expanded source children.

First allocate an endpoint `T_i` for every `i in I`, and the finite schema
nodes of `A`. Then visit each non-reference source node once, using an existing
identity on every child/binder/schema reference. Associate each emitted clause
with its generating source occurrence. Distinct source uses retain distinct
occurrence identities even when they refer to the same endpoint.

| Supplied node | Finite output and coverage witness |
|---|---|
| literal | One declared atom equation at its endpoint. |
| resolved name | `T_e = T_rho(e)`; one occurrence identity and reference to the already allocated lexical endpoint. |
| lambda | One Function descriptor referencing parameter and body endpoints; no traversal of the referenced binder's definition. |
| mandatory record | One Record descriptor with exactly its finite unique-label field references. |
| application | One directed bound to a Function descriptor over the argument/result endpoints. |
| known mandatory field selection | One directed bound to a one-field Record descriptor over the result endpoint. |
| immutable binding | One binder/RHS equation and the existing body result reference. |
| monomorphic recursive definition/reference | Allocate the member binder once; every reference uses that endpoint through its occurrence equation. |
| admitted structural annotation | Retain its finite guarded schema graph and supplied original directed checking clause. |

This is the existing §5 translation, with an explicit source/output incidence
map. It introduces no new forcing, name-resolution, or annotation-admission
rule. In particular, the resolution map and original annotation checking
clause are input evidence, not inferred from successful structural solving.

Each row emits bounded local data plus references to its explicitly present
fields. Hence there is a fixed finite constant `c` for this table such that
the generated node/clause/reference count is bounded by

```text
c * (|I| + |F_S| + |A| + 1).
```

No numerical value for `c` or production allocation guarantee is claimed.
The bound records schema nodes and their finite edges, including annotation
back-references. A constructor cycle contributes graph edges once, not its
infinite unfolding. Exhaustion of the nine rows proves coverage of this
supplied table. It does not prove completeness of the table for raw Yulang.

## 4. SCC partition and the external-use distinction

Restrict `I` to a finite set `D` of represented definitions. For every supplied
resolved occurrence inside a represented definition body, record its parent
and target in `D`; local lexical names remain endpoint references but do not
become module-definition arcs. This requires that the chosen graph's module
use endpoints and parent assignments are supplied and total. Its use set `U`
is finite because it is indexed by finite source occurrences. Deduplicating
graph arcs does not remove occurrences from `U`.

The directed graph `D,U` has a finite SCC partition and finite condensation
DAG. Every internal occurrence references its preallocated member endpoint.
Every external occurrence also references an existing lexical endpoint under
the **global monomorphic table**. Thus this construction cannot generate the
recursive `t -> Box(t)` instance family from finite-context §5. It creates no
scheme instances at all, inside or outside an SCC.

The Authoritative foundation guarantees complete collection and occurrence
retention for its admitted F0 binding-body uses, and a deterministic static
partition/order. It explicitly excludes direct-root names and later discovered
dependencies. It also explicitly creates no occurrence values, name subtype
facts, schemes, or publication events. Its open/closed lifecycle description
therefore does not authorize executing the table's Function/name equations
on all source bodies under F0–F2.

For the wider theorem-scoped table, the construction above is mathematical
graph bookkeeping. Its coverage follows from the supplied derivation/map,
not from an assertion that F0–F2 already admits lambdas, applications,
annotations or every nested binding. A future collector correspondence must
show that those admitted source nodes produce this exact complete graph.

One may partition a finite ledger by component and retain crossing endpoints
as shared ports: this remains finite and retains the original conjunction
under one assignment. That observation constructs a finite **presentation**,
not a generalized scheme or a freshening rule. Calling a component export a
scheme would require the missing quantification/publication contract.

## 5. Premise ledger for the reviewed SCC-instance bridge

| Bridge premise | Derived portion | Exact remainder |
|---|---|---|
| 1: finite local generation and finite scheme publication | Finite endpoints, descriptors, clauses and original use roots for the supplied §5 graph and schemas, by §3. | No inspected rule constructs a generalized scheme, chooses its quantified/local/import ports, or proves that publication preserves finite recursive back-references. |
| 2: internal live-root reuse | All recursive references of the supplied monomorphic table reuse preallocated binder endpoints. F0–F2 independently establishes its admitted graph/use structure and describes the intended open-root lifecycle. | Raw-source admission, collector/table correspondence and execution of later semantic-use rules remain outside the foundation's approved scope. |
| 3: finite external target instance, one copy per static site, canonical reuse on replay | Static external occurrences are finite; dependency-first order is available for the foundation graph. The monomorphic table uses lexical endpoint equations for them. | The table does not imply any fresh instance. Finite target-scheme publication, graph-preserving copying, permitted fresh binders, sharing, site ownership and replay reuse all remain premises for a scheme-based route. |
| 4: finite closure and stable roots/contexts | §5 invokes finite rational equality quotient and descriptor-known normalization; known-head comparisons inspect finitely many original-bound/node pairs and retain bound identities. | General comparison emission, aliases/replay/extrusion, invalidation termination, guard contexts and multi-parent evidence need rule-by-rule closure and soundness. Finiteness of the initial graph does not establish finite `J_T`/`A_T` or terminating updates. |

The equality quotient/known-head normalization statements are dependencies
reported by reviewed §5, not independently re-proved here. Their underlying
documents were not inspected. They concern a particular normalization phase,
not every subsequent solver transition. The seven closure hypotheses in
finite-context §3 remain conditional; §4's initial-context corollary explicitly
does not instantiate schemes or close replay/aliases.

For a wholly monomorphic global ledger, premise 3's copying summand is absent
and finiteness of the initial ledger follows directly without SCC induction.
This is a smaller theorem than scheme-based component inference. It does not
justify silently replacing the replacement's external-use semantics by shared
roots or declare any polymorphism policy.

## 6. Small independence witnesses for the remaining premises

These witnesses refute implications between proposed premises. They are not
claimed to be accepted raw syntax or actual Yulang solver behavior.

**Publication can unfold a finite graph.** Use one recursive definition,
whose RHS is a lambda returning a reference to that same definition. The
table gives, after its finite equations are identified,

```text
F = Function(X,F).
```

The binder, lambda, parameter and reference constitute a finite supplied
derivation; its generated descriptor graph is finite and guarded. A later
export operation could preserve this graph, or emit a separate Function node
for each unfolding depth. The latter has infinitely many output nodes while
leaving the initial table's equations unchanged. The inspected table gives
no publication rule choosing between them. One constructor back-edge suffices
to expose why finite local generation alone does not prove finite publication.
The infinite export violates bridge premise 1; it does not refute §5.

**A finite static use set does not bound repeated copying.** Take two
definitions: one literal definition and one name occurrence referring to it.
This produces one external arc and one static occurrence. A hypothetical
worklist step that attaches a fresh copy with a fresh endpoint identity on
every visit produces copies `I_0,I_1,...`. The same finite use graph is
compatible with either this accumulation or one canonical site-owned copy.
The inspected sources do not specify a freshening/replay owner. This is a
minimal external-use shape separating source-site finiteness from allocation
finiteness; it is excluded precisely by bridge premise 3.

**Finite states do not prove update termination.** A hypothetical invalidator
may alternate two dependency values forever, replaying the same canonical
comparison. No new endpoint or comparison state is needed. Finite-context
§3 premise 7 rules this out by requiring monotonicity or a decreasing finite
measure plus fair rechecks. That condition is not a consequence of the table.

These are different failure mechanisms, not repeated variants of a toy
transition checker. No source transition rule has been manufactured to close
any of them. No unresolved language meaning is selected.

## 7. Evidence, coverage and frozen handoff

There was no executable semantic experiment, oracle, seed range, enumeration,
mutation test or benchmark. The argument covers all nine supplied generator
rows. The three independence witnesses target publication unfolding,
per-iteration copying, and nonterminating invalidation respectively. Their
hypothetical downstream operations share the same finite source input and
local translation; they deliberately differ on a missing premise. They are
logical non-entailment evidence, not independent source-semantics validation.

The construction fails if a supplied node is outside the table, a reference
cannot be resolved to a preallocated endpoint, a schema is infinite/unfolded,
or a purported recursive reference recursively instantiates its definition.
These failures mean the construction's hypotheses are absent; they do not
classify a source program as ill typed. Generalization/freshening, complete
comparison emission, guards, effects, handlers, State, callback/FVIEW,
`Phi/K,D`, adapters and source acceptance remain unverified.

Checks: pinned Git-object reads; exact dependency blob identification; branch
read; lease absence check; rule-byte equality with baseline; final leased-file
scope/encoding check and artifact hash at freeze. No code, compiler tests,
builds, probes or measurements were run. At most ten sequential lightweight
commands were allowed; the handoff reports the actual count. There were no
parallel processes or heavyweight jobs. Peak memory and CPU time were not
instrumented; tool wall times cover commands only, not proof-construction time.

The artifact is frozen after the final narrow inspection. The producer's
inspection is not independent review. The primary must recheck dependency
hashes against its integration HEAD; any changed dependency requires focused
adjudication. No shared records were written.

Recommended next action: obtain or construct, in a separate authorized
research gate, the exact component scheme-publication and external-use
freshening/replay clauses, then prove their finite graph and static-site
ownership invariants. Increasing endpoint case counts cannot resolve those
missing rules.

## Commit packet

- Exact leased path: `notes/progress/2026-10-05-source-scc-source-coverage-construction.md`.
- Baseline SHA: `a4cfe9babacd0a7094d25beeec73104613b74b95`.
- Dependency hashes: table in §2; no dependency edits by this producer; current-HEAD comparison belongs to the primary.
- Claim/review status: frozen, unreviewed conditional coverage derivation; no theorem-closure or implementation authority.
- Checks already run: pinned reads, dependency identities, rule-byte equality, branch/lease checks, final path/encoding/hash inspection; no compiler or executable semantic checks.
- Proposed one-line commit message: `research: construct finite monomorphic SCC source coverage and isolate scheme premises`.
- Shared-record deltas intentionally left for the primary/curator: record finite local table coverage and monomorphic root reuse as derived within the supplied shadow; keep scheme publication, external freshening/replay and general context/update closure open; do not promote raw-source or full replacement coverage.
