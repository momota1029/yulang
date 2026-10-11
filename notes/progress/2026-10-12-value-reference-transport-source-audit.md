# Value-reference transport: bounded source audit

Status: frozen, independently spec-reviewed bounded non-authoritative research characterization
Baseline: `874d43756cc44ce1787b4ca30a7595eeff1bc121`
Branch: `research/simple-sub-intrusion`
Lease: this note only; no compiler, test, semantic or integration authority

## Objective and authority

Determine whether approved source incidence together with ordinary Simple-sub
extrusion/freshening determines Value-reference transport. This complements
the constructive proof lane; it supplies source locators and a minimized
conditional discriminator, not a proof of intrusion equality preservation.

The governing [parent-copy decision](../design/2026-10-10-parent-copy-scc-intrusion.md)
sections are **Selected operation and compiler responsibility**,
**Value-reference SCC clarification**, **Apply-result source-fragment ownership**,
**Nested Apply membership**, **Definition-root Value ownership**, and
**Retained boundary**. The [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5 and **Authority and integration** preserve proof/construction/cutover
boundaries. Rules read: `rules/research-lab.md`, `rules/design-authority.md`,
`rules/git-concurrency.md`, and `rules/compiler-engineering.md`, especially
**Natural compiler behavior and proof-obligation economy**.

Accepted decisions remain fixed:

- An Apply result owns resolved Names in its callee/argument fragment,
  recursively through nested Apply operands; containment creates no edge.
- A published definition root owns Names in its own initializer/body. A nested
  initializer belongs to its own declaration root. Roots are not thereby
  identified with Lambda, Apply or Block rows.
- The intended odd/even example has root edges `O → E` and `E → O` across
  levels. These edges do not establish a retained polar parent/copy pair.
- Comparison judgments and parent records do not create Value-reference edges.

The earlier [transport note](2026-10-11-value-reference-transport-proof.md)
§5 contrasts source-fragment and returned-image Apply content. That specific
choice has subsequently been settled by the approved Apply rule. This audit
does not reopen it.

## Source constructors and the actual copying operations

Locators below are relative to `crates/`, except the external reference.

| Responsibility | Inspected constructor/consumer | Established bounded fact |
| --- | --- | --- |
| Local binder and scope | `yu-hir/src/module/local_source.rs:338–372,740–805` | The temporary self binder precedes parameters; publish restores temporary bindings and exposes the local. Local identity, initializer identity and parameter ownership remain distinct. |
| Active recursive use | `yu-solver/src/candidate_source.rs:300–309,369–390` | An active local Name links to the existing initializer endpoint. A later published use schedules `Action::Local`; a module Name schedules `PendingDefinitionUse`. These actions are not explicit approved incidence edges. |
| Levels | `candidate_source.rs:254–306` | Lambda/Apply preserve traversal level; local initializers enter the next level; the block final expression stays at the block level. Levels do not filter approved reference adjacency. |
| Apply ownership evidence | `candidate_source.rs:394–409` | The planner retains callee, argument, result, occurrence, level and definition owner. This is useful construction evidence; the inspected record is not an emitted resolved-Name adjacency list. |
| Lambda and definition root | `candidate_source.rs:445–459,477–493` | Lambda retains its parameter/root/body endpoints. Definition publication links the body endpoint to a separately allocated root component. Neither fact identifies the rows' source-owned content. |
| Ordinary extrusion | External `Typer.scala:131–157` | The cache key is `(Variable, polarity)`. Positive copies get extruded lower bounds and an upper-bound link from the parent; negative copies get extruded upper bounds and a lower-bound link from the parent. These are type operations. |
| Ordinary freshening | External `Typer.scala:166–188,201–207` | One map per use preserves repeated variable identity across both bound sides; variables at/below the boundary remain unchanged. A fresh description is not a newly resolved source binder. |
| Native bound transport | `candidate_extrusion.rs:308–323` | `Work::Bound` looks up the copied endpoint and transports bound provenance. This establishes an existing bound operation, not Name-incidence transport. The row-allocation portion was not recovered in full within this read budget. |
| Native shared anchors | `candidate_scheme.rs:301–325,567–572,1008–1019` | Capture eligibility is `level > boundary && !non_generic`. Freshening uses one canonical-row map; older/nongeneric rows remain shared, and their mutable bounds remain in the session. |
| Native scheme payload | `candidate_scheme.rs:36–82,965–979` | The inspected Graph contains rows, nodes, bounds and effect/context evidence. Freshening prepares rows and restores retained bounds. No separately named source Name-incidence payload appears in these inspected definitions. This is not an exhaustive absence claim over the crate. |
| SCC qualification | `candidate_intrusion.rs:390–488` | The consumer traverses both bound sides, Function ports and effect dependencies, then compares parent/copy component numbers. Parent polarity/target are provenance, not graph edges. A bridge from this adjacency to approved source incidence is still required. |

The external reference is
`/home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala`
at `9bae772624c23b52a93c1b226157e16898b4d9db`. Its `Lam`, `Var`, `App` and
recursive `Let` constructors are at lines 48–84. They construct types and
constraints, not an approved Value-reference graph. The pinned local paper
`/home/momota1029/rust/simple-sub-reference-paper.pdf`, Figure 7 and the adjacent
extrusion/freshening discussion,
describes copying cyclic type-bound subgraphs with a polar cache; its
freshening discussion describes replacing variables above a level. Neither
inspected passage supplies copied source-owner or Name-target equations.

[Local self-recursion](../design/2026-10-10-local-self-recursive-binding.md)
**Selected source behavior** and **Proposed source-to-solver seam** require one
open monomorphic root for active recursion and ordinary freshening after
publication. [Source Generalize](../design/2026-10-08-source-generalize-definition.md)
§2 fixes actual binding/provider objects while allowing fresh inferred
descriptions, with initializer/environment Shared binders shared once. These
are constraints on any proposed transport, not permission to retarget a
resolved Name to another binding. The referenced full Generalize construction
§§3–5 was not audited in this packet.

## Exact missing premise and claim boundary

For an admitted resolved occurrence `n`, let `binder(n)` be its fixed binding
identity. For a source owner `s`, the approved rule fixes the edge from its
actual owner row to the actual row of `binder(n)`. If a copied owner is proved
to retain that same Name and the same binding-row interpretation, its target
is already fixed. A transport proposal may not substitute another binder.

What the inspected rules do not supply is the construction equation assigning
source-owned content to a polar type copy, and the relation between a fixed
binding object, its solver row and each fresh description frame. In particular:

1. Which copied rows inherit the resolved occurrences of an Apply or root?
2. Which map interprets those occurrences when one type variable has two
   polar copies, while ordinary freshening uses one row map?
3. When a target is outside the copied fragment, does its binding anchor stay
   fixed, and how does the target's current description enter that equation?
4. How do later uses preserve the same source binding without collapsing
   independent generic description frames or freshening shared anchors?

These are a source/construction seam. Recording existing occurrence, binder,
owner and frame identities is reconstruction debt (class D); choosing content
or a target interpretation that changes the approved graph requires authority.
The required SCC/equality result remains class A/B and OPEN. This audit does
not prove that two competing laws both satisfy all governing semantics, nor
prove that the omitted full Generalize construction cannot discharge the seam.
Thus it establishes insufficiency of the inspected premises, not a globally
certified semantic ambiguity or a merely mechanical implementation fix.

## Smallest conditional transport discriminator

This is a candidate graph witness, **not a source-qualified counterexample**.
Assume the following independently supplied premises:

- `p` and `c` are a distinct, genuinely retained parent/copy pair.
- Before copying, the source-owned value of `p` has a self Name incidence
  `p → p`. After allocation, a separate actual source-reference construction
  supplies `p → c`. Its source realization is not established here.
- Copying gives `c` a description of the same self occurrence. The two candidate
  completions differ only in interpreting its target, not in ordinary type
  constraints or retained parent provenance.

| Candidate completion | Edges after copying | Qualifies `(c,p)`? |
| --- | --- | --- |
| Binding-anchor target | `p → p`, `p → c`, `c → p` | Yes: each reaches the other. |
| Copied-description target | `p → p`, `p → c`, `c → c` | No: `c` cannot reach `p`. |

The second completion is a hypothesis about descriptions, not an approved
retargeting of the source binder. It fails immediately if the required target
is the original binding row `p`; the first fails if copying does not give `c`
the source occurrence at all. The unresolved owner/row/frame equation must
decide these conditions before this discriminator can be applied.

Two vertices are necessary for a distinct pair, so the witness is minimal in
vertex count. Removing the independently supplied `p → c` destroys the
positive qualification; removing the inherited self occurrence removes the
candidate difference. No subtype or parent edge is used as a reference edge.
User permission for references across an extrusion family does not establish
the concrete `p → c` source constructor. The accepted `O ↔ E` example cannot
be substituted for either pair endpoint.

## Checks, limits and frozen dependencies

Five lightweight read batches were used after the primary explicitly expanded
the original two-read budget. The first two captures truncated; decisive rules
and source windows were recovered in later bounded reads. Native extrusion
allocation and the complete Generalize construction remain explicit omissions.
Paper text was extracted with `pdftotext -layout ... -` and filtered to extrusion
and freshening windows; no paper-wide correspondence claim follows.

HEAD initially matched the baseline and status was clean. External reference
HEAD matched the pinned reference SHA. No dependency was edited by this leaf.
The following SHA-256 values freeze the inspected direct inputs; baseline blob
equality for every dependency was not checked and remains with integration.

| Dependency | SHA-256 |
| --- | --- |
| Parent-copy design | `fd07ecc76e9df0b1937f72e74ce4a35b982b51031b04022672228e307d03615c` |
| Top-level principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| Odd/even derivation | `238e21c0a027aa9f0ca14c563c3fbaa11188ee268e8b819a049f81dd6afd5830` |
| Exact-source admission audit | `2bb4b6a1389dc054f6a16a1bf566b68cba7648cd31355a4b10c29b1f91d2cb06` |
| Previous transport note | `4081b6ef45c21007ce2246840e64538b9bddaf4c30f453fb8a88350317ab6789` |
| `candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| Reference `Typer.scala` | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| Reference paper | `5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698` |

Artifact verification: relative Markdown target existence and trailing
whitespace checks. Zero tests, builds, Oracle runs, executable graph probes,
mutations, randomized seeds/ranges, child delegation or Git mutations.
No independent oracle was used: the graph calculation explicitly assumes its
edges and only discriminates the two supplied target equations. CPU/peak RAM
were not measured; read commands completed in under a second each. Work stayed
within the 30-minute wall-time allocation, with no heavyweight process.

Unverified: exact-source admission, concrete `p → c` realization, generic versus
shared-target histories, rollback/replay/diagnostic paths, all-source Call/effect
transport, equality soundness and principality. No self-review or closure claim.

Recommended next action: primary adjudicates the copied-owner/binding-row/frame
equation against the full adopted Generalize construction, then supplies that
exact established or missing premise to the existing proof owner. A further
toy graph probe will not establish it.

## Commit packet

- Exact leased path: `notes/progress/2026-10-12-value-reference-transport-source-audit.md`.
- Baseline: `874d43756cc44ce1787b4ca30a7595eeff1bc121`; reference baseline:
  `9bae772624c23b52a93c1b226157e16898b4d9db`.
- Dependency changes: none by this leaf; direct snapshot above. Full baseline
  comparison and any subsequent invalidation belong to the primary.
- Review: independent `spec_auditor` found no issue within exact-conformance
  scope. The conditional graph witness is not a source counterexample or
  approved semantic alternative, and does not close transport or intrusion.
- Checks already run: bounded rule/source/paper reads, initial HEAD/status,
  external reference identity, dependency SHA-256 snapshot, artifact link and
  whitespace validation. No tests/builds/Oracle.
- Proposed message: `research: audit Value-reference copy ownership and target transport`.
- Shared-record deltas intentionally left to primary/curator: preserve the
  resolved Apply/root meaning; record the owner/binding/frame seam and concrete
  source realization premise; retain parent SCC/equality and cutover gates OPEN.
  No task, theory index, design or question-board file was changed.
