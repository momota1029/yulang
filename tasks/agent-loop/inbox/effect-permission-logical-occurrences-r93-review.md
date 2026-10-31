# R93 frozen independent review

Verdict: **STATIC REVIEW PASS for the occurrence-provenance candidate; kernel
acceptance, elaborated types and transitive axiom results remain UNVERIFIED.**
No BLOCKING, major or minor correctness finding. This verdict permits the
primary to consider the separately authorized bounded check; it does not
establish checked theorem completion or promote a parent/production gate.

## Evidence and independence

I read the admitted contract and candidate declarations/constructions before
reading either producer handoff. I then compared both handoffs against the
candidate and its two pinned source dependencies. Producer explanations were
not evidence for the initial assessment. Applied `yulang-lean-proofs` under
the packet's explicit no-execution boundary. Read the root operating map,
design-authority rule, original parent statement, selected source-Generalize
authority and its binder/scope construction, and inference principles.

The following SHA-256 values were independently recomputed and match the
frozen assignment:

| Input | SHA-256 |
| --- | --- |
| R93 contract r1 | `e762c73cfd33c60428bb632ef4441bac8f4df2f579a6e0a9c394c5e6ac9b0c77` |
| `SourceLogicalOccurrencesR93.lean` | `3c3ac12f0e652b361925ff0d80db78b4bae96f4bd2cc83f3f8346d6e5db54192` |
| R93 proof handoff | `b8124915768462011bd4fe74a0a0b92cfc9ae3b140a88cde4c8708b06fb7b164` |
| R93 source handoff | `4f1688000679f03c24a04ca84708b755f706399990b5c003291d7d19dce3ada6` |
| `OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |

## Correctness assessment

The construction addresses the syntactic provenance gap at its source owner:
`sourceIndex` encodes unchanged `sourceRules`, rather than inferring ownership
from a flat Binder/site or from successful admission. It does not repair the
semantic admission/readout gap; both handoffs correctly retain that gap.

`advance` and `encodeTree` cover all ten RuleTree constructors; forest nil/cons
are covered in `encodeForest`, `advance` and the route induction. Rule descent
and forest positions are separate steps. Unary wrappers enter on false;
choice and forest sibling alternatives have disjoint false/true prefixes.
No branch uses site/name freshness, binder equality or an ambient path naming
convention to identify positions. Repeating sites, identical binders, identical
sibling subtrees and empty forests therefore do not merge structural paths.
An invalid step returns none. Scope accumulation occurs only on the selected
descent, so one sibling's scope does not leak to another.

The syntax walker and index are separate definitions. `encode_lookup` compares
them for arbitrary scope, cursor and route. `inventory_iff_lookup` supplies both
membership directions, and `source_membership_iff` instantiates this at every
Source category without a typing/success premise. `source_provenance` recovers
the precise reached existential node, full Binder, ordered enclosing syntactic
frames and exact original generated body. Every enclosing exists/forall,
initializer, execution, shared, publication, restoration and alias wrapper is
retained as syntax. This is not a semantic environment/restoration theorem.

At candidate lines 205–213, `full_route_unique` quantifies over any two inventory
members at one complete route and concludes equality of their whole Occurrence,
without a distinct-site assumption. That is the admitted functional uniqueness
claim. It is not a separate `Nodup` theorem about list enumeration multiplicity.
I considered identical duplicate list entries: the current root/false/true
inventory construction is structurally disjoint, and I found no duplication or
distinct source position collision. Absence of an additional `Nodup` declaration
does not invalidate the stated functional theorem or create a correctness
finding for this packet.

App at candidate lines 261–282 matches generator lines 111–123, including the
conditional singleton-formal premise, both exact checking goals, ordered
callee/argument children and the ViewLogic binder. An outer annotation adds
exactly rule-to-forest and forest-to-head steps and adds no scope frame.

Lambda at candidate lines 284–330 matches generator lines 132–168. The eight
initial false steps reach `enteredBody`; Value adds the actual return/rebind
execution step, Computation does not. The remaining false/false/true/false
steps traverse Shared, the checked-body sequence, its forest tail and the
second child's EventProof introduction. The unannotated route lengths are
13 for Value and 12 for Computation; annotation adds two. `bodyScope` preserves
Description, ViewLogic, Invocation, Receipt, optional Return/rebind and Shared
in order. The target EventProof is correctly absent from its own enclosing
scope. `formalContext` retains the formal's annotation/entry/single-use flag;
`bodyContext` reproduces the original pattern binding filtering. `bodyRule`
retains both local atoms, the exact computation check, and unchanged
`sourceRules inner body`. Pattern and body are siblings in `checkedBody`;
the body context retains the pattern's source bindings.

The exact equations universally quantify Context, incoming scope, source
operands, Formal and Mark. Their proof branches cover both outer annotation
options and both formal entry modes; formal annotation and raw body/pattern
data remain arbitrary. No source constructor is filtered out: the generic
claim operates on every unchanged generated RuleTree, including continuation
and optional/container branches.

## Audit surface and claim limits

The ten declared theorems each have an embedded fully qualified `#check @...`
and `#print axioms ...` pair at lines 353–372: `inventory_iff_lookup`,
`encode_lookup`, `observe_eq_follow`, `source_membership_iff`,
`full_route_unique`, `source_provenance`, `app_exact`, `lambda_body_exact`,
`app_inventory`, and `lambda_body_inventory`. Static inspection found no proof
holes, project axiom declarations, native evaluation or kernel-check bypass.
This is not a transitive axiom audit result. Private-helper reduction and tactic
elaboration remain to be tested by the primary's authorized execution.

The source mapping to App/Lambda and raw operands is directly supported by the
two inspected dependencies. The stored subtree is a generated RuleTree body,
not a general inverse map to a raw Source subterm. The source handoff's claims
about `ActualKey`, `localAdmissions` and `decodeFrame` name three additional
modules outside this review's permitted source dependency set; I did not
independently inspect or authenticate those modules. They remain source-lane
evidence, not facts certified by this review. Both handoffs explicitly leave
route adaptation and semantic admission/readout open, so this limitation does
not affect the occurrence-only result.

No result establishes admitted joint payloads, selected contract transport,
semantic restoration, original A/B claims, native correspondence, principality,
termination, full effect hygiene or production authority. Those original
quantifiers and parent obligations remain unchanged and OPEN.

## Resource and writes-stopped receipt

One independent reviewer, no children. Lean/Lake/checker/build/test executions:
**0**. No scratch, cache, environment, project copy, worktree, Git/index/branch
operation, compiler edit or dependency edit. Only read-only file inspection,
hashing and this exact leased review output were used. No heavy process or
background work; CPU/RSS and elapsed wall time were not separately instrumented.
The review stopped within its finite 500-second assignment.

Writes stopped after creating this receipt. The only written path is
`tasks/agent-loop/inbox/effect-permission-logical-occurrences-r93-review.md`.
No further writes or execution are active. Primary owns adjudication and any
subsequent execution authorization.
