# Cross-level odd/even: Yulang source correspondence

Status: frozen, unreviewed research-only static characterization; no theorem closure
Baseline: `e37a937d02c88400a381e08253d0bfd7ac45a473`
Lease: this note only
Method: source constructors, lexical lifetime and candidate-field audit; no execution

## Objective and governing premises

The assignment's flattened source is:

```yu
my odd n = my even n = if n <= 0 { true } else odd(n - 1); even(n - 1)
```

The intended nesting is the user's previously recorded indented body:

```yu
my odd n =
    my even n = if n <= 0 { true } else odd(n - 1)
    even(n - 1)
```

These are not asserted to have identical parsed CSTs. No parse was performed
for either spelling. The flattened text supplies the assigned source structure;
the indented text supplies the existing exact-source admission locator.

Authority is [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–3 and “Authority and integration”; [parent-copy SCC intrusion](../design/2026-10-10-parent-copy-scc-intrusion.md)
“Value-reference SCC clarification”, “Apply-result source-fragment ownership”,
“Nested Apply membership”, “Definition-root Value ownership”, and “Retained
boundary”; [value/type association](../design/2026-10-12-intrusion-value-type-association.md)
“Approved extrusion-event qualification”, “Qualification”, and “Implementation
and proof boundary”; and [copied-row ownership](../design/2026-10-12-value-reference-copied-row-ownership.md)
“Decision”. The [local self-recursion decision](../design/2026-10-10-local-self-recursive-binding.md)
“Selected source behavior” and “Proposed source-to-solver seam” govern temporary
local identity. The [nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–3 applies only to its named `apply/step` candidate; its broader block
interpretation is not generalized here.

Accepted premises: Value SCCs use actual value references; the nested initializer
belongs to E, the enclosing final use belongs to O; copies of type descriptions
do not copy reference edges; intrusion qualifies actual extrusion events by
their origin/receiver Values and retained polar pairs. Neither type rows nor
Function ports are automatically Value vertices. This audit supplies no native
Simple-sub typing derivation; that is the separate prover lane.

## Conditional lexical derivation

Hypotheses for the following crosswalk: a recovery-free carrier represents the
intended nested body; its Names resolve uniquely; no additional binder shadows
`odd` or `even`; unsupported If/operator forms acquire their owning admission
without changing these identities. These hypotheses are not established for
the exact text.

| Source occurrence | Existing identity/lifetime constructor on an admitted carrier |
| --- | --- |
| Outer `odd` binder O | Module `namespace()` installs its `DefId` before body lowering ([module.rs](../../crates/yu-hir/src/module.rs):1322). `DefinitionRootId` identifies the source artifact root; it does not itself emit a Value-reference edge. |
| Outer formal `n`, denoted Nₒ | `lower_plan` creates `HirParameterId(root,0)`; LocalSource pushes that parameter before its Lambda/body ([module.rs](../../crates/yu-hir/src/module.rs):1393; [local_source.rs](../../crates/yu-hir/src/module/local_source.rs):296). |
| Nested `even` binder E | `block()` allocates `HirLocalId { owner: outer root, ordinal }`, `binder_source`, separate initializer index and `LocalInitializer(E)` scope (:729–807). Artifact `owner=O` does not mean O semantically owns E's initializer. |
| Inner formal `n`, denoted Nₑ | A new parameter ordinal starts after outer parameters; `local_parameter_owners[Nₑ]=E` is recorded (:770–789). For the simple one-outer/one-inner carrier it is ordinal 1, distinct from Nₒ. |
| Inner initializer/body lifetime | `Work::Initializer` pushes temporary E only for a parameterized local function, then Nₑ (:338–375). Lookup consults lexical `latest` before module namespace (:633). The inner `n` occurrences in `n <= 0` and `odd(n - 1)` therefore select Nₑ under the hypotheses. |
| Inner body's `odd` | No local `odd` is inserted here. Lookup falls through to the unique module DefId O (:636–644). E's temporary self identity does not redirect this Name to E or to a copied type row. |
| Publication and final `even(n - 1)` | `Publish` restores the initializer guard, removing Nₑ and temporary E, then installs E (:380–386). Nₒ remains live. Final `even` selects the same HirLocalId E; final `n` selects Nₒ. Block `Restore` subsequently removes local bindings (:820–825). |

The program's inner body does not refer to `even` itself. Temporary E self
visibility is nevertheless a real construction step. Its recursion is the
cross-level O→E→O pattern, not a same-level local mutual-recursive group.

Under these hypotheses and the approved definition-root rule, the final E Name
contributes O→E, and E's O Name contributes E→O. This two-vertex, two-edge
fragment is the smallest nontrivial root SCC witness. It is a conditional
application of accepted incidence laws, not evidence of compiler emission.
Other formal/operator incidences need not be enumerated to witness this cycle;
their omission does not claim an exhaustive Value graph.

## Parser, operator and HIR seams

The existing [admission audit](2026-10-12-odd-even-source-admission-audit.md)
is reused as historical evidence, with direct constructors inspected again at
the supplied baseline. Binding syntax dispatches a strictly indented body to
`IndentedStatementBlock` ([binding.rs](../../crates/yu-syntax/src/declaration/binding.rs):329;
[statement.rs](../../crates/yu-syntax/src/statement.rs):474). `if` has a dedicated
`IfExpression` constructor ([if_expr.rs](../../crates/yu-syntax/src/expression/if_expr.rs):50).
Ordinary HIR `lower_body` substitutes an `UnsupportedExpression` error body for
an indented block ([module.rs](../../crates/yu-hir/src/module.rs):1597).
Private LocalSource `body()` requires one `OperatorChain` (:251); its expression
switch admits braced Block but no If/Branch constructor (:477–695). These are
static guarded-route facts. They establish no observed acceptance, rejection,
diagnostic sequence or inferred type for either spelling.

For `<=` and `-`, the actual parser scans the selected dynamic operator table
([operator_scan.rs](../../crates/yu-syntax/src/lexical/operator_scan.rs):39);
`SyntaxEnvironment::empty()` supplies none ([syntax_environment.rs](../../crates/yu-syntax/src/syntax_environment.rs):20).
An appropriate environment and unique value-level operator realization were
not provided or executed. Conditional on admitted infix uses, association builds
`HirExpr::Apply { operator, operands: [left,right] }` ([lib.rs](../../crates/yu-hir/src/lib.rs):358,632).
Thus the expected associated operand shapes are `Apply(<=,[Nₑ,0])`,
`Apply(-,[Nₑ,1])`, and `Apply(-,[Nₒ,1])`. This is the pre-HIR operator product:
it explicitly lacks declarations, Name resolution and DefIds (:20). It is not
the private `LocalSourceForm::Apply { callee,argument }` used for function Call.
No operator-to-resolved-callee Call constructor, tuple/curried choice, primitive
signature or effect behavior is established by those associated nodes.

Private OperatorChain formation only accepts ML/Call/colon/ascription tails;
`InfixOperatorUse` falls outside that switch ([local_source.rs](../../crates/yu-hir/src/module/local_source.rs):519).
The source calls `odd(...)` and `even(...)` have a supported CallTail→Apply
constructor with separate callee/argument indexes (:544–575), conditional on
their operands being admitted. `true` is not a Bool LocalSource constructor;
the carrier has Integer and Unit only (:113–151). Lexical identifier scanning
is distinct from contextual `if/case/catch` recognition ([lexer.rs](../../crates/yu-syntax/src/lexical/lexer.rs):685–710).
No implicit Bool binder is assumed. Even a brace substitution leaves If,
operator and Bool realization seams; such substitution is not an authorized
semantic repair of the example.

## Candidate construction versus approved Value evidence

On an admitted carrier, [candidate_source.rs](../../crates/yu-solver/src/candidate_source.rs)
:187–249 allocates occurrence components, distinct parameter recipes and formal
Name registrations. Parameter Names reuse their parameter endpoints. Scheduling
starts at level 1; Lambda preserves the level, Block visits initializers at
level+1 and installs them at the block boundary (:254–328). Thus the expected
carrier places Nₒ/final E use at 1 and Nₑ/E initializer at 2. These are rules,
not observed inference levels for the exact source.

An O Name becomes `PendingDefinitionUse` and `Action::Module`; a current local
self Name becomes a direct initializer `Action::Link`; a published E Name
becomes `Action::Local` (:369–392). Active module uses route through an open
root during module-SCC processing ([candidate_scheme.rs](../../crates/yu-solver/src/candidate_scheme.rs):870–889,938).
Local publication retains `LocalScheme { id, root, boundary }`; later E use
captures and freshens that live type graph (:1320–1387). A Link admits a subtype
constraint, not a source-reference edge (:1337–1343).

An Apply creates `CandidateRelation::Apply` and `ApplySourceInput` containing
source indexes, type endpoints, level, checking occurrence and cause
([candidate_source.rs](../../crates/yu-solver/src/candidate_source.rs):394–411).
Both local formal and Call input `owner` fields use the outer `definition_root`.
They do not retain E as the independent semantic initializer owner. Native
Call demand formation stores type Terms in `NativeInterface`
([shadow_apply.rs](../../crates/yu-solver/src/shadow_apply.rs):1335–1397;
[candidate_call.rs](../../crates/yu-solver/src/candidate_call.rs):30–59).
Neither record supplies the approved extrusion-event identity, origin E,
receiver O, or all produced pairs under that event. Typed replay also lacks
that association ([lib.rs](../../crates/yu-solver/src/lib.rs):3997;
[candidate_extrusion.rs](../../crates/yu-solver/src/candidate_extrusion.rs):763).

Pair retention itself is stronger than a hint: allocating a younger type-row
copy immediately records real `Parent { copy,parent,polarity,target }`
before bound traversal ([candidate_extrusion.rs](../../crates/yu-solver/src/candidate_extrusion.rs):90–122;
[candidate_intrusion.rs](../../crates/yu-solver/src/candidate_intrusion.rs):171–219).
The extrusion entrypoint receives only type endpoint/polarity/level. No actual
pair identity for this exact program is established because no admitted run
exists in this packet. In particular, it would be false either to describe all
candidate parent records as mere hints or to label them `(C,B)`/`(D,R)` for the
exact program without the missing construction and trace.

The intrusion consumer interns solver Value/Effect rows, walks bound payloads
and Function ports, then compares canonical type parent/copy SCCs
([candidate_intrusion.rs](../../crates/yu-solver/src/candidate_intrusion.rs):375–486).
It does not consume the approved Value-reference graph or compare an event's
origin/receiver Values. Module-use planning, local IDs, source scopes, Call
operands and parent records preserve useful construction inputs; they do not
materialize the selected O↔E Value incidence plus its associated extrusion
occurrence. The pinned inspected route therefore supplies neither complete
exact-source emission nor the corrected event-qualified correspondence.

## Checks, limits and frozen dependency snapshot

Checks: bounded `rg`, `sed` and `cat` reads plus `sha256sum` of 25 direct inputs.
No parser, inference execution, tests, builds, Oracle, mutation, seed/range
search, Git command or child delegation ran. No independent executable oracle
was used. Authority supplies the normative reference laws; current candidate
code supplies implementation facts and cannot validate its own graph meaning.
Historical notes supply locators, with owning code reread rather than accepted
as exact-source execution evidence. Some broad text captures were truncated;
decisive constructor ranges were reread narrowly. Guessed obsolete spec/docs
paths were absent; no full public specification inventory is claimed.

The primary reported clean HEAD/upstream at dispatch. This worker obeyed the
no-Git restriction and records in-worktree hashes; comparison to the pinned
commit remains the primary's integration check. No dependency change was
observed in the inspected source reads; baseline equality is not independently
certified here.

Resources: lightweight sequential read processes only, zero heavyweight
processes, one leased output. CPU/RAM and precise elapsed wall time were not
measured; the packet supplied no numeric wall/CPU/RAM budget. Requested role is
researcher; runtime task identity is `/root/odd_even_yulang_source_bridge`.
Project defaults are `gpt-6.1-sol/high`, researcher has no model pin; observed
effective model/effort are unavailable. No model-policy change occurred.

SHA-256 snapshot (paths are relative to repository root):

```text
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b  notes/design/2026-10-10-parent-copy-scc-intrusion.md
0063b88d17104f85182439d80360e42f8f99a5af4793eab70640a66f955ede25  notes/design/2026-10-12-intrusion-value-type-association.md
7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd  notes/design/2026-10-12-value-reference-copied-row-ownership.md
38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895  notes/design/2026-10-10-local-self-recursive-binding.md
750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0  notes/design/2026-10-06-nested-block-function-source-realization-addendum.md
eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544  crates/yu-syntax/src/declaration/binding.rs
dc18a26663b4351b774a930bfcc8b343cf0c41651960b49ec2f2c6e744b0e89d  crates/yu-syntax/src/statement.rs
cd7b6ccd9e0bf92d90de5a0e9e5cfdede5f38990bacb12d60fff8e9fdf8edc2d  crates/yu-syntax/src/expression/operator_chain.rs
77ae21897cf23988c394686cb823b4f3d731b53aa483566a73c67295a7326fba  crates/yu-syntax/src/expression/if_expr.rs
145002d4254aaf186fa5176d0c6c56d89c88235e29e2da9ab1d33790a31ca3a2  crates/yu-syntax/src/lexical/operator_scan.rs
9a18b24628844e2e5ab1bcc1dc26e05cb14bdb6fca35a3a2d31f45ba5180b3a1  crates/yu-syntax/src/lexical/lexer.rs
3f1e2c97c49318e02c595aa739bfb48532f7631d38afaaac4d8dfca6142cb973  crates/yu-syntax/src/syntax_environment.rs
51e5fa543cd65ced879a7561e0d602e686a072378cde5ec16a20b4afb875fc0a  crates/yu-hir/src/lib.rs
943dcab6440ffb70061f08641afa13fa8b36c5689a326d07288b9593e17ba8f5  crates/yu-hir/src/module.rs
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  crates/yu-hir/src/module/local_source.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35  crates/yu-solver/src/candidate_call.rs
cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411  crates/yu-solver/src/shadow_apply.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
2bb4b6a1389dc054f6a16a1bf566b68cba7648cd31355a4b10c29b1f91d2cb06  notes/progress/2026-10-12-odd-even-source-admission-audit.md
2063fb4e1143c39972dac352a32534f4843d8286e2e38b1ab793e9221b0f709b  notes/progress/2026-10-12-extrusion-occurrence-source-audit.md
```

Failure/invalidation conditions: altered lexical resolution/publication;
changed source-owner or event law; new If/operator/Bool admission; or revised
consumer/retention fields. Unverified scope includes actual exact-text CST,
complete source Call elaboration, graph emission, event identity through replay,
generalization and independent fresh uses, intrusion equality preservation,
soundness, principality, effects, termination and public/F5 replacement. All
original gates remain OPEN. This producer is not an independent reviewer.

One recommended next action: primary attaches this identity/admission crosswalk
to the existing Call-demand/extrusion source gate and requests the smallest
authorized event-construction packet retaining E/O and produced pairs; exact
source admission remains an explicit prerequisite for execution evidence.

## Commit packet

- Exact path: `notes/progress/2026-10-12-odd-even-yulang-source-bridge.md`.
- Baseline: `e37a937d02c88400a381e08253d0bfd7ac45a473`; changed dependency hashes:
  none observed, pinned comparison deferred to primary (snapshot above).
- Status: frozen unreviewed static characterization, conditional lexical/SCC
  application only; no production or proof promotion.
- Checks: owning source ranges read; 25 SHA-256 values captured; no execution.
- Proposed message: `research: trace cross-level odd/even Yulang source identities`.
- Shared deltas left to primary/curator: link this note in `tasks/current.md`
  and the owning theory gate; preserve exact-source admission, approved graph
  construction, extrusion-event association and all parent gates as OPEN.
  No shared task/index/authority/question/production path was edited.
