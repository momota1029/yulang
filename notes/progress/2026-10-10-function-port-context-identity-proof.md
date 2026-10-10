# Function-port context identity: bounded constructive derivation

Status: unreviewed research-only conditional derivation and source inspection;
no source theorem, implementation conformance, soundness, or gate closure.
Assigned baseline: `3c42971ea`.
Exclusive output lease: this file only.
Worker identity: `/root/function_port_identity_proof`; constructive proof leaf,
with no delegation. Requested runtime: `gpt-6.1-sol` / `high`. Observed effective
model, effort, and launch-role metadata: unknown in this child session. The
registered `.codex/agents/prover.toml` has neither a model nor an effort pin;
`.codex/config.toml` requests Sol/high subagent defaults. Configuration and the
assignment do not establish the effective runtime settings.

Primary follow-up: the later conditional
[Function-port effect-order proof](2026-10-10-function-argument-effect-contravariance-proof.md)
resolves the missing child-prefix composition premise from the frozen Oracle
source; implementation commit `0d2986b6f` now constructs that ordered context
for the approved local shape. This note remains an unreviewed identity and
recoverability argument. It does not prove nonidentity execution, fresh-use
transport, or lifecycle behavior.

## Objective, authority, and dependency snapshot

Use a direct identity argument, then trace the actual Function child constructor,
admission, queue, and context consumer. The governing source is
[`contextual-attachment-admission-design`](../design/2026-10-10-contextual-attachment-admission-design.md)
§3, especially lines 106–110 (exact operation order and shared inputs), and §4,
lines 126–147 (relation authority, Function ports, and omission). Its bounded
private-carrier authority and §6 exclusions apply. §3.1's approved attachment-set
grouping is retained; it does not decide Function context composition.

The primary instructed this leaf to use the available workspace files and
explicitly mark equality with the assigned HEAD as unverified. No Git command
was permitted or run. The source claims below therefore concern the following
inspected workspace snapshot, not independently authenticated commit contents:

| Dependency | SHA-256 of inspected file |
| --- | --- |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `crates/yu-solver/src/candidate_context.rs` | `470a5d45b6a7d6d2faf55de388908fc6b724dac7a14af87a3ff67a227b975ac5` |
| `crates/yu-solver/src/lib.rs` | `9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1` |

These hashes were the same in two reads during this assignment. Baseline
equality and changed hashes relative to `3c42971ea` remain unverified. Relevant
operating rules and the `yulang-proofs` skill were read. Shared task/index
records were inspected for context only and are not authority substitutes.

## Authority sufficiency before derivation

§4 fixes which transformation belongs to each ordinary Function port:

| Field | Endpoint direction | Transformation of processing parent context |
| --- | --- | --- |
| Argument Value | Reverse | `Swap` |
| Argument Effect | Reverse | `Swap` |
| Result Value | Preserve | Preserve |
| Result Effect | Preserve | Preserve |

It does **not** fully specify an operation combining the transformed processing
parent context with an independently constructed child source-local context.
§3 requires order to be retained once constructed; it does not supply that
missing order. §4's directed-mix rule is explicitly for opposite bound replay,
and cannot by itself authorize reusing that operation at a Function port.
Its wrapper rules identify local operations but provide no explicit insertion
position relative to the port-transformed parent. `both` is restricted to the
certified source-owned inferred-entry flow and is not a generic composition
operator for ordinary ports.

Consequently this note does not define or select that composition. The two
derivations below stop at identity and conditional necessity.

## Frozen statements, binders, and exclusions

Work within one fixed live relation/context state, with fixed endpoint
canonicalization and source-local data. IDs mean their identities in this
state; no claim compares numeric IDs across rollback, fresh uses, or sessions.
Let `P` be the set of typed canonical pairs, including component kind. Let `C`
be valid exact retained context IDs in this state, and let an admitted relation
key be `K = (q,c)` in `P × C`. All attachment identities, member ordinals,
resolved operands, lexical scopes, origins, providers, and residual lineages
remain those of the supplied state; none are independently chosen or merged.

**ID statement (conditional identity lemma).** For every `q ∈ P` and every
`c₁,c₂ ∈ C`, if `c₁ ≠ c₂` and both `(q,c₁)` and `(q,c₂)` are admitted, then
their relation keys differ. The projection `π(q,c)=q` is noninjective on these
two keys, and no single-valued reconstruction from `q` alone recovers the
exact admitted context on both relations.

The existence of such a pair of admissions is a hypothesis, not a conclusion
about any Yulang source execution. An endpoint lookup may enumerate a set of
relations; that does not select which member is the exact processing relation.

**PORT statement (conditional retention necessity).** Fix one ordinary field
`f`, one child pair `q_f`, and its exact child-local construction `L_f`. Let
`r₁,r₂` be processing Function relations having the same parent pair but exact
contexts `c₁ ≠ c₂`. Assume:

1. The selected construction must retain the field-specific transformation
   `T_f(c)` of the *actual processing* relation's context, rather than a
   context regenerated from its endpoints.
2. A separately approved port construction, if supplied, retains both
   `T_f(c)` and `L_f` in their specified roles/order/shared-input graph. In
   particular, the designated retained parent input can be read from its
   result. This is an explicit conditional faithful-retention premise, not an
   additional approved implementation rule.
3. Exact structural interning preserves those input identities; it does not
   identify nodes merely because they have equivalent effect observations.

Here `T_f` is Preserve for Result/ResultEffect and the exact unary `Swap` node
for Argument/ArgumentEffect. Then a child constructor whose context depends
only on `q_f` and fixed `L_f` cannot satisfy these retention premises for both
parents. This proves necessity of retaining the exact parent input; it does
not establish a concrete port composition or its semantic correctness.

Excluded conclusions: actual source reachability of the hypothesized pair,
activation or complete replay, Function context semantics, filter discharge,
complete Call meaning, effect hygiene, soundness, required principality,
termination, concrete formal-row admission, and public/default/F5 cutover.
No new scope/binder restrictions, annotation requirement, supported-input
restriction, context quotient, or independent marginal witness is introduced.

## Direct derivation

For ID, `(q,c₁)=(q,c₂)` would imply equality of their second components, contrary
to `c₁≠c₂`. Both project to `q`. If a function `R:P→C` recovered exact context
for both admitted relations, it would satisfy `R(q)=c₁` and `R(q)=c₂`, again
contradicting `c₁≠c₂`. This is an information-loss argument about exact
identity, not a claim that these contexts have different observable effects.

For PORT, Preserve is injective. Exact unary `Swap` construction is also
injective on its retained input: `Swap{input:c₁}` and `Swap{input:c₂}` have
different structural keys when `c₁≠c₂`. Successful exact interning therefore
assigns them distinct IDs. No involution or semantic simplification of Swap
is assumed, including at identity.

Suppose a child root is chosen from `q_f,L_f` alone. Both parents present
identical arguments to that choice, so its root is identical in both cases.
By the faithful-retention premise, reading its designated parent input must
return `T_f(c₁)` in the first case and `T_f(c₂)` in the second. A single root
cannot return both distinct inputs at the same designated position. This
contradiction proves PORT. Giving the constructor the actual processing
RelationId supplies the missing identity input; it does not determine how to
combine its context with `L_f` or justify execution of the resulting graph.

No lemma assumes transition generation by a checker. The mathematical proof
uses only the frozen identity hypotheses; source inspection below separately
identifies which hypotheses have construction evidence and which remain open.

## Actual constructor and consumer bridge

All following locators are in the hashed workspace snapshot above.

| Owner / consumer | Source locator | Established inspection fact |
| --- | --- | --- |
| Exact key shape | `candidate_context.rs:80`, `:104` | `ContextExpr` stores exact typed operation/input handles; `RelationKey` stores the complete typed pair and ContextId. |
| Structural node interning | `candidate_context.rs:1256` | `State::context` checks valid inputs and interns the full expression key. It does not simplify Swap or replace exact child inputs. |
| Relation interning | `candidate_context.rs:1418` | `State::relation` keys its map by `(pair,context)`. `previous_on_pair` retains other relations on that pair rather than identifying them. |
| Function endpoint owners | `lib.rs:13249`, `:13270` | Positive/negative Function children come from the actual stored Function terms. |
| Function child generation | `lib.rs:12023` | The four child pairs reverse Argument/ArgumentEffect endpoints and preserve ResultEffect/Result endpoints. |
| Processing relation | `lib.rs:11835`, `:11859` | The route seeds context, and each popped work item installs its retained RelationId as `context.processing` before context execution. |
| Child-local context | `candidate_context.rs:1606` | `candidate_context_source(pair)` returns `PrefixLeft(weight,IDENTITY)` for a closed upper Effect allowance, otherwise identity. It does not read the processing parent context. |
| General child admission | `candidate_context.rs:1652` | `candidate_context_admit` creates the child key from that local reconstruction. It separately selects the retained parent when its pair matches and records a Derived dependency; that dependency does not change the child key. |
| Function port incidence | `candidate_context.rs:1675` | `candidate_function_port_admit` first uses general admission, then records the exact processing RelationId, field, and Swap/Preserve label in `Dependency::FunctionPort`. It constructs no transformed executable ContextExpr. |
| Dependency effect | `candidate_context.rs:1454` | FunctionPort/Derived add provenance edges; the dependency label does not rebuild the child's retained context. |
| Child queue | `lib.rs:12066`, `:12123` | The Function loop passes the admitted child RelationId into `TypedWorkItem`; enqueue preserves that supplied handle. |
| Context execution | `candidate_context.rs:1783` | `candidate_context_execute` reads the child relation's `key.context`, asserts its pair matches the task, and passes that root to filter validation. It does not interpret the FunctionPort label to transform a parent context. |
| Executable fragment validation | `candidate_context.rs:1731` | The zero-word consumer accepts validated `PrefixLeft(weight,IDENTITY)` and ordered Replay nodes, and rejects the other operation forms. Executable Swap support is not established by recording its incidence. |
| Retained-input completeness | `candidate_context.rs:494` | Selected FunctionPort dependencies are explicitly classified as inert evidence. |

The admission-to-queue-to-consumer path above is an actual source-code control
path, conditional on reaching its Function decomposition branch and on its
successful allocations/validation. It is not a derivation that a source
program reaches the distinct-context hypothesis. The present source retains
the parent relation identity as provenance, but executes the independently
reconstructed child context. That is evidence of an unresolved operational
bridge for contextual ports, not evidence that the current identity-only
fragment produces an unsound source result.

Bound/replay owners retain contexts by separate mechanisms:
`candidate_context.rs:1846` uses the selected parent and its post-check context
at bound attachment; `:1906` reads both bound relations' contexts and builds
an ordered Replay context when nonidentity input exists. `:1560` returns
identity only for a relation marked discharged. These mechanisms explain why
endpoint IDs are not the representation's sole context authority. This note
does not prove all resulting bounds are activated or that a nonidentity
Function processing relation can be generated by source.

## Precise obstruction and proof-obligation economy

The missing premise is an approved source-owned construction rule
`PortContext_f(exact_processing_parent_context, exact_child_local_context)`
specifying operator, order/bracketing, shared inputs, and the responsibilities
for executable checking/discharge. This notation names the missing rule; it
defines no new representation or semantics. Neither the port row nor the
wrapper/replay rows supplies that complete rule. Source reachability of the
distinct-context parent witness is a separate missing operational premise.

Only one direct derivation was attempted; no two-attempt threshold was reached.
The economy audit nonetheless identifies endpoint reconstruction as D debt:
the processing loop already knows the exact RelationId, and the child admission
point is the owner that can carry its context into the approved construction.
The faithful executable transport requirement concerns A safety/correctness
and potentially B ordinary inference. Retaining existing authority at this seam
can remove the identity-reconstruction obligation, but cannot decide the
missing composition policy or prove semantic preservation. Classification is
not proof progress or gate closure. No additional reconstruction layer is
proposed.

## Verification, resources, and handoff

No executable checks, tests, builds, probes, benchmark samples, or Git commands
ran, as instructed. Evidence consists of `cat`, `sed`, `rg`, `nl`, and
`sha256sum` source inspections plus the written derivation. Hash comparison is
snapshot evidence only. No CPU/RAM/wall-time measurement was taken; no heavy
process, external recipient, or additional worker was started. The primary
remains the verification and independent-review owner.

Changed path: this exact leased note only. No compiler, expectation, rule,
configuration, question, shared task/index/theory record, or Git state was
edited. Independent review is pending; the producer does not certify this
artifact. Writes stop at this handoff.

Next action: the primary resolves the precise parent/local composition premise
against an in-scope authoritative source or records the genuine missing
decision before implementing or proving executable port transport.

## Commit packet for the primary

- Exact lease: `notes/progress/2026-10-10-function-port-context-identity-proof.md`.
- Assigned baseline: `3c42971ea`; equality to inspected files unverified under
  the no-Git instruction. Dependency hashes are listed above; changes relative
  to that baseline are unknown, and no hash drift was observed during reads.
- Claim/review status: unreviewed research-only conditional identity and
  retention derivations; missing composition and source-reachability premises
  remain open. No theorem or production status promotion.
- Checks already run: none. Read-only source inspections and SHA-256 snapshots
  only; no tests/builds/Git.
- Proposed checkpoint message: `research: record conditional Function-port context identity derivation`.
- Proposed shared-record delta, left to primary/curator: link this conditional
  note and record the exact missing port composition/operator/order premise;
  retain source reachability, executable transform/discharge, soundness,
  hygiene, principality, and existing Packet 1 readiness gates as open. Do not
  change authority or mark any gate CLOSED from this artifact.
