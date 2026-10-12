# Oracle effect hygiene: document lineage, corrections and transfer premises

Date: 2026-10-12
Status: bounded research characterization independently reviewed; no parent theorem or implementation gate closed
Method: pinned-document dependency and supersession audit, with two small conditional derivations
Lease: this file only; no production edits, tests, runtime probes, or Git mutations
Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Archive baseline: `7915390c9cc8fb7f39eb04123abc0c7b581ea4a0` (`9b853468f^`)
Yulang comparison baseline: `67830dce14e6987b37e47b2540c204fcd06a92c6`

Review integration (primary): the same fresh `compiler_referee` independently
checked the URR-v3 withdrawal, MPC conjunction witness, DPN allocation-rank
withdrawal, runtime protocol, generalization distinctions and scoped approvals.
No correctness findings. All 18 historical and seven current dependency hashes
were checked, including current baseline/live equality. Full later appendices,
external approval receipts and implementation correspondence were not reviewed.
The original producer packet below retains its pre-review status; this paragraph
supersedes that status only. Original producer SHA:
`0cbbff5f6f1ce2e8a4fbd630348df6add17a723d77508c01940bb0f310b03d9b`.

## 1. Result and authority boundary

The documents establish a lineage of selected contracts and explicitly corrected
premises. They do not establish a general source-to-runtime hygiene theorem.
June's weighted model, its source construction, public projection,
specialization evidence and runtime marker protocol are separate obligations.
July's projectability proof machinery is another dependency: it controls which
relations reach generalized schemes and which replay routes remain active.
The word *proof* in those implementation designs does not make them metatheory.

The most consequential correction is recorded directly in the August 1 URR-v3
document's opening post-implementation addendum. The motivating nested LVB
test constructed a concrete callback reference before body lowering, violating
LVB v5's deferred-reference rule. Correcting that witness, without changing
claim propagation, made its outer scheme equal to the parsed control
(`a65655b2`, as reported by the document). URR-V3-B was discarded; the neutral
URR-V3-A registration slice remained. This withdraws that witness as evidence
that causal qualification was needed to fix that bug. It does not retroactively
refute every URR/DCP/MPC theorem or independently tested contract.

Approval evidence is scoped throughout this audit:

- `spec/README.md` identifies promoted, confirmed specifications and explicitly
  puts specification/manual derivation above old executable behavior. This is
  repository standing, not an independently authenticated approval receipt.
- July/August documents record user approval, sometimes including chosen
  options, revision and quoted instruction. Their authorship and Git addition
  do not independently authenticate the receipt or enlarge its scope.
- August 16 explicitly records retrospective/analysis approval, excluding
  implementation authority. Its §11 records a later direct successor decision
  superseding the proposed pilot/decision process only; the historical analysis
  remains. Older passages still saying “unapproved” are first-draft history,
  not grounds to erase the later scoped header and addendum.
- No user message archive or external approval receipt was verified by this
  lane. Unknown receipt is not disapproval.

Active comparison authority is `rules/design-authority.md` and the current
documents in §7, subject to the October 11 top-level principles. Historical
contracts below are evidence about Oracle, not permission to reselect Yulang
semantics or implement an old storage design.

## 2. Corpus coverage and metadata

Path abbreviations below: `S/` = `spec/`, `D/` = `docs/`, `N/` =
`notes/design/`. Dates are JST. ADD and last-edit dates come from
`git log --no-renames`; an ADD after a declared date is publication evidence,
not evidence that the decision happened that day. Author/committer timestamps
match except the last invariant edit (01:14:01/01:15:26).

| Document | Declared date/revision; standing recorded in document | Exact-path ADD; last edit at anchor |
| --- | --- | --- |
| `S/2026-05-31-effect-variable-subtractable.md` | May31 initial; June22 full revision; core specification | June6 `934d2d376`; June23 `4dc5130c3` |
| `S/2026-06-13-computed-fetch-value-restriction.md` | June13; infer/generalize/SCC specification | June13 `174b120df`; June13 `24cf3b3ae` |
| `S/2026-06-13-runtime-guard-markers.md` | June13, June22 coloring revision; runtime hygiene specification | June13 `9b4a3323f`; June22 `305da4228` |
| `D/infer-solver-invariants.md` | June23 working contract; explicitly not complete proof | June23 `c436fc309`; July17 `42e3ad0d1` |
| `D/effect-inference-brief.md` | June23 outward-facing draft; public principality excluded | June23 `0f9c1080d`; unchanged |
| `D/hidden-effect-evidence.ja.md` | Implementation supplement; mixed old/new vocabulary | May14 `37f780f70`; June24 `ae8b657c0` |
| `N/2026-06-22-directed-stack-weight-implementation.md` | Consequences of colored draft; conflicting protect/floor readings superseded | June22 `b1cf52ff8`; June23 `4dc5130c3` |
| `N/2026-07-28-local-var-effect-boundary-fix.md` | v5; approval July30, explicitly retrospective confirmation | July28 `bcb8a8eaf`; July30 `eed7acd66` |
| `N/2026-07-28-subtype-fallthrough-closure.md` | July28 approved; implementation authorized; bounded project closeout | July28 `61a666dc3`; July28 `cc40ddd25` |
| `N/2026-07-29-unweighted-row-reduction-fix.md` | v6; approved July30; prior v3–v5 attempts rolled back | July29 `1022ec471`; July30 `cb7fa2265` |
| `N/2026-07-30-derived-row-claim-propagation-gap.md` | Approved July31, §5.1 D and §5.4 C selected | July30 `c49a4faab`; July31 `93479f84b` |
| `N/2026-07-31-claim-parent-delta-materialization.md` | July31 approved CDM | August1 `51d56605e`; unchanged |
| `N/2026-07-31-mixed-proof-conjunctive-ownership.md` | July31 approved MPC | August1 `51d56605e`; unchanged |
| `N/2026-08-01-derived-unary-premise-nodes.md` | August1 approved DPN | August1 `51d56605e`; unchanged |
| `N/2026-08-01-dpn-root-claim-and-cycle-safety-addendum.md` | August1 approved; retracts arena-rank premise | August1 `51d56605e`; unchanged |
| `N/2026-08-01-urr-v3-causal-qualification.md` | Approved, implementation held; B discarded, A retained | August1 `52a1cf712`; August1 `8bf3e62f6` |
| `N/2026-08-05-constraint-proof-kernel-separation-plan.md` | August5 approved CPK; narrow proof-layer rebuild | August5 `f2e491f06`; August5 `70ea51ac1` |
| `N/2026-08-16-infer-proof-architecture-retrospective.md` | August16 analysis approval; §11 successor process supersession | August16 `884fcefcf`; August18 `6a18bd24b` |

The May30 seed, its detail specification and the May31 original subtractability
note were read completely at the archive baseline. The seed/detail documents
contain no independently verified direct approval receipt. The detail calls the
seed the original intent and requires repairing the detail if they conflict.

Reading coverage: core specifications, brief, hidden-evidence supplement and
selected current governing documents were read substantively; long July
designs were read through revision histories, normative decisions/invariants,
relevant producer/consumer sections and closeout/stop conditions. Output
truncation occurred on long document captures; this is not a claim of complete
line-by-line reading. Later RCPF/CPK-8/GWCB/PCLF/QORF/CPK-SV documents were
inspected at their headers/revision summaries, with the August16 retrospective
providing the cross-document episode analysis. Their complete proof and
implementation appendices are unaudited here. The six TeX proof audits belong
to separate prover packets and were not duplicated.

## 3. May–June definitions and actual dependencies

### 3.1 The seed is not the later weighted calculus

The May30 seed extends a Function to
`a [b] -> [c] d ≡ thunk[b,a] -> thunk[c,d]`. Annotation binds a handled set to
the input effect variable; catch adds
`c <: [handled1 ∩ handled2; residual]`, and its result includes that same
residual. Concrete comparison uses row subtraction; residual row comparison
uses `(H1-H2) ∪ e <: f`. Its runtime proposal gives each effect at most one
block ID and avoids assigning a second ID to an already tagged effect.

The detail specification claims this avoids split residuals structurally,
defines EFF-ROW/EFF-BIND and polar glob desugaring, and leaves atom argument
constraints, normalization, recursive monomorphization and continuation/marker
behavior as TODOs. It first says bind is not represented by a side table, then
§2.4.1 adds a modifier table holding handled metadata, while keeping residual
state in ordinary bounds. Thus “no side table” cannot be quoted without its
qualified later representation. The seed's special bind operation is not an
ordinary intersection type merely because its examples use `&` notation.

The archived May31 note replaces bind with lifetime-scoped
`S-subtract(alpha,id)` and cancellation via `non-subtract(T,ids)`.
It specifies weighted comparison, variance reversal, freshening IDs during
instantiation and eliminating dead subtraction evidence. The upper-row rule
intersects allowed sets whose IDs are not cancelled by the left context.
It explicitly distinguishes complete/incomplete handlers and gives manual
shallow/deep and nested-handler derivations. These are original examples and
rules, not an independently checked universal theorem.

The external owner memory
`/home/momota1029/.claude/projects/-home-momota1029-rust-yulang/memory/project_infer_residual_regression.md`
was consulted only at pertinent May30–June6 entries. It reports user decisions
against closed rows, reverse residual flow and cooccurrence protection, later
changes of causal diagnosis, blocked-pair removal and a final level-zero
resolution need. It is an external owner report, not a Git specification or
approval receipt. Its successive investigations must not be flattened into
one established diagnosis. No unrelated memory was read.

### 3.2 Directed weights and row split

At the Oracle anchor the promoted May31 specification selects:

```text
T @L <: @R U
L(id) = pop^m take(F)^n; R(id) = pop^r
take;pop cancels; pop;take does not
J = K ∩ Common(L)
alpha @L <: @R [K; beta]
  => alpha <: [J; gamma], gamma @(L-J) <: NWeight(R,beta)  if J≠∅
  => alpha @L <: NWeight(R,beta)                         if J=∅
residual key = (source,J,L-J), excluding target tail
```

`Common` includes active left pushes only. Pure/right pop, filter and legacy
floor do not supply head subtraction authority. `take(Empty)` protects;
filter is a retained check on existing/future concrete lowers, erased from
stored weights after its consequences are installed. Family-path encounters
also generate invariant argument constraints. Functions reverse context for
arguments and preserve it for results. Replay preserves exact counts after
ordered composition/W-Mix. Same-boundary alias subsumption is a storage
rule, explicitly not a type equality `pop(n)=pop(1)`.

The implementation note cites the colored-soundness predecessor TeX by name,
supersedes conflicting protect/floor readings, and limits its runtime claim to
normalized, well-bracketed colored elaboration. It reports partial compact
cleanup, family checks outside machine context and runtime audit as remaining
work. These reported implementation states were not reverified as code facts.

The specification's termination section explicitly says unrestricted exact
natural-counter row-only termination is false. Its conditional stopping result
needs cycle-neutrality, exact cache, residual memoization and finite capability
algebra. Source-generated cycle-neutrality and sound alias subsumption remain
source/operational premises; a row-only theorem does not prove those premises.
The main self-tail rule restricts finite-observation omission to empty right
pop; the informal worked example omits that qualification. Reuse the precise
rule, not the abbreviated example.

### 3.3 Generalization and public projection

The June13 computed-fetch specification distinguishes obtaining a Function
value from evaluating its body. A computed fetch, even one returning a
Function, cannot quantify variables born during that computation: this includes
role inputs, effect/stack residuals and annotation/associated-type escape paths.
They move one owner level outward or remain non-generic. Multi-root runtime
SCCs containing computed-fetch edges are rejected; this specification does
not itself reject every single-root computed self cycle. It requires exported
fetch metadata and source-ordered computed top-level runtime roots.

This contributes independent premises to a generalization theorem: correct
fetch classification; coverage of every computation-born hidden coordinate;
quantifier/owner-level discipline; lawful SCC introduction; exported metadata.
It cannot be discharged by a let-rec calculus whose only recursive RHS is a
lambda, or by showing that stack IDs freshen in one helper.

The invariant document distinguishes hidden evidence from ordinary public
residuals. Its `ref.update` field uses private `kappa` and projection
`kappa <: e`, explicitly not equality. It openly calls same-boundary
subsumption formalization and private-tail boundary questions unresolved.
The June23 brief reserves stronger principality for hidden weighted schemes;
the public projection's generality order and full implementation termination
remain open. “Principal-style” must not be silently upgraded to principality.

The hidden-evidence supplement retains the older `HandlerMatchEdge` /
`ShiftKeep` / closed-positive-row-only conservative solver account alongside
later `take(Empty)` examples. Its claimed exclusions from `Scheme` and ordinary
type display are not the same representation as the weighted-scheme account.
The promoted specification's explicit priority and later directed-weight
supersession govern their overlap. This supplement is useful evidence of
layer separation and historical intent, not a unified frozen solver semantics.

### 3.4 Runtime hygiene requires an additional correspondence conjunction

The runtime-guard specification requires fresh runtime guard IDs, distinct
from static subtraction IDs and family/exact-operation paths. Guard membership
uses a dynamic list, with balanced dynamic-wind push/pop across effect search,
abort and resumption. `add_id[0,path,id]` records `entry_except` when activated.
It paints nonmatching requests only if their old guards do not intersect that
entry snapshot. Current visibility is insufficient: a request hidden only by
a later inner scope still needs the outer marker's color; a request already
hidden at entry must not be repainted by the new inner marker.

Function/thunk/structural values carry delayed shape-directed markers; escaping
request payloads and continuations must retain hygiene. Handler arms execute
outside the handler's marker frame; only the innermost active handler marker
is added at local value lookup. Family-prefix acceptance at `add_id` and exact
operation matching at the handler have different owners.

Therefore the transfer dependency is conjunctive:

```text
weighted source constraints + lawful generalized hidden scheme
  + specialization's exact boundary evidence / adapter placement
  + shape-directed delayed marker preservation
  + entry-snapshot coloring and resumable frame protocol
  => candidate source-to-runtime hygiene claim
```

This is a dependency statement, not a proof of the implication. A normalized
colored core excluding thunk/structure/family arguments cannot alone establish
the added runtime cases. The May seed's at-most-one-ID protocol also needs a
proved translation to the later guard-ID-list protocol; name similarity does
not provide it.

## 4. July correction lineage and why designs changed

| Document/section | Original premise or gap | Recorded reason and scope of correction |
| --- | --- | --- |
| LVB revision v1→v2 | Used raw `SubtractId` survives generalization as binder | Production trace says ordinary receiver effect correspondence survives while used push/pop IDs disappear; empty stack quantifiers are normal. |
| LVB v2→v3 | Positive push inside invariant ref effect becomes concrete row prefix | Push-only evidence cancels/prunes; invariant compaction does not materialize the claimed prefix. Target moves to actual callback negative return-effect boundary, preserving exact ref capability. |
| LVB v3→v4 | Helper may independently add family boundary then call real `run` | Real `run` already owns subtraction; the second source produces Empty/Set collision under one-ID-one-family invariant. Keep one real-run owner; runtime contract does not create type facts. |
| LVB v4→v5 | Concrete callback ref may be connected before body lowering | Controlled comparison reports timing as necessary/sufficient for that leak; defer concrete connection to ordinary second application. Earlier A/A3/A4 characterize primitive/helper transport, not all production lifecycle. |
| July28 subtype closure §§0–3,13 | Unmatched concrete head pair succeeds in both infer/specialize; emitter accepts generic coercion | Close ordered six-head matrix, preserve nominal-struct and registered-effect bridges, defer open alternatives. This is a source-reachable shape soundness fix, not revised effect subtraction or proof of global soundness. |
| URR v1→v2 revision | Full insertion-order invariance via dormant/lazy state | Broad activation inflated state/tombstones and changed hashes. Explicit recorded user decision narrows persistent mechanism to an initial matching lower; zero/no-match upper-first remains deferred. |
| URR v3 | Canonical record derivation identity is replay ownership | Same-key evidence merge contains different logical claims. Separate per-claim coverage from physical canonical record; retain independent direct tail claims. |
| URR v4 | No cross-source coverage inheritance | Exact binary replay derivation transports originating claim; endpoint equality alone remains insufficient. |
| URR v5 | Initial unmatched route can start root-self/uncovered | It is the reduction's own byproduct. Tag exact unmatched arm at admission, without tagging shared generic row helper or matched arm. |
| URR v6 | Suppressing generic replay suffices | Mirrored ordinary lower still reaches compaction, positive aliases and generalized witness. One scheme-projectable view and liveness/epoch invalidation must govern all three consumers. |
| DCP §§4–6 | Upper-only claim inheritance; structural and one-sided concrete child lose qualification | Use both exact replay parent sides and generic structural/lower admission hooks, retaining per-proof mixed record evidence. §5.1 explicitly defers conjunctive Boolean ownership to separate design. |
| MPC §2 | Flat OR of inherited claims treats AND inputs as independent derivations | Add clauses: standalone alternatives OR; one binary replay AND. Preserve claim payload and raw bounds, change projectability decision and its invalidation together. |
| DPN §§2,7 | Unary premise must be an existing linked lower record | Map miss is ordinary for upper-only constraint. Introduce Record/Constraint/RootCoverage premise sorts; remove accidental standalone fallback. |
| DPN cycle addendum §§0–2 | Arena parent ID always precedes child; root can be found via current record | Reports 88 rank violations and Reduced-root movement lookup misses. Add producer-root mirror index and active-path guard; no correctness/termination judgment may use ID order. |
| URR-v3 opening addendum | Direct-root causal qualification needed for nested LVB motivating bug | Overmatched independent MPC control; alternative route absent at producer. Invalid eager-ref witness repaired the motivating bug without propagation changes. B discarded, A remains neutral. |

Approval histories explicitly reopen substantive revisions pending new review,
even when earlier versions were approved. Later final headers record approval
for v5/v6; intervening “still unapproved” revision text is historical. LVB
v5's July30 approval is expressly after-the-fact confirmation. DCP records its
chosen D/C decisions explicitly; MPC says it adds proof-tree evaluation without
replacing the existing claim payload layer. These distinctions prevent reading
MPC as silently making the original DCP flat interpretation universally valid.

## 5. Two minimized conditional derivations

### 5.1 Mixed replay needs conjunction

Hypotheses: use MPC's selected projectability interpretation; a binary replay
is the only complete derivation of result `r`; its two exact premise records
are `l,u`; no standalone alternative, missing metadata or fallback applies.
Let `eval(l)=false` (covered-only) and `eval(u)=true` (independent).

```text
selected complete replay proof: eval(r)=eval(l)∧eval(u)=false
flattened independent claims:  eval(r)=eval(l)∨eval(u)=true
```

Two premise records and one binary result are minimal for distinguishing
binary conjunction from disjunction. Adding a genuinely independent complete
proof of `r` correctly restores its projectability by OR over alternatives.
This is an exact Boolean counterexample to flattening under documented MPC
hypotheses; it is not a fresh source-qualified counterexample, and does not
prove the source creates these premises. The historical motivating fixture's
later invalidation prevents using it to supply that missing source premise.

### 5.2 Canonical IDs do not supply a causal rank

Hypotheses: the DPN addendum's documented occupied canonical-child admission
permits a new structural derivation from a later parent to an existing child.
Allocate child `c=1`, then parent `p=2`; add edge `p→c` through occupied
admission. The graph has two nodes, one edge, and no cycle, but `p<c` is false.
No one-node allocation exhibits distinct parent/child allocation order, so
this is the smallest distinct-node schema.

This derives invalidity of arena allocation order as a universal proof rank
from the documented transition premise. It does not prove that transition
from source, or show that the historical 88 observed violations are this exact
fixture. The source artifact reports those violations independently of this
schema. A tri-color guard proves a finite walk terminates under its own
finite-graph assumptions; it does not by itself prove that every cycle cut
preserves the required global proof meaning or full solver termination.

## 6. Later designs, approvals and oracle limits

These are document-level findings, not new implementation measurements.

- CDM preserves exact carrier semantics and moves full-prefix materialization
  to delta processing. Its stated equivalence with a bulk oracle is conditional
  on the oracle's common claim/link rules and complete event census. That oracle
  independently checks representation maintenance, not source semantics.
- RCPF (August2 §§1,6–11) separates exact occurrence, immutable parent-set
  finite map and consumer summaries. The retrospective reports approximately
  50.4M parent memberships with 878K carriers; exact/semantic clause count
  similarity ruled out semantic dedup as the explanation. Physical copying,
  rather than redundant meaning, motivated factorization.
- The August2 quarantine addendum selects one authority per attempt and clean
  legacy retry after terminal discard. It does not authorize mixing per-record
  answers from old and new stores.
- August3 RCPF-D explicitly quotes blanket preauthorization at 10:28 JST for
  maintenance until 17:00, and says the user had not individually read the
  document. It deliberately labels this differently from individual approval.
  August5 CPK later records that RCPF-D §3 disagreed with a pinned independent-
  then-claimed occurrence contract and that five production consumers remained
  outside the earlier cutover inventory. Approved status did not prove that
  rule or census complete.
- CPK August5 §§1,5–10 moves proof authority to one store while preserving the
  core algorithm. It explicitly identifies replay routing and scheme projection
  as synchronous semantic services; provenance is not wholly passive metadata.
  Failed-attempt publication and invalidation are further coupled duties.
- CPK-8/8G separately authorize physical removal after authority cutover. The
  August7 plan records the user's explicit advance approval of 8G, removing a
  later reconfirmation requirement while retaining prerequisite gates. Its
  cycle-cut addendum changes cross-authority parity to canonical CPK order and
  final decision/payload, excluding incidental cut occurrence equality.
- GWCB rev.2 August10/11 requires the single decisive exact qualifying clause
  selected by canonical evaluator order to survive generalization, rather than
  only root/representative identity. The all-true-arm version exceeded resource
  gates. This is a certificate cardinality contract change, not deletion of
  alternate semantic proof arms.
- PCLF August11 rev.2 retracts clause-wide source-template uniformity: exact
  incidence can have different lawful source metadata. Zero conflicts in the
  original census were not a universal invariant. Rev.3 changes reader topology
  after three parity-correct readers lost performance. Its header records the
  full safety suite unfinished after 32 minutes; “landed/approved” does not
  close that suite gate.
- QORF August12 rev.2/3 separates occurrence arms, root winners and full exact
  associations. It refines failed-event transaction scope: outer replay event
  still appends after inner parent preparation fails. One-arm lookup cannot
  replace consumers needing the complete association relation.
- CPK-SV August12–14 distinguishes structural validation from Boolean
  projectability. Dynamic dependency addendum uses one current-state owner and
  late binding; SS2 resequencing disables cross-scope reuse during partial
  sealing. A writer census alone does not prove cache validity while owners
  remain unsealed. Prototype compile success is expressly local evidence.
- August16 retrospective §§1–2 separates comparable artifact measurements from
  owner-reported 80–1200× observations and says sampled reconstruction misses
  transient divergence and unrevisited broken records. It identifies copying,
  full-prefix updates, repeated completed-view evaluation, retained migration
  stores and unconstrained certificate cardinality as different causes. They
  cannot all be repaired by a semantic simplification or one cache.

Exact snapshot/bulk/parity oracles share specified identity, composition,
projection and event assumptions with production. Their independence is
representation/maintenance independence to the extent recorded; no general
external semantic oracle is supplied by naming them “independent.” Sampling
is explicitly weaker than checking all events. This lane ran no seeds, ranges,
mutations, timing samples or executable semantic checker.

## 7. Current Yulang transfer ledger

| Current governing source | Established selection relevant here | Reuse/repair/new obligation |
| --- | --- | --- |
| Oct10 annotation hygiene §§1–4 | Composed negative concrete annotation permits local subtraction; positive concrete annotation permits that effect; symbolic variables retain later checks | Reuse old polarity intuition conditionally. Construct exact occurrence/owner and actual concrete/filter transport; family equality alone supplies no authority. The recorded callback output was retracted and is not an oracle. |
| Oct6 directional protection §§1–3 | Protected variable's source Function upper exposes protected output effect; existing lower provider effect is not retroactively protected | Historical May31 unannotated-call clauses are correspondence inputs. Prove directional source construction and typed event/transport bridge, not an indiscriminate solved-row protection rule. |
| Oct10 residual lineage policy | Every separately created recipe keeps constructor identity; applicable present/future lowers fan out; qualifying parent/copy equality retains recipes | Oracle `(source,J,L-J)` key excluding tail is a historical policy, not current identity authority. Transfer needs a translation preserving separate recipes and reverse feedback; do not coalesce after equality without renewed selection. |
| Oct10 attachment/admission §§2–6 | Exact contextual operation tree, source attachment set identity per occurrence, two reviewed unbounded-cycle accelerations only | Weight algebra may be reusable after its formal proof audit. Prove constructor/context/lifecycle correspondence, including both/swap and correlated inputs. General mixed admission and concrete formal enabling remain open. |
| SourceGeneralize Oct8 §§2–4 | Publication-indexed scoped closure preserves fixed actual objects and simultaneous component relation; eligible own Desc declarations become templates; original residual remains active | Old fetch/value restriction is a necessary historical comparison, not the current source judgment. Need explicit translation of hidden row/boundary coordinates, shared initializers, monomorphic aliases, latent proofs, one-shot choices and established contracts. Selected local laws L1–L5 remain genuine premises. |
| Oct7 complete Call §§2–4 | Full callee, argument carrier, returned-provider dispatch, receiver and independent alternatives retained at their shared interface | Old four-slot Function or row substitution does not supply full Call ownership/accounting or complete C0. Reuse syntax/algebra only with independent semantic supplier and active consumer laws. Literal emission/WF_Dec formation is outside this history packet and remains separately owned. |
| Oct11 top-level principles §§1–5 | Correct natural Simple-sub; prove central invariants before implementation; no general full restoration/retry mandate | Historical RCPF/CPK attempt rollback is one old implementation contract. Preserve necessary semantic state/publication safety, not every old capacity/diagnostic/restoration requirement. |

The residual identity contrast is a documented policy difference, not evidence
that Oracle's mathematical key theorem is false. Likewise the current
Value-reference parent/copy SCC is not the historical effect-row cycle or
proof-graph cycle. A shared name “SCC” gives no translation theorem.

Recommended next action: have the primary add the explicit conjunction
source constraints → generalized evidence → specialization boundary evidence →
runtime protocol to the transfer ledger, assigning each missing bridge to its
own source/operational owner after consuming the separate TeX audits. Do not
restart hygiene from zero or promote a model theorem across those bridges.

## 8. Snapshot hashes, commands and commit packet

SHA-256 of pinned Oracle dependencies:

```text
fbd9588b489dbc6b987c5e7a11d1d3f1bdc696be3bed605e5dcac849f42cda7a spec/2026-05-31-effect-variable-subtractable.md
b3b53fd74256a212b06b8cfbdd8a2812d84f81ba5cc59d8fe37f0cdeec3bbac9 spec/2026-06-13-computed-fetch-value-restriction.md
80491d935c59b0098bd0c80d9d81ba5c53771b1786a3290bd48f055a93d155aa spec/2026-06-13-runtime-guard-markers.md
ad57daf9ec85c51a0363c13c34d15d5fb6db91afc8245478a08f274f676f8e0b docs/infer-solver-invariants.md
9a537ddafb1fc0ba60ad6d2077d5d7d6bde0c02ab1ecab39b8a1bad641b7dc4c docs/effect-inference-brief.md
9b83d2cc9cd7a35f89f85da7f9775aebc67ba3b56556f3038ae764a7a3163a51 docs/hidden-effect-evidence.ja.md
25ff7f5e8ae4133291c671744a3ebc95789d5ebea82684e9c6105cba54fef10f notes/design/2026-06-22-directed-stack-weight-implementation.md
f3385af851223873a7f77d300afbe7514d8abd8546b5fafbbbd4bacf3c808e59 notes/design/2026-07-28-local-var-effect-boundary-fix.md
7b5203e30f106c448c149ffd5ffd7066d56446dc14e2dd8e2ca709a8e721aca4 notes/design/2026-07-28-subtype-fallthrough-closure.md
2f8e6b44c74dc03c72d01fa6ae8a534e09ff3f53731e95a9789358682873573c notes/design/2026-07-29-unweighted-row-reduction-fix.md
a06dfed930f0dbb5f3eeaf59a9d97008867910b4a373b4aaa9e8c0ebcc1b7324 notes/design/2026-07-30-derived-row-claim-propagation-gap.md
7085de077af4ea43bbedf698dfaf04a8a21d01b3c60593d89a464221a61feef7 notes/design/2026-07-31-claim-parent-delta-materialization.md
2d46038533b1c7c1fbf129e574abb49a9ec45d72ed0b2a1d8c7ec464c63df62d notes/design/2026-07-31-mixed-proof-conjunctive-ownership.md
80baae430af4f590598371e8947f6941af728dc42213a834d54fd90e6719d85d notes/design/2026-08-01-derived-unary-premise-nodes.md
e9b66a4cb650ac53d1f2e4c4fa0bea7b140452872c66012b5ac4752b646b5dad notes/design/2026-08-01-dpn-root-claim-and-cycle-safety-addendum.md
121d598d91fe809582625e9541ed174aae81082922325283f9557c3f9e587952 notes/design/2026-08-01-urr-v3-causal-qualification.md
e93779aa3bd38982400e17c76e00a678944f24c3a2a6997ed9a61ede16072183 notes/design/2026-08-05-constraint-proof-kernel-separation-plan.md
eddd1965cabbe8c2cde09c483c2c1aaaec69c82c68a272d9021ade90a5a6df39 notes/design/2026-08-16-infer-proof-architecture-retrospective.md
```

Archive hashes, in seed/detail/original-May31 order:

```text
b885f4542c8e73449fe0316afcbdf546d577d6929d1a51741590bdcb7c706cb9
c9a48f0eb0311f09b3594117a5139df8503be72b3ad877d50334f6b127cf4343
d6cd61e0959470662afeba8ad21a6ea5fa03d69dd75453f891640616ebd417a1
```

Current governing dependencies in §7 order: live files were byte-equal to the
comparison baseline when checked.

```text
503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a
6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7
d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38
4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389
```

Commands: `git show <pin>:<path>`; bounded `sed`/`rg` section captures;
`git log --no-renames --format='%H %aI %cI' <anchor> -- <path>` with
`--diff-filter=A` for creation; read-only Python `subprocess`/SHA-256 snapshot
inventory; `git diff --check -- <leased-path>` and local text/lease inspection.
The file is new/untracked, so the Git diff check alone does not inspect its
contents; the separate Python text check found no trailing whitespace.
One mistaken lookup of `spec/INDEX.md` failed; corrected to `spec/README.md`.
No build, test, Oracle execution, exhaustive checker or timing measurement ran.
Resource budget: 25-minute first pass; lightweight read processes only, no
heavy processes; peak aggregate CPU/RAM and exact total process count unknown.
Coverage gaps: full 645-path reading; separate TeX proof validation; actual
approval receipts; complete later-design appendices; current production/source
correspondence; global hygiene/principality/termination; external memory not
immutable in Git. All remain unverified by this lane.

Commit packet:

- Exact leased/changed path: `notes/theory/oracle-inference-document-audit/effect-hygiene-history.md`.
- Baselines: Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`; archive
  `7915390c9cc8fb7f39eb04123abc0c7b581ea4a0`; comparison
  `67830dce14e6987b37e47b2540c204fcd06a92c6`.
- Dependency changes: none; frozen content hashes above. Other workers'
  catalogue/README edits are not dependencies for the substantive findings.
- Claim/review status: unreviewed documentary characterization and conditional
  finite witnesses; frozen before handoff; no independent self-review claimed.
- Checks already run: pinned reads, exact ADD/last-edit inventory, dependency
  hashes/live equality, leased-path whitespace/text inspection; no tests.
- Proposed message: `research: audit Oracle effect hygiene corrections and transfer premises`.
- Shared deltas left for primary/curator: catalogue metadata/standing fields;
  separate approval-record/receipt columns; invalid LVB motivation pointer;
  explicit runtime/generalization/source bridge conjunction; honest incomplete
  PCLF suite and sampled-oracle limits. No shared record was edited here.
