# Nested Function effect variance and exact port-operation order

Date: 2026-10-10
Status: independently reviewed research derivation and bounded source characterization;
no proof-gate closure or production conformance claim
Assigned baseline: `3fab829c0683e4b3b06dfe61f4b60a12884560a5`
Exclusive write lease: this note only
Worker: `/root/nested_effect_bridge_prover`, constructive leaf; no delegation

## 1. Objective, authority, and frozen claim boundary

Extend the [ordinary Function port proof](2026-10-10-function-argument-effect-contravariance-proof.md)
to finite nested paths without moving Swap across local prefixes or treating
Swap as an involution. Compose the result with the existing
[conditional contribution-local hygiene derivation](2026-10-10-contravariant-effect-conditional-proof.md)
only under that derivation's original hypotheses.

Authority is [contextual attachment admission](../design/2026-10-10-contextual-attachment-admission-design.md)
§3 (exact operations and identities), §3.1 (one attachment identity per atom
set at one exact annotation occurrence), and §4 Function ports/Positive wrapper;
[annotation policy](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–4; and its [integration checkpoint](2026-10-10-annotation-effect-hygiene-integration.md).
The selected meaning is composed-negative local subtraction permission and
composed-positive allowance. Variables are excluded from concrete atom
collection while retaining flow and later checks. The callback result was
retracted; no replacement result is assumed. Section 6 of contextual admission
does not enable general negative concrete annotation inference.

Fix one original lexical scope, enclosing resolved source signature r and
one exact effect row occurrence a reached at path p. Fix its annotation owner,
source positions, resolved operands, symbolic coordinates and binders. Where
boundary evidence exists, also fix the original receiver b, provider, exact
contribution c and its event/path lineage. Distinct source occurrences,
members, providers, receivers and residual constructor lineages are never
identified by this proof. All children use the one actual parent context at
their firing; no independently selected marginal witness is introduced.

The quantifier is every finite path in such a supplied signature, including
finite occurrence unfoldings if separately supplied. Recursive node sharing
does not merge occurrences. This quantifies over supplied source structure;
it does not prove that any chosen structure is accepted or that all its solver
tasks activate. The context statement quantifies over every fixed initial
exact expression P and the actual fixed local wrapper inputs of the specified
transition chain. It concerns operation construction before further checking,
replay, extrusion or normalization, unless those transitions are explicitly
included as hypotheses. Full source inference, complete Call, soundness,
required principality, arbitrary mixed recursion, runtime discharge and
complete output accounting remain excluded conclusions, not waived duties.

## 2. Literal Effect-only count: counterpath and restricted theorem

Let n_E count only `ArgumentEffect` edges and m_E count only `ResultEffect`
edges. This is the literal count in the assigned question. For general nested
source paths, the proposed equation

```text
sigma(a,p) = sigma(r) * (-1)^n_E
```

is false. A minimal counterpath is

```text
whole signature: (int -> [E] ()) -> ()
path to the inner [E]: Argument(Value) ; ResultEffect
sigma(r) = +, n_E = 0, m_E = 1, n_V = 1
actual composed sign = -; proposed sign = +.
port operation sequence = Swap ; Preserve.
```

Here E denotes one fixed resolved concrete effect identity. This is a
source-structure counterpath under the selected formation rule, not a compiler
acceptance/run claim: the negative concrete occurrence is rejected by the
current candidate. Even with a symbolic row in place of `[E]`, the same
variance and port-operation discrepancy remains. At least one Argument Value
edge is needed to make the omitted count matter; reaching an inner Function
effect then needs a second port edge. A direct one-edge Effect path has no
such omitted reversal. Thus this two-edge path is minimal within typed
Function-port paths ending at an Effect annotation.

There is still a restricted algebra theorem: for a word whose only reversing
edges are ordinary `ArgumentEffect` and whose other edges preserve, the sign
flips n_E times, and its formal inherited operation sequence has n_E Swap
steps in the original order; `ResultEffect` steps preserve. This holds for
every finite supplied operation word by the induction in §3. It is not an
arbitrary-length typed source path theorem: `ArgumentEffect`/`ResultEffect`
children have Effect sort, so ordinary Function decomposition cannot simply
continue at another Function in that child. Nested source paths normally
traverse Value children before their terminal Effect edge. The all-source
statement must count those reversals too.

## 3. Correct finite-path theorem and derivation

Let n_V count Argument Value descents and m_V Result Value descents, keeping
n_E and m_E exactly as defined in §2. Define N = n_V + n_E. For every supplied
finite Function-port path p from root variance s0:

```text
sigma(a,p) = s0 * (-1)^N.
```

This is a derivation under the selected source variance rule. Whole binding,
whole local and expression ascription roots use s0 = +; formal roots use
s0 = -. A root computation row has the root sign without any Function edge.
These source signs are separate from the positive/negative checking endpoints
of a paired annotation.

Freeze a path p = f1 ... fk. Its exact port action is

```text
T_f(K) = Swap(K)   if f is Argument Value or ordinary Argument Effect
T_f(K) = K         if f is Result Value or Result Effect.
K0 = P
Kj = T_fj(Kj-1)    (port-only expression).
```

Induct jointly on j. At j = 0 the sign is s0, the introduced operation word is
empty, and the context is the same P. For an argument step, source variance
negates the prior sign, N increases by one, and the constructor makes exactly
one new Swap node with the unchanged prior K as its designated input. Append
that Swap event to the chronological word. For a result step, sign, N and K
are unchanged and the operation event is Preserve. The two cases establish
the formula and exactly N new port Swap events for every finite prefix,
in precisely f1 ... fj order. Every inherited input is used once. Any Swap
already inside P is not counted as introduced by this path.

With no intervening operation the expression is `Swap^N(P)`, meaning N nested
syntactic constructors, never a parity quotient. Although scalar sign depends
on parity, `Swap(Swap(P))` is retained and is not inferred to equal P. The
proof assumes no injectivity, involution, cancellation or arithmetic meaning
of Swap. Positive sign does not mean that the original context was recovered.

For the local positive-wrapper extension, fix each actual child template
B_j to be either the identity template or `PrefixLeft(w_j,hole)`, where w_j
is that exact source child constructor's weight. Under the previous proof's
ordinary-port/positive-wrapper/order hypotheses:

```text
K0 = P
Kj = B_j(T_fj(Kj-1)).
chronological operations at j: port f_j, then its child-local prefix if any.
```

The same induction gives the composed sign and exactly N *introduced port*
Swap nodes. Each local prefix wraps the newly transported input; the next
port wraps that entire prior tree. For two argument steps with two wrappers,
the derived tree is

```text
PrefixLeft(w2, Swap(PrefixLeft(w1, Swap(P))))
```

and not `PrefixLeft(w2,PrefixLeft(w1,Swap(Swap(P))))`. Source order here is
the parent-to-child order along this path, not an assertion about global
worklist scheduling. Each w_j, original P subgraph, and its shared identity
is retained. No substitution touches a type/effect operand, receiver or
lexical binder. Extra checks, replay, filter erasure, negative wrappers or
inferred-entry Both require their own transitions; they cannot be silently
inserted into this unary formula. A justified intervening operation can be
recorded at its exact place, but the port-only nested-power formula then no
longer describes the complete tree.

## 4. Actual formation, decomposition and consumers

The following current-workspace locators were inspected at the supplied
baseline; complete file hashes are in §7. The primary reported HEAD equal to
the assigned baseline. This leaf made no Git query; equality of live file
bytes with baseline blobs remains an integration check for the primary.

| Owner / consumer | Exact locator | Established local fact and limit |
| --- | --- | --- |
| HIR annotation data | `crates/yu-hir/src/module/source_annotation.rs:68`, `:89` | Owner and annotation/row source positions are retained separately; rows retain resolved concrete identities and symbolic names. This is not a contribution attachment judgment. |
| Actual syntax formation | same file `:349`, `:399`, `:468`, `:505` | Annotation construction retains owner/position; arrow parsing builds argument/result subtrees; row parsing resolves a unique declaration to `SourceEffectId`. Parsing itself assigns no executable subtraction license. |
| Formal paired constructor | `crates/yu-solver/src/candidate_effect.rs:899`, `:919`, `:938` | `candidate_formal_pair` negates variance for both argument Value and Effect and preserves it for both results; entry starts at Negative. Annotation/scope/view map are passed together. Negative concrete rows fail. |
| Whole signature constructor | same file `:1059`, `:1212`, `:1266`, `:1272`, `:1286` | `candidate_annotation_pair` starts source variance Positive for both checking/exposed directions. `candidate_signature_value` flips argument source variance independently of endpoint polarity and preserves result variance. |
| Exact effect occurrence view | same file `:1304`, `:1364`, `:1396` | Negative concrete rows fail; symbolic connections remain scoped. Covariant rows reuse a view keyed by the exact row position and carry annotation scope/source polarity. Support and Allowance are paired interfaces, not proof of negative source permission. |
| Source preflight | `crates/yu-solver/src/candidate_source.rs:89`, `:92`, `:98` | Reverses the same argument-position sign; rejects negative concrete rows before general source admission. This guard agrees with the constructor refusal; it does not close the missing implementation. |
| Typed Function decomposition | `crates/yu-solver/src/lib.rs:12023`, `:12032`, `:12039`, `:12046`, `:12074` | Argument Value and Effect endpoints are reversed; result endpoints are preserved. Effect tasks have Effect sort. Each child goes through `candidate_function_port_admit`, then is enqueued with its retained relation. Enqueue is local evidence, not complete activation/replay. |
| Port operation/context construction | `crates/yu-solver/src/candidate_context.rs:1675`, `:1694`, `:1700`, `:1719` | Selects Swap/Preserve by all four fields, uses the exact processing parent's post-check context, applies its supported child prefix outside the inherited operation, and records parent/child/field/operation incidence. |
| Post-check input | same file `:1560` | A discharged parent supplies Identity; otherwise its original relation context. Therefore the original pre-check context cannot be assumed at the next port. |
| Child-local wrapper owner | same file `:1606` | `candidate_context_source` uses the exact Allowance's closed weight to construct `PrefixLeft(weight,Identity)`; the port constructor substitutes the inherited input into that template. Other child templates fail. |
| Live context consumer | same file `:1731`, `:1807` | Validates only Identity, closed zero-word PrefixLeft, and ordered Replay. An unhandled node including Swap fails; nonidentity Value context also fails. Registered allowance checks and discharge are not negative contribution subtraction. |

For current runtime trees define Q_j as the actual post-check parent input
and define

```text
T_runtime_argument(Q) = Q       if Q is structural Identity
                       Swap(Q) otherwise
T_runtime_result(Q)   = Q.
runtime child context = B_j(T_runtime_fj(Q_j)).
```

This recurrence follows directly from the inspected branch at
`candidate_context.rs:1702`. It is a bounded source characterization, not a
claim that these contexts all execute. In particular, the one-step identity
argument path retains a Swap *incidence* but has no structural Swap node.
Thus §3's exact unsimplified operation word/tree cannot be equated with the
runtime ContextExpr tree. Exact tree equality for a selected chain requires
the earlier transition premises, actual matching Q_j, and no Identity Swap
elision at its argument steps. Incidence and retained dependencies can record
the operation history even where the tree elides a step; this note does not
prove complete history reconstruction or semantic adequacy of elision.

The prior port proof's frozen Oracle evidence is inherited, primary-supplied
evidence: commit `6a18bd24bd0fa8b07e3eca5e099bfa8646320e3a`, Function owner
`crates/infer/src/constraints/machine/propagate.rs:226–270`, positive wrappers
at `:19`, `:31`; operation bodies in `constraints/mod.rs:3566`, `:3577`.
Its blob identities are `d558e7b9c17d33e91c5bb39c4cd85ebbfa4a8b09` and
`14860e3664a7ac05f7493f1d51fe69a6f34216e5`. This leaf did not re-extract Oracle
blobs. Its ordinary Argument Effect branch is the Swap branch; the separate
syntactic `Neg::Bot` Both branch is not included. The candidate's source-owned
inferred-entry evidence also supplies no license to replace written annotation
ports by Both. No frozen Oracle arithmetic is inferred from sign parity.

## 5. Strongest inherited conditional hygiene consequence

Take exactly the hypotheses and quantifiers of the existing conditional proof
§2: finite monomorphic decorated graph Ω, one shared assignment ν, any finite
execution prefix t, the same exact annotation a, owner f, signature path p,
original boundary instance b where introduced, concrete set C_a and symbolic
coordinates T_a. Supply its source formation, exact attachment A_a(c), typed
transport and owner hypotheses, and executable current/future-lower consumer
hypothesis together. Parameterized operand compatibility remains a separately
justified instance; the executable source slice provides nullary identities.

Then §3 determines the supplied formation sign as `s0*(-1)^(n_V+n_E)`.
If it is Negative, directly instantiate conditional proof §4 for every such
finite prefix and every finite chain of the supplied typed correspondences.
Transport preserves the original annotation/receiver, predicates K,
dependency incidences D and lineage L under the same ν, with no grant at an
unrelated path or receiver. Its owner-expiry/frame conditions remain intact.
For the exact finite contribution witnesses O and any permitted selected R:

```text
R subseteq {c in O | A_a(c) and pi_nu(c) admitted by C_a}
Residual_a(O,R) = O \ R
Support_nu(Residual_a(O,R)) = {pi_nu(c) | c in O and c not in R}.
```

Proof: the corrected sign discharges only the sign test in that conditional
theorem; all its other premises remain supplied. Apply its transport result
with the same indexed input witnesses and its subtraction result with the
same exact R. Expand difference membership for the support equality. A sibling
c′ with the same projected E remains whenever c′ is not selected in R; neither
same support nor equal canonical endpoints derives its attachment. Every
symbolic/current/future lower still checks the original correlated view. If
the sign is Positive, the concrete clause is an allowance, and this theorem
supplies no R formation. An even/odd Swap count alone supplies neither case's
attachment or consumer evidence.

This is the strongest consequence available by composing the existing stated
hypotheses here: conditional transport and licensed contribution-local
filtering, not proof that actual source output is O or that R is actually
consumed. A whole-output corollary still requires the existing §5 independent
discharge/complete-image premise `actual output = (O \ R) union New`, with all
new surviving contributions accounted for. E is absent only when neither
residual nor New contains an E witness. Handler-role/profile derivation,
actual receipt/event observation, active owner/receiver, ordered arm selection
and operation compatibility remain additional original premises. No local
subtraction clause alone creates a Handler role, proves runtime selection,
or establishes complete Call or principal inference.

## 6. Missing source bridge and proof-obligation economy

The remaining premise is not another polarity induction. At the authentic
composed-negative annotation formation, the compiler must construct the local
executable subtraction view and derive A_a(c) from the actual contribution and
typed route, retaining annotation set/member, owner/path, receiver, compatibility
and lineage. The live consumer must apply that authority to current/future
lowers, preserve original symbolic/predicate correlations, and feed exact
residual recipes in their retained constructor lineages. Replay activation,
extrusion, fresh use, qualifying recorded parent/copy SCC intrusion and rollback
must preserve those same obligations. This note proves none of that from stored
records, port parity, annotation support, canonical equality or enqueue alone.

Two tempting routes fail for different reasons: (1) identifying two Swap steps
with Identity erases exact operation order and does not construct attachment;
(2) instantiating hygiene transport with an assumed attachment preserves it but
does not prove its source construction. Both leave the same negative formation
and consumer premise untouched. No third equivalent reconstruction is proposed.

Apply `compiler-engineering.md`, Natural compiler behavior and proof-obligation
economy: this is A safety/correctness, also B where ordinary approved negative
inference is required; D arises if formation discards its known occurrence,
owner and incidence and a later consumer reconstructs them from IDs/support.
Formation and the actual contribution/typed-boundary owner are the places that
know those facts. Existing SourceAnnotation/SourceEffectRow, AttachmentSet,
relation/dependency and selected residual records supply concrete ownership
locators, but do not by themselves establish the missing attachment judgment.
The next proof should follow that coupled constructor/consumer when it exists.
Retaining genuine construction evidence is a possible implementation duty for
the primary to adjudicate, not a new carrier or semantic proposal in this note.
No source restriction, mandatory annotation, marginal witness selection,
weaker inference, support-wide erasure or new reconstruction relation is added.

## 7. Dependency snapshot, checks, resources and runtime

The dependency hashes below are the live bytes inspected by this leaf and
rechecked after writing. The primary's message supplied baseline/HEAD equality
and the prior port-proof hash; that hash agrees. No baseline blob extraction or
Git operation occurred. The primary must compare these exact source hashes with
its pinned revision before integration or review.

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/progress/2026-10-10-annotation-effect-hygiene-integration.md` | `16ca6bed3fa6ead4c82f8d7d92bdf9ba9f3e35c623c0098d5ecc66a3896ae878` |
| `notes/progress/2026-10-10-contravariant-effect-conditional-proof.md` | `3ef7fd4b45dc55b7e2d7ffb32f28ae2a9912176570d96756658a1f6896033c02` |
| `notes/progress/2026-10-10-function-argument-effect-contravariance-proof.md` | `7377dc89973b5b380c1466161f0c20e94d0cf39fb860aa1477e9a3b3aec1730c` |
| `notes/progress/2026-10-10-function-port-context-operations.md` | `f6fdde8ed8671812c93a94bc5700797b6d845c1f2cabc0b1a62cf2fc5edb188b` |
| `crates/yu-hir/src/module/source_annotation.rs` | `a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb` |
| `crates/yu-solver/src/candidate_source.rs` | `8adc289142dd78a625184dd661fb162e49f24532a19c7c4f9e114e604c0966a0` |
| `crates/yu-solver/src/candidate_effect.rs` | `2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e` |
| `crates/yu-solver/src/candidate_context.rs` | `2897c168c02640443a2f1280286a648853afe08324294c53f1c95d373ac3a337` |
| `crates/yu-solver/src/lib.rs` | `9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1` |
| `.codex/config.toml` | `dae388e4e811c346727ec6688472c7fcf6341ddc5466168cfaa03fdcc0b8e17a` |
| `.codex/agents/prover.toml` | `485a26c7409e16c692ad10095031ab0e7084726ec5da5666082b3bbc4a5daf98` |
| `rules/orchestration-budget.md` | `a0a114b589e8920af8e8fd871d15f63d68b735fc1a553f5a89952b1eab8489e5` |
| `rules/agent-orchestration.md` | `cce7862a101aa348eecf55cd66e76d5215eaba934f8e3048105ad0f25d3dd65e` |
| `rules/research-lab.md` | `3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69` |
| `rules/design-authority.md` | `4477be1344edb73e2873f94233d760c9a600bee6adbaaff3ec812a49c5219e7b` |
| `rules/compiler-engineering.md` | `1ff144d376052d2e01d2e97ba3290e6942f126765067fbf11dfeffc06f89b442` |
| `rules/git-concurrency.md` | `2561a7168ba8b2d655cc928c8adac565755ec7e3b6b4175e8ac87be4bcdaa5e6` |

Checks by this leaf: read/search the listed owning constructors and direct
consumers; derive the minimal two-edge counterpath directly from their cases;
hash the dependency files; run a focused Python document-integrity check on
this exact leased note (local relative references, balanced fences, final
newline, no trailing whitespace, required corrected/restricted formulas and
unchanged listed hashes). The document check is not an executable proof test.
No source fixture, compiler test/build, algebra enumeration, benchmark or
runtime discharge check ran. Coverage is the two structural induction cases,
the exact local port branches and the conditional theorem instantiation;
arbitrary source acceptance and complete operational traces are unverified.

The primary reports that the actual spawn returned worker identity
`/root/nested_effect_bridge_prover` with role `prover`, requested explicitly at
`gpt-6.1-sol` / `high`. The child-visible identity agrees. Observed effective
model/effort: **unknown**; no runtime metadata is available in this session.
The inspected role omits model/effort pins; config registers the role and
requests Sol/high defaults. Those facts are not evidence of effective runtime
settings or a hot reload. No Astra, child dispatch or external contact occurred.

Resources: one bounded leaf; lightweight document/read processes only, initial
independent reads peaked at two simultaneous shell processes, then serialized
inspection and one document-check process. No heavyweight process, performance
samples or persistent child process. CPU/RAM and total wall time were not
instrumented; no numerical resource result is claimed. All assigned writes
are frozen on delivery; independent review and global budgets remain primary-owned.

## 8. Commit packet and one next action

Exact path: `notes/progress/2026-10-10-nested-function-effect-variance-bridge-proof.md`.
Baseline: `3fab829c0683e4b3b06dfe61f4b60a12884560a5`.
Changed dependency hashes: none observed between this leaf's first complete
snapshot and delivery; the primary revalidated current source hashes against
the frozen table.
Claim/review status: independently reviewed constructive research derivation, literal
Effect-only counterpath, restricted operation-word theorem, corrected
all-argument-edge theorem and bounded source characterization; no self-
certification, gate promotion, production conformance or semantic authority.
Checks already run: the source inspections, dependency hashing and focused
document-integrity check described in §7. No Git, compiler execution or tests.
Proposed one-line checkpoint message:
`research: derive nested Function variance and exact port-operation order`.

Shared-record deltas left to the primary/curator: record that literal
ArgumentEffect-only counting fails at nested Argument Value positions; preserve
the corrected all-argument-edge sign/operation statement separately from runtime
Swap incidence/tree elision. Record only the conditional hygiene instantiation;
leave attachment construction, current/future consumer, lifecycle, complete
Call, soundness/principality and negative-concrete admission open. No shared
task, index, theory or design record was edited.

One next action: assign the exact source-owned attachment construction and live
inverse-context consumer bridge, retaining the current/future receiver checks
and lifecycle obligations; keep negative-concrete admission gated.

Independent review: a fresh `compiler_referee` review found no blocking or
major issue in the corrected sign recurrence, exact operation-word order,
conditional hygiene composition, or bounded source characterization. It found
one minor comment paraphrase in the companion source audit, corrected there.
No source-reachability, executable subtraction, lifecycle, soundness,
principality or admission gate was certified.
