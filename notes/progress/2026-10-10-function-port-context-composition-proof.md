# Exact context composition along an ordinary Function-port path

Date: 2026-10-10
Status: unreviewed conditional algebraic derivation with a bounded frozen-source
audit; no source-reachability theorem, production conformance, or gate closure
Baseline: `8282e7a756eeb4a1262847d5fb050e355440765f`
Worker: `/root/function_port_path_proof`, assigned prover leaf; no delegation
Exclusive output lease: this note only

## Objective and governing dependencies

Extend the prior one-port derivation to a fixed finite path by induction on its
length. Authority is
[contextual attachment admission](../design/2026-10-10-contextual-attachment-admission-design.md)
§3 (exact operation order and shared child identity), §3.1 (one attachment set
per exact annotation occurrence, with separate member ordinals), and §4
(Function ports and positive wrappers). Section 6 retains the approved internal
gate boundary. The
[prior conditional derivation](2026-10-10-function-argument-effect-contravariance-proof.md)
supplies the one-edge algebra and historical Oracle evidence; its Oracle blobs
were not inspected anew here. All workspace source observations below were
independently read from the assigned commit, never from uncommitted files.

This assignment makes no semantic decision. Authority/behavior/scope/surface
classification: existing authority, no behavior change, local research note,
internal surface. Review assignment and status adjudication belong to the
primary. Reading executable role configuration establishes requested defaults,
not observed model execution.

## Frozen statement, binders, hypotheses, and exclusions

Fix an original source scope and binder environment, a natural number `n`, one
parent context root `P`, and one indexed path of comparison occurrences
`v_0,...,v_n`. Edges are indexed **from parent to child**, `i=1,...,n`:
edge `i` descends from `v_(i-1)` through its selected Function port `f_i`, then
consumes the specified positive wrapper at that child's positive endpoint;
`v_i` denotes the comparison after that wrapper is consumed. For `i<n`, this
same `v_i` must be the owning comparison of the next Function firing.
The empty path has only `v_0` and performs no port or wrapper transition.

The fixed data also include, for each edge, the actual wrapper occurrence,
its complete local weight `w_i`, attachment set/member identities, resolved
operands, constructor lineage, endpoints and component sorts, providers,
dependencies, and lexical references. These are parameters, not existential
witnesses chosen separately after observing each port. Distinct occurrences
are not identified by equal nominal effect families or equal numerical counts.
The lemma performs no source substitution, binder renaming, freshening, scope
movement, or identification of provider, witness, or residual lineage.

For every such fixed tuple satisfying the following hypotheses:

1. Every edge is an ordinary Function port. Argument Value and ordinary
   Argument Effect reverse their endpoints and apply `Swap`; Result Value and
   Result Effect preserve their endpoints' orientation and context. The
   special syntactic `Neg::Bot` Argument Effect passthrough is excluded.
2. The selected positive endpoint **after** the port's reversal/preservation
   has the exact specified child-local positive wrapper, with weight `w_i`.
   Its operation is immediately next on this path and is
   `PrefixLeft(w_i, input)`. It is neither a parent wrapper nor an upper
   negative wrapper. Its closed local template has precisely one context hole:
   `PrefixLeft(w_i, Identity)`.
3. At firing `v_(i-1)`, one actual parent input `K_(i-1)` is shared by the
   firing's ports. Each port transforms that input; this path selects one
   child of that firing. No independent marginal parent-context witnesses,
   weight substitutions, or changed attachment instances are allowed.
4. From the supplied root to the reported endpoint, these are the only context
   transitions. There is no intervening discharge/reset, filter projection,
   opposite replay/directed mix, negative-wrapper transition, residual
   creation, nonempty residual/POP transition, or transport. All named
   comparisons and wrappers are known; an unknown child does not satisfy this
   hypothesis. Success of the required primitive transitions is assumed.

The required conclusion is the **exact ordered context expression** at every
path prefix, in particular at `v_n`. No claim of existence of such a source
path is included. Port lists alone do not establish sort-compatible nested
Function constructors. An opaque supplied `P` may retain earlier structure;
the lemma neither evaluates it nor establishes applicability to operational
paths carrying nonempty residual/POP obligations.

Define exact unary constructors, without quotienting their syntax:

```text
S(K)       = Swap(K)
L_w(K)     = PrefixLeft(w, K)
T_f(K)     = S(K)  if f is Argument Value or ordinary Argument Effect
T_f(K)     = K     if f is Result Value or Result Effect
U_i(K)     = L_w_i(T_f_i(K)).

K_0        = P
Q_i        = T_f_i(K_(i-1))          (immediately after edge i)
K_i        = L_w_i(Q_i)             (after its child wrapper), 1 <= i <= n.
```

For all `j` with `0 <= j <= n`, the claim is

```text
j = 0:  K_0 = P
j > 0:  K_j = U_j(U_(j-1)(...U_1(P)...))
             = L_w_j(T_f_j(L_w_(j-1)(T_f_(j-1)(
                 ...L_w_1(T_f_1(P))...)))).
```

The innermost pair of operations belongs to edge 1; edge `j` is outermost.
The equalities preserve references to `P` and every complete `w_i` record.
They describe exact trees with retained shared inputs, allowing structural
interning of identical nodes but no semantic cancellation.

## Induction and consequences of its exact scope

Base case `j=0`: the empty transition sequence returns its supplied context
`P`. No wrapper is prefixed and no Swap is inserted. This is the empty unary
composition, not an assertion that `P` equals Identity.

Inductive step: fix `j<n` and suppose the formula holds for the actual `K_j`.
Hypotheses 1 and 3 give the next port's context `Q_(j+1)=T_f_(j+1)(K_j)`
using that same parent root. Hypotheses 2 and 4 give the next context
`K_(j+1)=L_w_(j+1)(Q_(j+1))`. Substitute the induction equality into this
single context input, leaving weight, endpoint and source identity parameters
fixed. The result is
`U_(j+1)(U_j(...U_1(P)...))`, exactly the formula at `j+1`.
The substitution concerns an expression hole; it cannot capture any source
binder. Induction therefore derives the claim at every prefix and at `n`.
No inverse reconstruction or additional relation is needed.

For example, two argument edges give
`PrefixLeft(w_2, Swap(PrefixLeft(w_1, Swap(P))))`.
Replacing this by `PrefixLeft(w_2, PrefixLeft(w_1, P))` would require moving
Swap across the first prefix and cancelling Swap operations. Neither follows
from the induction. Even a separately established involution law would not
justify moving Swap across a prefix. Likewise, the one-edge argument formula
`PrefixLeft(w_1, Swap(P))` cannot be changed to
`Swap(PrefixLeft(w_1, P))`; the trees have different outer constructors.

A filter inside `P` remains inside that same retained input. A filter carried
by a local weight stays attached to that exact weight occurrence. Nothing here
establishes commutation, cancellation, filter removal, or projection across
either one. A path requiring an inserted filter check/discharge is outside
hypothesis 4; its consequences need their actual receiver and consumer proof.

Falsifier for the conditional claim: a trace satisfying all four hypotheses
whose first differing prefix does not contain exactly the prescribed port
operation followed by its own prefix on the same input root and weight identity.
For a one-argument trace, a Swap-rooted output instead of the PrefixLeft-rooted
output is the smallest order falsifier. A two-argument trace tests the proposed
cancellation above. A mismatched sibling parent input falsifies hypothesis 3,
so it defeats a source bridge rather than the induction. No executable probe
or source trace was run; these are specified falsifiers, not observed results.

## Actual frozen constructors, consumers, and missing bridge premises

Every locator here refers to baseline `8282e7a756eeb4a1262847d5fb050e355440765f`.

| Owner or consumer | Frozen workspace locator | What inspection establishes locally |
| --- | --- | --- |
| Exact context carrier | `crates/yu-solver/src/candidate_context.rs:80` | `PrefixLeft` retains a `LocalWeightId` and input `ContextId`; Swap retains its input; Replay retains ordered lower/upper inputs. |
| Structural interning | `candidate_context.rs:1256` | `context` keys complete constructor records, including weight/input IDs. This is structural equality, not a semantic equivalence theorem. |
| Function decomposition | `crates/yu-solver/src/lib.rs:12023` | Argument Value/Effect endpoints reverse; Result Value/Effect endpoints preserve orientation. |
| Port relation admission | `lib.rs:12074`; `candidate_context.rs:1675` | The loop calls `candidate_function_port_admit` and enqueues the returned relation with each child; the helper retains parent, child, field and Swap/Preserve incidence. |
| Parent context selection | `candidate_context.rs:1560`; `:1698` | Port admission uses the retained parent's **post-check** context; a discharged relation yields Identity. |
| Child-local prefix construction | `candidate_context.rs:1601`; `:1706` | Local context comes from a closed upper Effect Allowance. When it is `PrefixLeft(weight, Identity)`, admission prefixes that same weight onto the transported parent input. |
| Source weight preparation | `crates/yu-solver/src/candidate_effect.rs:598`; `candidate_context.rs:1360` | The view constructor retains owner/position and source weight. The weight retains allowed operands, member ordinals and optional attachment scope/polarity; live left word and right POP arrays are empty. |
| Task consumer | `lib.rs:11843`; `:11859`; `:11861` | A worklist item becomes the retained processing relation and is passed to `candidate_context_execute` before endpoint handling. |
| Current execution envelope | `candidate_context.rs:1756`; `:1785`; `:1807` | Zero-word validation accepts closed Identity-input prefixes and ordered Replay fragments; other constructors fail that validation. Nonidentity Value contexts fail in `candidate_context_execute`. |

The port helper gives a bounded conditional construction observation: if an
invocation has an appropriate retained parent and the stated local unary
prefix, it constructs the ordered prefix over the inherited operation, using
the same stored weight ID. For an argument with nonidentity inherited input it
constructs a structural Swap node. This observation is narrower than a source
path realization or execution theorem.

There are explicit gaps between the abstract transition hypotheses and this
workspace source:

1. **Literal Swap on Identity:** `candidate_context.rs:1702` guards Swap-node
   construction with `inherited != IDENTITY`. For a parent Identity and local
   prefix, stored syntax is `PrefixLeft(w, Identity)`, whereas the abstract
   argument formula is `PrefixLeft(w, Swap(Identity))`. FunctionPort incidence
   still records Swap, but incidence is not that missing structural node.
   No quotient law or normalization proof is assumed. This directly prevents
   an unrestricted exact stored-DAG correspondence claim for the assigned
   theorem; the theorem itself retains its original quantifiers.
2. **Actual positive wrapper and scheduling:** the local source reader selects
   an upper Allowance's closed weight, rather than tracing a positive wrapper
   activated on the post-port positive endpoint. Reading that weight and
   reconstructing a prefix does not establish the exact source occurrence or
   immediate wrapper-consumption step required by hypothesis 2.
3. **Parent continuation:** `post_check_context` can replace the retained
   relation context with Identity. Establishing `K_i` as the next firing's
   actual input requires showing no intervening discharge/reset or proving
   the different, check-aware trace. No such discharge proof is supplied.
4. **Reachability and activation:** the worklist consumer exists, but no parsed
   source path, complete admission/activation trace, or fair/complete replay
   argument has been constructed. Unknown inner children, unresolved source
   identity maps and sort-incompatible proposed paths cannot be filled in
   from stored relations alone.
5. **Shared identities across a whole path:** the local helper retains one
   parent relation for a port invocation and exact weight handles. This does
   not establish one source-origin map through every firing, attachment
   instance, receiver, provider, or later freshening/extrusion/intrusion.
   Those witnesses must be traced jointly, never selected marginally.
6. **Execution:** nested prefixes and Swap expressions are outside the
   inspected live zero-word validation fragment. Stored output syntax alone
   proves neither successful activation nor complete contextual execution.
   Detached source PUSH preparation does not supply an executable live PUSH.

These are unresolved premises or concrete representation limits, not adopted
restrictions on ordinary inference. The one-edge prior result and this finite
induction are algebraic derivations, not two attempts establishing missing
source reachability. No third equivalent algebraic reformulation is proposed.
Before repeated source reconstruction, the primary should apply the required
proof-obligation-economy audit at the source constructor, port admission and
worklist consumer: distinguish required correctness/natural-inference evidence
from stronger characterization and evidence discarded by construction. This
note neither reclassifies nor retires an existing gate.

Complete Call meaning, receiver checks, runtime/handler hygiene, semantic
soundness, required principality, generalization, qualifying parent/copy
intrusion, complete propagation/replay, mixed recursion, rollback and production
cutover remain unverified. The named exclusions do not reject source programs
or alter their approved semantics.

## Snapshot, checks, runtime, and frozen handoff

Direct dependency identities were independently computed from frozen blobs:

| Dependency | Git blob | SHA-256 |
| --- | --- | --- |
| Governing design | `c99873544ca90aa817c77941514f7868a8023d65` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| Prior one-port proof | `d7857f0a8639e9f46ea81374f41c427eeeeb00c1` | `7377dc89973b5b380c1466161f0c20e94d0cf39fb860aa1477e9a3b3aec1730c` |
| `candidate_context.rs` | `33f9206171f721246f3a4f206d3690e924bbbb10` | `2897c168c02640443a2f1280286a648853afe08324294c53f1c95d373ac3a337` |
| `candidate_effect.rs` | `d1fd99d140c3f3b9d9d4464c85639f0d0e5a2502` | `2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e` |
| Solver `lib.rs` | `1b036291c8c52a5723f070d80ac655f6355e5629` | `9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1` |

Commands: read-only `git show BASE:path`, `git grep` and `git ls-tree` located
and inspected frozen sources; inline `python3` with sequential `git show` /
`git rev-parse` computed dependency SHA-256/blob identities. A final note-only
`python3` integrity check passed for final newline, fence balance, whitespace,
required statement/obstruction markers, and baseline-resolved relative links.
These are document/provenance checks, not proof tests or source execution.
No compiler tests, builds, benchmarks, executable models, Git mutations,
external contact, or other writes occurred.

Verification owner for these narrow checks: this leaf; the primary retains
global verification/integration ownership. Read-only subprocess concurrency
peaked at seven lightweight blob/skill reads; subsequent inspection and hashing
were serial. No heavy process ran. CPU/RAM peaks and total wall time were not
measured; no numeric resource allowance was supplied in the packet.

Requested identity/settings: registered `prover`, normal configured
`gpt-6.1-sol` / `high`. The live callable schema exposes `prover`; frozen
`.codex/config.toml` registers it and requests those defaults, while
`.codex/agents/prover.toml` omits model/effort pins. Effective launch role,
model and effort are not exposed to this child and remain **unknown**;
the primary owns evidence of its actual launch. No Astra override, hot-reload
claim, child launch, or coordinator work occurred.

Writes stop with this frozen note. Independent review is pending; this producer
does not certify the artifact. Next action: the primary assigns fresh
compiler-referee review of the conditional induction and the explicit limits
of the frozen source bridge before any status adjudication.

Commit packet: exact leased path
`notes/progress/2026-10-10-function-port-context-composition-proof.md`;
baseline `8282e7a756eeb4a1262847d5fb050e355440765f`; direct dependency hashes
are above. No dependency was changed, and equality with later HEAD/live files
was not checked. Claim/review status: unreviewed conditional derivation plus
bounded source audit, no gate closure. Checks already run: frozen provenance
reads/hashes and the note-only integrity check. Proposed checkpoint message:
`research: derive ordered context composition along ordinary Function paths`.
Shared-record deltas left to the primary/curator: record the conditional path
lemma after adjudication; retain exact Swap-on-Identity correspondence, positive
wrapper occurrence/scheduling, shared source identities, reachability,
activation and contextual execution as unresolved. No shared task, design,
index, theory-status, question-board, code or test record was edited.
