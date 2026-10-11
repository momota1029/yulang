# Exact nested source: parameter value and extrusion-copy reference bridge

Status: frozen research obstruction; independent review pending
Claim class: bounded source-to-operation audit, not an established theorem or counterexample
Parent claim: OPEN; no semantic parent/copy SCC witness
Primary-pinned baseline: `35e88c8113c9c6516e260170503bea753e4ede6`
Branch supplied by primary: `research/simple-sub-intrusion`
Exclusive lease: this file

## Frozen statement, scopes, hypotheses and exclusions

The exact source assigned through the frozen theory input is:

```yulang
my f x = { my inner z = g z; g };
my g y = f
```

The original required witness is one successful source/artifact/inference
history of this program, containing the actual retained, distinct Value pair
`(C,Z)` created by extrusion of the argument port of the nested `g z`, and
source-value reference paths `Z ->* C` and `C ->* Z` before the equality whose
qualification those paths would establish. All path vertices, ownership and
reference targets must belong jointly to that same artifact/history. This
packet does not replace this existential witness with a claim about all rows,
all programs, or all possible graph interpretations. The broader parent gate
retains its original scope.

`f,g` are distinct module definitions; `x` binds only in `f`'s Lambda, `y`
only in `g`'s Lambda, and `z` only in the local initializer Lambda for `inner`.
The nested callee `g` and the separate Block-result `g` are distinct Name
occurrences. `Z` is the actual parameter row for that `z`, not its separately
allocated expression facade. `C` is the actual positive argument copy whose
retained parent is `Z`, not a result copy or an independently chosen witness.
No module spelling, binder ID, or root row is substituted for either endpoint.

The inherited unproved hypotheses remain explicit: **H_source**, that this
exact source lowers/collects with these forms and resolutions; **H_prefix**,
that its ordinary source driver reaches the previously identified argument-copy
creation prefix, with checked allocation succeeding and without prior
identification of these rows. Granting these hypotheses only exposes the
semantic bridge tested below; it does not establish source execution. No new
copy-value assumption is added to make the desired conclusion conditional on
itself.

The method is different from the earlier guarded level/polarity trace: start
with the approved meaning of a reference in a Value variable's value, identify
what the source owns for the formal `z`, and inspect what the copy constructor
transports. Stop at the first missing source/value correspondence. No new source
variant, later continuation, rank argument, executable model, test, build or
Oracle run is used.

The comparison relation, physical lower/upper storage, extrusion-family parent
metadata and definition `SccPlan` are excluded as semantic edges. Complete Call,
effect hygiene, soundness, required principality and ordinary Simple-sub
inference retain their contracts. The original-source root theorem for
`my f x = g; my g y = f` is not transferred to this nested artifact. The
complementary progress input uses a different `f y; inner g` source and a result
copy; it supplies obstruction history only, not this pair's identities or paths.

## Governing sources

Authority is `notes/design/2026-10-10-parent-copy-scc-intrusion.md`, **Direct
decision**, **Selected operation and compiler responsibility**, **Value-reference
SCC clarification**, and **Retained boundary**. The clarification fixes vertices
as Value variables and edges as references in their values. It allows references
across the extrusion-family tree; this audit imposes no contrary restriction.
The graph criterion alone does not establish which value and reference targets
the source and copy operation assign to a particular internal row.

The top-level principles, §§1–5 and **Evaluation**, require mathematical native
inference and proof-supported implementation without inference search or
artificial source restrictions. `rules/compiler-engineering.md`, **Natural
compiler behavior and proof-obligation economy**, governs the stopping audit.
`rules/agent-orchestration.md`, **Proof delegation and decomposition** and
**Model routing and Astra escalation**, and `rules/git-concurrency.md`,
**Disjoint-file mode**, keep this a bounded, leaf-only producer assignment.

## Direct source-to-row correspondence that is available

Under H_source, HIR's local binding constructor records `inner` with its own
`HirLocalId`, initializer and retained parameters
(`crates/yu-hir/src/module/local_source.rs:738`, `:757`, `:796`). Initializer
work installs its parameter in the lexical table and constructs
`Lambda(parameter=z, body=Apply(Name(g),Name(z)))` (`:330`–`:366`). Name
lookup consults that lexical table before the module namespace (`:636`–`:658`).
Consequently the argument Name resolves to the actual `HirParameterId` of `z`;
the callee resolves to module `g`. These are source occurrences in the local
initializer. Collection's containing-definition field does not relocate their
value ownership onto the module root.

The solver registers one parameter recipe for that actual Lambda parameter
(`crates/yu-solver/src/candidate_source.rs:188`–`:202`). Let `p_z` be that
jointly constructed recipe position. Parameter Names use
`CandidateEndpoint::Parameter(p_z)` (`:210`–`:216`), and
`candidate_endpoint` translates it to the checked live row

```text
Z = session.parameter_live_base + p_z
```

(`crates/yu-solver/src/shadow_apply.rs:1287`–`:1304`). Initial session
construction allocates one actual row for each parameter recipe
(`crates/yu-solver/src/lib.rs:10092`–`:10107`). This establishes the parameter
target's identity without choosing numerical ordinals. The Name's independently
allocated expression component does not replace `Z`.

The source-owned Apply input retains the argument endpoint, original expression,
callee and original result component (`candidate_source.rs:393`–`:409`;
`candidate_call.rs:29`–`:47`). The formal-registration consumer retains the
same parameter endpoint as its native root (`candidate_source.rs:544`–`:558`).
These facts identify a source reference target and its native argument port.
They do not establish the outgoing references of a value owned by `Z`.

In particular, the source gives `z` a **formal binder**, not a local initializer
expression. `LocalSourceParameter` has the parameter identity, source location,
scope and optional annotation (`local_source.rs:154`–`:161`); the distinct
`LocalSourceBinding` has an initializer (`:163`–`:171`). The initializer belongs
to `inner`, not to `z`. Reading `Name(z)` as the value *owned by* `Z` would
reverse the source reference's owner and target. Reading `g z` as that owned
value would instead move the Apply result onto its argument. Neither follows
from these constructors or the reviewed original-root proof.

## Copy owner and the earliest missing premise

Take the actual `(C,Z)` allocation from the frozen conditional theory input,
under H_prefix. This packet does not repeat its admission/replay/level proof.
The direct copy owner is `candidate_extrude`
(`crates/yu-solver/src/candidate_extrusion.rs:21`). Its inputs are an actual
endpoint, polarity and target level. At the row branch it snapshots selected
bounds, allocates a fresh Value row, retains the parent and memoizes the actual
copy (`:83`–`:123`). `fresh_value_at_level` creates a new checked row with
default bounds and Fresh metadata (`lib.rs:10156`–`:10177`). Parent retention
stores actual row identities, polarity and target (`candidate_intrusion.rs:178`
–`:220`); it deliberately supplies no adjacency edge.

The operation's later `Work::Bound` transports selected endpoint payloads and
their admission origins (`candidate_extrusion.rs:308`–`:324`), and
`Work::Function` replaces structural ports using this same operation-local map
(`:325`–`:353`). This establishes what native inference transports. It is not
an established source-value/reference transport clause. An empty selected
snapshot would therefore not prove an empty semantic value, just as a stored
one-sided link would not by itself prove a semantic reference.

The earliest missing premise in this method occurs already at the original
formal row: **an independently established source/operation correspondence
identifying the value owned by `Z` and its actual outgoing reference targets**.
The parameter identity and incoming argument Name do not supply that premise.
To continue through the actual copy, the same correspondence must establish
what value `C` owns after this extrusion and how its reference targets relate
jointly to the original value and the operation's actual copy map. This is the
previous copy-owned-value obstruction with its original-row prerequisite made
explicit; it is not a new obligation invented to replace the parent claim.

The approved reference criterion applies once those source-owned contents and
targets are established. It cannot supply them merely from the existence of a
Value row. Thus no first semantic edge out of `Z` or out of `C` is derived
here, and neither required path is established. This is a failure of the
available derivation, **not** proof that those edges or paths do not exist.
No concrete runtime value, admissible typing, marginal witness or invented
graph interpretation is selected for an unknown formal. Missing implementation
fields do not prove semantic impossibility or justify removing intrusion.

The actual qualification consumer is `settle_candidate_intrusion`
(`candidate_intrusion.rs:358`): it constructs operational adjacency from rows
and structural endpoints (`:389` onwards), computes components, and compares
the retained pair's representatives (`:474`–`:486`). Establishing that this
consumer implements the approved value-reference qualification is a separate
source/scanner bridge. Neither that equivalence nor complete replay or later
activation follows from these storage constructors. Source-prefix validation,
semantic reference transport and scanner equivalence remain separate OPEN
frontiers.

## Primary-supplied complementary negative-result owner audit

Before freeze, the primary supplied the separate frozen dependency
`notes/progress/2026-10-11-extrusion-copy-source-owner-audit.md` and asked whether
its recoverable source-origin chain establishes the negative result-copy law.
Its exact source is `my f x = { my inner y = f y; inner g }; my g y = f`.
Write its pair as `(C_n,P_n)` **only in this section**, to prevent collision
with this packet's `(C,Z)`. Its source/prefix hypotheses remain conditional;
the new dependency does not establish this packet's source acceptance or move
any reference between artifacts.

That audit identifies `C_n`'s retained parent `P_n`, the original Apply result
component and the exact nested `f y` source. This is genuine retained origin
evidence. Direct native Apply construction confirms what is identified:
`shadow_apply.rs:1331`–`:1387` selects the original callee, argument and result
endpoints and records the original four-port NegativeFunction. The observer
checks actual HIR Apply/operand identities and those original demand ports
(`candidate_call.rs:282`–`:341`). It does not establish that the references in
the Apply syntax are the references in a value owned by its result row `P_n`.
In particular, the callee Name's reference to module `f` cannot be promoted
into `P_n -> F` or `C_n -> F` by matching the Apply origin. The same source
meaning must justify the result-owner incidence first.

At negative result extrusion, `candidate_extrude` copies the selected upper
endpoint payloads, memoizes `(P_n,Negative,1) -> C_n`, and reconstructs the
Function result port with `C_n`. The exact unresolved law is therefore:
**this selected operation determines the owned value of `C_n` and each actual
target referenced in it, in correspondence with the original Apply-result
value and the joint operation map**. Origin recovery supplies inputs to that
law; it does not prove it. Captured Graph/Row/Bound structures
(`candidate_scheme.rs:36`, `:77`, `:96`) retain live algebra and evidence,
which supplies no independent shortcut to the law. The demand remains queued
at the supplied stopping prefix, so later admission is not inferred. This
follow-up reaches the same obstruction rather than proving `C_n ->* P_n` or
any semantic negative-copy edge. It proves neither impossibility nor the need
for a new representation. Neither source's parent/copy SCC claim is closed.

## Economy audit and one next action

The earlier guarded constructor audit and this source-formal/copy-content
method leave the same decisive source-owned-value premise unestablished. A
third level/polarity trace, graph restatement or alternative source would not
discharge it. The required fidelity of qualifying equality remains A/B; this
note neither reclassifies nor closes that parent obligation. Attempting to
recover known source ownership from incidental row IDs or bounds is D
reconstruction debt, but evidence retention is justified only after showing
the corresponding semantic fact is actually known at its constructor. Adding
a source pointer or copying an AST without that argument would assume the
missing bridge.

One next action for the primary: resolve the original formal-row and
extrusion-row value correspondence at the existing formal-registration/Apply
and `candidate_extrude` owners, using the approved Value meaning and actual
joint identities; keep executable validation of this exact source prefix in
its own lane. Investigate existing construction evidence before proposing a
new certificate, and retain the parent gate OPEN until the missing premise is
established or a source-qualified counterexample is obtained.

## Checks, resources and frozen dependencies

Commands used: bounded `cat`, `rg`, `sed`, `head`, `nl`, `sha256sum`, and patches of
the exact leased note. One broad locator query included nonexistent `spec/`
and returned that missing-path diagnostic; it supplied no premise. No tests,
builds, Oracle/compiler executions, executable probes, Git commands, child
launches, model escalation or compiler edits ran. One bounded static attempt;
stop condition reached at the source-owned-value premise. At most four
lightweight read processes ran concurrently. Zero heavyweight processes and
zero measurement samples. CPU/RAM and total reasoning wall time were not
measured; no numerical local compute budget was supplied. The primary retains
verification and integration ownership.

Requested route: `gpt-6.1-sol` / `high`, as supplied by the primary's packet.
Observed effective model/effort: **unknown**, because runtime metadata is not
exposed to this leaf. `.codex/config.toml` registers `prover` and defaults to
Sol/high; `.codex/agents/prover.toml` omits model/effort pins. Those files and the
callable role schema were inspected; configuration is not runtime evidence.
No hot reload or routing override is claimed.

SHA-256 snapshot of direct dependencies (none edited by this leaf):

| Path | SHA-256 |
|---|---|
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/theory/2026-10-11-mutual-recursion-parent-copy-proof.md` | `d198a3392cee6907b37a3856c3582b05e9bf7ea490876d1a5a3cf38a5d47507a` |
| `notes/progress/2026-10-11-mutual-recursion-parent-copy-search.md` | `e9241c2aa184ea7679525e912651e79b29f47a977d00aa28ffc0312e25dc8035` |
| `notes/theory/2026-10-11-mutual-recursive-value-scc-proof.md` | `332f757481af278e533f0e5d7eda2b3aa004e75d54f1d3e48c77b8f76d5a786d` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/shadow_apply.rs` | `230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/candidate_call.rs` | `79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `notes/progress/2026-10-11-extrusion-copy-source-owner-audit.md` | `81f5668eb4a66a624cbc82e12af026689bf1b82d97b74ca17c2e6bd9abbd3cd9` |

All initially hashed direct dependencies were rehashed before freeze with no
change; the two supplemental dependencies were hashed after inspection.
Baseline comparison and branch validation remain
primary-owned because this packet prohibits Git. No source acceptance,
whole-history reference meaning, scanner equivalence, generalization, effects,
complete Call, soundness, principality or production/cutover certification is
claimed. No shared record changed. Independent review is pending; the producer
does not certify this note.

## Commit packet

Exact leased path: `notes/theory/2026-10-11-extrusion-copy-reference-proof.md`.
Baseline: `35e88c8113c9c6516e260170503bea753e4ede6`.
Changed dependency hashes: none caused by this worker; baseline deltas unknown,
primary integration comparison required. Status: frozen research obstruction,
unreviewed, parent OPEN. Checks already run: static source reads and dependency
hashes; no tests/builds/Oracle. Proposed one-line message:
`research: locate formal-value and extrusion-copy reference bridge`.
Shared-record delta left to primary/curator: record the exact `(C,Z)` source
identity and original-formal prerequisite of the unresolved copy-value bridge;
preserve source-prefix, semantic SCC, scanner and dependent inference gates
OPEN. This is an obstruction handoff, not proof progress or gate closure.
