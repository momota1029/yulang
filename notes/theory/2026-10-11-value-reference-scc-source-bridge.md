# Value-reference SCC: candidate relation and first source bridge obstruction

Status: reviewed bounded research; proposed relation, conditional derivations and source characterization
Parent claim: OPEN; no semantic adoption, theorem closure or compiler conformance certification
Independent review: compiler_referee passed bounded semantic/source-bridge review; all original parent gates remain OPEN
Baseline supplied by primary: `57820e44e`, branch `research/simple-sub-intrusion`
Exclusive output: this file

## 1. Frozen objective, authority and quantifiers

For every supported source program `P`, every actual inference history `h` for
`P`, and every retained extrusion pair `(c,p)` of **Value variables**, identify
the actual values owned by those variables and their directed references.
Determine whether the compiler's qualifying SCC test computes that relation
before it equates `c` with `p`. Supply the construction/transport bridge through
constraint generation, accumulation, extrusion, later uses and generalization.
The full bridge must preserve original lexical binders/scopes, distinct copies,
shared captures and fresh-use independence. It must not replace complete Call,
effect hygiene, soundness or required principality with a graph fact.

The primary's current user decision governs: vertices are Value variables;
edges are references **in their values**, not subtype comparisons. Parent
metadata alone neither connects nor identifies vertices. Parent/copy equality
is permitted by the selected qualifying SCC intrusion operation, not by a
source-binder quotient. No claim is restricted to the displayed example or to
nonrecursive bindings in order to obtain closure.

Exact authority: `notes/design/2026-10-10-parent-copy-scc-intrusion.md`,
**Selected operation and compiler responsibility**, **Value-reference SCC
clarification**, **Retained boundary**; and
`notes/design/2026-10-11-yulang-inference-top-level-principles.md`, §§1–5 and
**Evaluation**. The primary-supplied
`notes/design/2026-10-11-source-value-reference-intrusion-draft.md` is a Draft;
its **Source-value reference graph**, **Relations that must remain distinct**
and **Missing bridge** delimit this research question, not new authority.
`rules/compiler-engineering.md`, **Natural compiler behavior and
proof-obligation economy**, forbids solving this gap by restricting inference
or adding another ungrounded reconstruction mechanism.

Original conclusion sought: an independently grounded interpretation of actual
Value references and faithful source/operational construction, sufficient to
justify the SCC qualification of actual parent/copy equality. This packet does
not establish that conclusion. It stops at the first unprovided ownership
constructor premise. Its bounded independent review does not certify closure
of that parent claim.

## 2. Candidate relation on actual Value identities

Let `V_h` be the actual allocated Value-variable identities in history `h`.
In the candidate implementation these are Value rows; Effect rows and immutable
positive/negative Function nodes are not vertices of this proposed graph.
Use raw distinct identities before a qualifying equality. After an already
justified equality, canonical identity may be used; that equality must not be
assumed while establishing its own qualification.

The unresolved input is an ownership interpretation `C_h`: for each relevant
`v ∈ V_h`, it gives the actual constructed value owned by `v`. It must come
from the owning constructors and history, not from arbitrary assignments of
stored bounds to values. For notation only, write owned construction syntax
using literals, `Ref(w)`, application, lambda/body, transparent group/ascription
and block/result constructors. A declaration initializer has its own owner;
traversing the surrounding block's owned value excludes that initializer.
This notation does not propose an additional compiler representation or a new
restriction on source programs. Other supported value constructors must receive
their actual ownership clause; coverage of them is not assumed.

Define direct owned references `refs` structurally:

```text
refs(literal)                    = ∅
refs(Ref(w))                     = {w}
refs(Apply(a,b))                 = refs(a) ∪ refs(b)
refs(Lambda(parameter,body))     = refs(body)
refs(Group(a)) = refs(Ascribe(a)) = refs(a)
refs(Block(declarations,result)) = refs(result)
```

Each declaration initializer is considered separately at its own owner.
A parameter declaration does not itself add a reference; an owned occurrence
that resolves to it does. Referencing a variable does not inline the referenced
variable's owned value: that variable supplies the next graph vertex.

The **candidate mathematical relation** is

```text
R(C_h) = {(v,w) ∈ V_h × V_h | w ∈ refs(C_h(v))}.
```

This fixes adjacency independently of constraint direction, storage side,
lexical containment and parent provenance. The parameter `C_h` is an explicitly
unprovided bridge premise. Defining `R(C_h)` does not assert existence of a
source-faithful `C_h` in the implemented solver. In particular, this note has
not defined the concrete operational graph `R_h` merely by naming its missing
interpretation.

SCC qualification then has the ordinary exact meaning
`p R(C_h)* c ∧ c R(C_h)* p`, with reflexive transitive closure. For distinct
parent/copy identities this requires real paths in both directions. A self-loop
is a cyclic singleton SCC; it does not identify a distinct parent and copy.

## 3. What follows, and under which hypotheses

**Conditional owned-reference lemma.** Given a single actual `C_h` with the
clauses above, the outgoing references of an application are the union of its
owned operand references; those of a lambda are those of its owned body; nested
declaration initializers contribute only at their separate owners. Proof:
structural induction on the finite owned construction, using exactly the
displayed clauses. No constraint or bound-storage assumption occurs.

**Conditional transport lemma.** Fix one jointly supplied variable map `θ` for
an owned construction and its reference leaves. If an actual transport replaces
each `Ref(w)` by `Ref(θ(w))`, preserves these constructors and respects separate
initializer ownership, then
`refs(transport_θ(t)) = θ[refs(t)]`. Proof: induction; singleton image at Ref,
empty image at literal, images commute with union at Apply, and the remaining
clauses use the induction hypothesis. This is not an extrusion proof: the
actual polarity/target keyed copy map, selected bound transport, fresh uses and
shared captures have not been shown to transport this owned construction.
Different marginal choices of copies cannot satisfy the hypothesis in place
of one actual jointly constructed map. SCCs need not be unchanged by transport.

**Source-binding characterization for the accepted example.** The independently
given binding projection for

```yulang
my host z = {
  my outer x = {
    my g y = outer g;
    x
  };
  outer
}
```

is `host→outer`, `outer→x`, `g→outer`, `g→g`. Only `g` has a cycle, and it is a
singleton. This follows from separate initializer ownership and name resolution;
there is no path back to `g` from `outer` or `x`. It supplies neither a map of
extrusion copies nor SCC membership for solver variables. No binder quotient
is used as a substitute for the required graph.

## 4. Actual producers and consumers inspected

| Owner | Concrete construction fact | Remaining semantic bridge |
|---|---|---|
| HIR `module/local_source.rs:332`, `:636`, `:819` | Initializer work introduces its own local identity and parameter scope; IdentifierExpression resolves the latest lexical binding; Block schedules initializers separately from its final expression. | Resolution and syntax ownership do not identify an owned Value-variable value or a copied target. |
| Solver `candidate_source.rs:202`, `:233` | Expression components and parameters are allocated/planned; a parameter Name uses `CandidateEndpoint::Parameter`, rather than its own component endpoint. | Which actual Value variable owns the containing value, and which actual `Ref` it constructs. |
| `candidate_source.rs:372`, `:665` | A forming local Name emits `Action::Link(initializer endpoint, Name component)`; execution submits a positive-to-negative subtype link. Published locals use `Action::Local`. | The link is a comparison. Its endpoints alone do not supply the owner-to-target reference required above. |
| `candidate_source.rs:394`, `:445`; `shadow_apply.rs:1304`; `lib.rs:11233` | Apply retains callee/argument/result endpoints, constructs a negative four-port Function demand and submits it. Lambda constructs argument/body/result/effect ports. | Ports have actual structural constructors, but their type positions alone do not prove an occurrence belongs to the value of a particular Value vertex. Complete Call is separate. |
| `candidate_extrusion.rs:85` | Wrong-level rows get actual fresh same-kind copies. Parent retained before descent; memo keys include endpoint, polarity and target; selected bounds are transported. A one-sided bound links original and copy. | Does each transported payload represent an owned value reference, and which actual reference target is replaced by which copy? The bound link is not automatically a reference edge. |
| `candidate_scheme.rs:1316`, `:1354`, `:981`, `:1500` | Local publication retains `LocalScheme(id,root,boundary)`. Later use captures the live graph, supplies one actual row remap, shares canonical rows, preserves non-generic captures, restores bounds and submits the final subtype link. | Ownership/reference interpretation of the captured interface and its remap, including references not represented by that interface. |
| `candidate_intrusion.rs:358`, `:390`, `:447`, `:476` | Consumer traverses lower and upper payloads, structural Function nodes, Effect rows/views and all four Function ports, then compares actual parent/copy component IDs and merges qualifying pairs. Parent provenance is not itself inserted into adjacency. | Equivalence of that mixed operational traversal to SCC reachability in `R(C_h)` is unproved. Removing Function/Effect vertices would need a justified Value-path interpretation, not arbitrary deletion. |

These are bounded construction facts established by direct source inspection,
not a theorem that every history has the proposed interpretation. A stored
payload is not disqualified because it is lower/upper stored. It also is not
qualified merely because it is stored there. Each incidence needs its actual
owning value/reference constructor.

The original ordinary Simple-sub constructors do not supply that missing law.
Pinned reference `Typer.scala:59` returns an instantiated type at Var, builds
Function(parameter,body type) at Lam, and returns a fresh result variable after
the App comparison. `:115` stores/replays bounds; `:134` extrudes with a
polarity-keyed cache; `:166` freshens a type scheme with shared variables. Its
`Variable` representation at `:223` owns bounds and a level, not a source value
body. These directly justify their ordinary type operations. They do not
declare source-owned Value-reference SCCs or Yulang parent/copy intrusion.
The reference's omission is not an impossibility theorem about Yulang.

## 5. Minimal outstanding obligations and earliest missing premise

1. **Owned Value introduction (OPEN, earliest).** For actual allocated Value
   identities, derive `C_h` and the occurrence-to-owner/target correspondence
   from source construction. At a resolved Name occurrence, prove which actual
   containing Value owns its `Ref(w)` and how its resolved binding/parameter or
   fresh use selects that actual `w`. Preserve original scopes and initializer
   boundaries. `emit_candidate_source` allocates endpoint recipes and retains
   the occurrence, but does not supply this law. Scope labels may be inputs;
   they are not themselves the law.
2. **Native accumulation bridge (OPEN, depends on 1).** Classify each actual
   direct/exact stored incidence by the value/reference construction it retains
   or by its independent checking responsibility. Prove activation/replay of
   required native constraints separately; storing them is insufficient.
3. **Extrusion/later-use bridge (OPEN, depends on 1–2).** Show how actual copy
   constructors and one jointly retained use map transport owned references,
   preserving distinct parent/copy and shared captures. No universal parent
   edge, copy collapse or independently chosen witnesses is allowed.
4. **SCC/equality consumer bridge (OPEN, depends on 1–3).** Establish that the
   implemented graph's relevant Value reachability equals the approved relation,
   and that later solver use observes only equality licensed by that relation.
   The mixed Effect/Function traversal needs its own justified interpretation.
5. **Generalization/publication bridge (OPEN, depends on 1–4).** Connect the
   retained generalized value interface and all fresh instantiations to the
   same construction, with lexical scope and non-generic captures preserved.
   Complete Call, effect hygiene, soundness and required principality retain
   their existing owners and remain OPEN; none follows from these graph lemmas.

The first missing evidence is therefore **the actual Value-owner introduction
and resolved-Name reference lemma**, before any SCC calculation. The inspected
owners are `candidate_source.rs` endpoint planning/Name dispatch together with
the source-value constructors in `shadow_apply.rs` and `admit_lambda_fact`.
An actual constructor-directed interpretation, with its induction covering
Name, Lambda, Apply, Block and use identities, would close this premise.
A canonical retained owner/reference output could make the argument follow by
construction if the primary determines that these owners already know the fact;
this note does not require that particular representation or authorize code.

No third equivalent payload-graph proof is proposed. The minimal audit is:
graph qualification is required A/B insofar as it licenses actual inference
equality; guessing lost ownership from bounds is potential D reconstruction
debt. The phase that knows resolved occurrence and initializer ownership is the
source constructor. A source-directed owner law is the next decisive evidence.
This audit does not change any parent gate's status or weaken its statement.

## 6. Dependencies, checks, runtime and handoff

Read-only commands: governing-file reads, bounded `rg`/`sed` source tracing,
and `sha256sum` on the exact dependencies below. No test, build, executable probe,
Git operation, delegation or compiler edit was performed. One constructive
attempt; no exhaustive search or measurements; one shell command process at a
time except initial lightweight independent reads. Runtime CPU/RAM totals were
not measured. Requested role: prover, normal Sol/high route. Effective runtime
model/effort metadata is unavailable to this leaf and is **unknown**; local
configuration is not execution evidence. No Astra assignment was requested.

Dependency SHA-256 snapshot (read live files under the primary's supplied
baseline; equality to baseline content was not independently checked with Git):

| Path | SHA-256 |
|---|---|
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0` |
| `notes/design/2026-10-11-source-value-reference-intrusion-draft.md` | `4323a2223dbeb563f7822e6ff4fb889438c36d5a9139c0872070ac8112fefd94` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/shadow_apply.rs` | `230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| Reference `shared/src/main/scala/simplesub/Typer.scala` | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |

Reference root: `/home/momota1029/rust/simple-sub-reference`, primary's recorded
reference baseline `9bae772624c23b52a93c1b226157e16898b4d9db`. Governing rules
read: design authority, compiler engineering, agent orchestration, research
laboratory, Git concurrency and orchestration budget; prover role/config and
the yulang-proofs skill. Shared startup/index records were consulted as locators,
not as a semantic source or evidence of running jobs.

One next action: primary assigns the exact actual Value-owner/Name constructor
lemma, or obtains the missing owning definition, before another semantic SCC
reachability attempt. The source-to-solver, qualifying equality, soundness and
principality claims remain OPEN. Independent bounded review passed without
closing those parent claims.

Commit packet: exact lease `notes/theory/2026-10-11-value-reference-scc-source-bridge.md`;
baseline `57820e44e`; dependency changes unknown pending primary baseline/hash
comparison; reviewed bounded research only; source reads and hashes already recorded,
no builds/tests. Proposed message:
`research: localize Value-reference SCC ownership bridge`.
Proposed shared-record delta for the primary/curator: record the unprovided
actual Value-owner/Name introduction as the first bridge premise and preserve
all affected parent gates OPEN. This leaf changed no shared record.
