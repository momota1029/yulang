# Mutual recursion: constructive source-to-Value-root SCC bridge

Status: frozen, independently reviewed bounded constructive source bridge
Parent claim: OPEN; no full graph, scanner, extrusion or inference certification
Independent review: compiler_referee accepted exact two-root source-reference SCC scope; broader claims remain OPEN
Baseline supplied by primary: `a87a07eed9c9b6e911fd7b2f6ecc0d325d8f1ede`
Exclusive output lease: this file

## Frozen statement and authority

The primary selected the exact supported module source:

```yulang
my f x = g;
my g y = f
```

For each successful source lowering and component/session construction of this
module through the inspected owners, before any subsequent identification of
its distinct root rows, let `F` and `G` be the **actual allocated Value rows**
for the definition roots of `f` and `g`. Establish source-owned reference paths
`F → G` and `G → F`. The vertices are these actual rows, not source binders
substituted for rows. The conclusion is a nontrivial SCC in the source-level
Value-root reference graph. It does not assert that the compiler's operational
intrusion scanner computes that graph or that an extrusion parent/copy pair
belongs to this SCC.

The original broader obligation in
`notes/theory/2026-10-11-value-reference-scc-source-bridge.md` quantifies over
supported programs, inference histories and retained extrusion pairs. It
remains OPEN. The present witness discharges only the primary's bounded
source-root question. Selecting the smaller mutual source removes an
unnecessary Apply constructor from this witness; it imposes no restriction on
ordinary inference or the broader obligation's source domain.

Authority is the direct user rule recorded in
`notes/design/2026-10-10-parent-copy-scc-intrusion.md`, **Value-reference SCC
clarification**, together with **Selected operation and compiler
responsibility** and **Retained boundary**: edges are references in values;
comparisons and parent metadata are not edges; actual extrusion copies remain
distinct until qualifying equality. The selected parent/copy operation is
retained. The top-level inference principles, §§1–5 and **Evaluation**, retain
native Simple-sub inference, soundness, effect hygiene and required
principality. The collection foundation's **Oracle invariant** governs
predeclaration and open recursive use, rather than redefining the semantic
Value graph.

The original scopes and binders are fixed: `f` and `g` are distinct module
definitions; `x` belongs to `f`'s Lambda and `y` to `g`'s Lambda. Neither
parameter occurs in either body. There are no local declarations, shadowing,
annotations, applications or external bindings in this witness. All maps below
come jointly from this one constructed artifact/session; no independent choice
of target identities or copies is permitted.

## Exact source and Value-identity map

Write `d_f,d_g` for the actual `DefinitionOrderId`s, `r_f,r_g` for the actual
HIR `DefinitionRootId`s, and `o_g,o_f` for the respective Name occurrences in
`f`'s and `g`'s Lambda bodies. These are locators for constructed identities,
not prescribed numeric ordinals.

1. HIR constructs the namespace for all root plans before lowering any body
   (`crates/yu-hir/src/module.rs:943`, `:1322`). Each spelling has exactly one
   definition. The forward `g` in `f` therefore resolves to `g`, and the `f`
   in `g` resolves to `f`. Parameter lookup only considers `x` or `y`, so it
   cannot intercept these module names (`:2137`). Root lowering wraps the
   owned body in the corresponding Lambda and retains it as
   `HirBinding.value()` (`:1389`, `:1472`). Thus the actual owned source values
   are `Lambda(x, Name(o_g,g))` and `Lambda(y, Name(o_f,f))`.

2. Collection registers each binding's own root before its body
   (`crates/yu-solver/src/lib.rs:984`). `add_definition_root` (`:1676`) invokes
   `definition_value_component` (`:1897`), constructing
   `ComponentId::DefinitionValue { root: r_f }` or `{ root: r_g }` and recording
   its exact component position. The `CollectedDefinition` for that same
   binding retains its root (`:1092`). This is the owning root construction,
   not an inferred association from matching types or bounds.

3. Define the single actual map

   ```text
   k(d) = batch.root_component_positions[batch.definitions[d.ordinal].root].component
   β(d) = session.live_components[k(d)].ordinal
   F = β(d_f),  G = β(d_g)
   ```

   Session construction gives every Value component one checked, successively
   allocated dense Value ordinal (`lib.rs:10047`). Different root positions
   therefore receive different raw Value rows: `F ≠ G`. Their kind is Value
   by the `DefinitionValue` constructor. Both maps preserve the same HIR
   artifact and collection artifact; no binder quotient or parent/copy
   canonicalization enters this argument.

4. The Name constructor retains the actual resolved occurrence and its
   containing definition. On the LocalSource route,
   `candidate_source.rs:376` queues
   `PendingDefinitionUse { parent_ordinal: d_f.ordinal(), target: g, occurrence: o_g }`
   and the converse record for `o_f`. On the ordinary retained-HIR candidate
   route, `shadow_apply.rs:1188` queues the same information from the resolved
   `ResolvedExpr::Name` while the Lambda traversal carries the containing
   definition (`:1085`, `:1119`). The simple ordinary Lambda route in
   `lib.rs:1235` also records the resolved Name body. No Apply reconstruction
   is needed. LocalSource itself preserves the same parameter-first/module
   lookup (`module/local_source.rs:636`) and owned Lambda body (`:269`).

5. The final endpoint pass resolves each target through the actual collected
   definition map, retains the exact parent and target identities, and freezes
   the occurrence and target-root component positions (`lib.rs:1275–1327`).
   The resulting records are:

   | Owned Name occurrence | `parent` | `target` | Actual target Value row |
   |---|---|---|---|
   | `o_g`, in `f`'s owned Lambda body | `d_f` | `d_g` | `live_components[target_root_component].ordinal = G` |
   | `o_f`, in `g`'s owned Lambda body | `d_g` | `d_f` | `live_components[target_root_component].ordinal = F` |

   The actual occurrence rows `U_g` and `U_f` are independently retained by
   `use_value_component`. They are not silently identified with `G` or `F`.
   The containing root is obtained through `k(parent)` above, so the records
   trace both endpoints to actual Value roots.

## Derivation

For this bounded source-root graph, a reference occurrence in a binding's
owned source value witnesses an edge from that binding's actual Value root
to the referenced binding's actual Value root. Steps 1–3 establish who owns
the source value and which actual Value row carries its definition root;
steps 4–5 establish the resolved reference and its actual target root. This
uses the user-selected reference meaning directly. It does not require the
compiler to retain a second term-AST representation or recover ownership from
solver comparisons.

The occurrence `o_g` lies in `f`'s own Lambda body and resolves to `g`.
Consequently its owner is `F` and its target is `G`: `F → G`. The occurrence
`o_f` lies in `g`'s own Lambda body and resolves to `f`, giving `G → F`.
These are paths of length one in both directions. Since `F ≠ G`, they belong
to one SCC containing at least two distinct Value roots. In the restriction
to these two roots, the only reference edges are these two edges and its SCC
is exactly `{F,G}`. No exact maximal SCC of the complete solver graph is
claimed. The parameters supply no reference edges because they have no owned
occurrences. A singleton self-loop would still be an SCC, but this witness
contains two distinct roots.

The `DefinitionUse` SCC is not itself this proof: its records provide the
source occurrence evidence, and `β` supplies the actual Value identities.
The graph argument uses those actual root vertices and their source-owned
reference witnesses, rather than treating a dependency SCC or a subtype fact
as an automatically semantic SCC.

## Native operations and the exact retained boundary

The native consumers confirm that these are the intended open recursive
targets. `candidate_scheme.rs:869` installs both actual roots and their
internal uses before executing either source schedule. `:938` validates the
same parent/target use and routes it through `route_internal`; `lib.rs:15765`
uses precisely `target_root_component` and `use_value_component`. Its admitted
judgment is `target_root <: occurrence_row`. That judgment is **not** used as
a reference edge in the derivation.

For this simpler source, native Lambda construction takes its body result
directly from the resolved Name occurrence (`lib.rs:11233`) and constructs the
four-port Function (`:11342`). The retained-HIR candidate recipe can use the
definition root directly (`shadow_apply.rs:1093`, `:1154`); the LocalSource
recipe uses its Lambda expression component and later links that expression
to the definition root (`candidate_source.rs:445`, `:477`). These different
native type recipes do not change the source-root occurrence witnesses above.
They also do not establish additional graph edges merely by their subtype
links.

The optional factorization `F → U_g → G` and its converse is not required.
Such a claim about occurrence-row-owned values would require establishing
that additional ownership interpretation. This proof makes no such claim.
It also does not give owned values or reference transport for every internal
Value row, structural Function node, Effect row, extrusion copy or fresh use.
The reviewed candidate note's whole-history `C_h` premise therefore remains
OPEN; the result here supplies the source-to-actual-root part only.

In particular, `candidate_intrusion.rs:358` builds a different operational
graph by traversing bound payloads and structural nodes. Its equivalence to
the source graph has not been established by this proof. Scanner conformance,
copy reference construction, parent/copy SCC reachability, generalization and
fresh-use transport remain OPEN. No stored-constraint replay completeness,
complete Call, effect hygiene, soundness, required principality or production
cutover conclusion follows from this witness.

## Corroboration, checks and frozen dependencies

Existing test source corroborates that the selected syntax and mutual Lambda
shape are supported: `crates/yu-solver/src/tests/shadow_f5.rs:34` and
`crates/yu-solver/src/lib.rs:23072` contain this exact source. The latter
checks productive Function recursion. These are test-source locators, not
theorem premises or newly executed verification; neither test was run here.

Checks performed: `cat`, bounded `rg`/`sed` source tracing, dependency
`sha256sum`, and inspection of this exact leased output. No build, test,
Oracle process, executable probe, delegation or compiler edit ran. Initial
startup accidentally included read-only `git status --short` and
`git rev-parse HEAD` despite the packet's no-Git instruction; the latter matched
the supplied baseline. No Git mutation or subsequent Git command occurred.

One bounded constructive attempt with the primary's narrower source steering;
no equivalent replay of a payload-graph proof. At most four lightweight read
processes were concurrent during startup; subsequent source reads and the
single output write were sequential. Zero build/probe processes and zero
measurements. CPU/RAM and model reasoning wall time were not measured.
Normal requested route: Sol/high; observed runtime model/effort metadata is
unavailable to this leaf and recorded as **unknown**. No Astra escalation.

Dependency SHA-256 snapshot:

| Path | SHA-256 |
|---|---|
| `notes/theory/2026-10-11-value-reference-scc-source-bridge.md` | `1bc8b29b7b1f3995bf3adedf604fe15db80be8e4bc8f1d0771644a449d086aef` |
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/design/2026-09-20-constraint-collection-scc-foundation-draft.md` | `37a2799288db0081cf3f32c7f6860c376ff0b2ce3249397cd9c23c7a89fedeaa` |
| `crates/yu-hir/src/module.rs` | `943dcab6440ffb70061f08641afa13fa8b36c5689a326d07288b9593e17ba8f5` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/shadow_apply.rs` | `230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/scc.rs` | `3cfce9acfddd77838398cd95cd13c053f71f27a8367b07175a83c825d68a8df8` |
| `crates/yu-solver/src/tests/shadow_f5.rs` | `60ec24053fc89358e16078d3e9a1af04a787c826aac127542ae984eff9fbf0f0` |

These hashes record the inspected live dependency snapshot. No compiler
dependency was changed by this leaf. Comparison to baseline contents and
integration revalidation remain primary-owned. Governing rules, registered
prover config and `yulang-proofs` skill were read; configuration is not evidence
of observed runtime routing.

Independent bounded review accepted this original-root bridge. The next action
is extending it to extrusion-created identities and the intrusion consumer;
scanner equivalence and lifecycle remain OPEN.

Commit packet: exact lease
`notes/theory/2026-10-11-mutual-recursive-value-scc-proof.md`; baseline
`a87a07eed9c9b6e911fd7b2f6ecc0d325d8f1ede`; only that new research artifact
changed; changed dependency hashes not observed, baseline comparison pending;
frozen independently reviewed bounded research, no parent-gate closure;
reads/hashes already run, no builds/tests. Proposed message:
`research: derive mutual source reference SCC on actual Value roots`.
Shared-record delta left to primary/curator: record this bounded constructive
root witness and preserve full operational graph, copy lifecycle and all
dependent inference gates OPEN. No shared task, index or status record changed.
