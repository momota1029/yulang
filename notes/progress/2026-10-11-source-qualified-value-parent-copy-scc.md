# Operational bound-payload trace for a recursive source fixture

Date: 2026-10-11
Status: delta-reviewed bounded operational source/constructor trace; source Value-reference theorem OPEN.
Baseline: `330d5432aff4b1f9655d501e17a9eefb7e75e098`, branch
`research/simple-sub-intrusion`.
Exclusive lease: this file. No compiler edits, executable probes, tests, builds,
Oracle invocation, Git mutation, or children.

## Objective, authority, and claim class

Trace one source fixture through the current candidate constructors, recording
retained parent/copy identities, physical bound payloads and cycles in the
operational scanner. Identify where this operational trace stops short of the
user's source-Value-reference SCC claim. This note does not assert that a
physical bound incidence is a reference in the semantic Value owned by its
row. The primary supplies the source-reference authority and Simple-sub
characterization named below; this note does not certify their semantic bridge.

The current user decision fixes vertices as Value variables and edges as
references in their values. Comparisons and retained family records do not
create edges. Parent/child and nephew/uncle references may form SCCs. This
packet does not choose a different graph meaning or infer ordinary inference
success from a numerical nonreachability argument.

Exact governing sections:

- `rules/design-authority.md`, “Authority order”.
- `notes/design/2026-10-10-parent-copy-scc-intrusion.md`, “Direct decision”,
  “Selected operation and compiler responsibility”, and the current direct-user
  “Value-reference SCC clarification”. The clarification is an accepted
  working-tree dependency supplied by the primary, beyond the baseline file.
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md`, §§1–3
  and “Authority and integration”.
- `rules/research-lab.md`, “One semantic baseline, explicit dependency
  invalidation”, “Writes, artifacts and review snapshots”, and “Evidence
  quality and stopping unproductive loops”.
- `rules/git-concurrency.md`, “Disjoint-file mode”.

Claim class: bounded operational bound-payload derivation of a real extrusion
prefix and a later equal-level cycle in the scanner's current adjacency. It
does not establish a source-Value-reference edge, a source SCC, or a missing
semantic return edge. It is neither a source counterexample nor an all-source
rank theorem. The parent/copy and original inference/adequacy theorems remain
OPEN.

## A concrete source prefix creates an actual retained pair and payload trace

Use the existing source fixture at
`crates/yu-solver/src/candidate_source.rs:695`:

```yulang
my outer = { my loop x = { my direct = loop x; my helper y = loop y; helper x }; loop }
```

The adjacent owning tests check the two open recursive links and later fresh
use, and contain a candidate solve assertion. Those assertions were inspected,
not executed here. The bounded derivation uses only the first `loop x` in
`direct`'s initializer, before the enclosing `loop` Lambda is admitted.

Explicit hypotheses: start through `try_new_candidate` with the ordinary
candidate source schedule for this fixture; allocations/identity checks
succeed; the first Name/Apply native drain and its replay reach their ordinary
Value dispatch; no test helper writes, externally mutated session, or reused
failed state is substituted. This claims the constructor prefix conditional
on those ordinary finite control steps, not whole-program execution or
termination. The source schedule and replay owners below determine physical
bound-payload incidences. They do not determine the semantic Value owned by
each row or which incidences are source-Value references. No checker is used
as an oracle for either question.

Let `F` be `loop`'s initializer Value row, `N` the callee Name occurrence row
in the first `loop x`, `X` the actual formal parameter row, and `P` that
Apply's result row. Ordinals are unnecessary; these are owning source objects.

1. Source traversal starts at level 1. A Block initializer alone adds one;
   Lambda and its body preserve the traversal level
   (`candidate_source.rs:253–298`). Therefore
   `L(F)=L(X)=2` and `L(N)=L(P)=3`. The level maps are installed before
   admission at `candidate_source.rs:532–541` / `lib.rs:10103`.
2. The parameter Name resolves directly to `X`, rather than its otherwise
   allocated expression component (`candidate_source.rs:210–216`). The open
   `loop` Name resolves to initializer endpoint `F` through
   `active_initializers` and emits `Action::Link(F,N)` before the Apply
   (`:294–298,381–385,665–669`). It is a comparison until the native bound
   owner selects `N`, the higher-level row, and physically installs `F` in
   `N.direct_lower_rows` (`candidate_extrusion.rs:815–830,464–471`). The
   resulting operational payload incidence is **N ↝op F**. Whether this is an
   edge in N's semantic Value remains unproved.
3. Apply owns a negative Function demand whose actual Value fields are `X`
   and `P` (`shadow_apply.rs:1331–1362`). It then compares `N` with that
   Function (`:1390–1410`). At receiving level 3, neither Value port needs
   copying. The upper-bound insertion on `N` yields operational payload
   incidences **N ↝op X** and **N ↝op P** through the stored Function fields.
   This establishes physical adjacency consumed by the current scanner, not
   source-Value ownership of these references.
4. `candidate_replay_bound` reads `N`'s lower `F` and new upper demand,
   and requests `F <: Function⁻(X, effects, P)`
   (`candidate_extrusion.rs:763–802`). Both installed bounds have retained
   admission origins; the replay owner enumerates their newly encountered
   fiber pair and queues its Value task
   (`candidate_context.rs:2911–2987,3058–3101`). This replay comparison is
   still a comparison and creates no physical payload incidence from `F` to
   `P` at this step.
5. At `F`'s level 2, structural dispatch calls negative extrusion before
   installation (`lib.rs:12430–12454`). `X` stays shared at level 2.
   The result port `P`, at level 3, is replaced by fresh `C` at level 2.
   Real retention records `(copy=C,parent=P,polarity=Negative,target=2)` and
   installs `C` in `P.direct_lower_rows`
   (`candidate_extrusion.rs:83–124`). Thus the operational bound-payload link
   is **P ↝op C**. The copied result port is `C`, not `P`; the semantic
   Value-reference status of this incidence remains unproved.
6. Function reconstruction preserves the rebuilt Value fields, and rewritten
   dispatch installs that negative Function on `F`
   (`candidate_extrusion.rs:325–355`; `lib.rs:12451–12454`). Its relevant
   operational payload incidences are **F ↝op X** and **F ↝op C**. The earlier
   unextruded demand remains owned by `N`; it is not also installed on `F`.
   Semantic Value-reference status remains unproved.

The current scanner's operational bound-payload adjacency in this prefix,
projected through Function syntax, is:

| Owner | Level | Relevant operational payload targets |
| --- | --- | --- |
| N | 3 | F, X, P |
| F | 2 | X, C |
| P | 3 | C |
| X | 2 | no new target from these steps |
| C | 2 | no new target from these steps |

The result row `P` has no previously emitted bound payload in this prefix;
negative extrusion copies its selected upper snapshot, which is empty.
Effect port copying and origin/context records are omitted from this table,
not from the compiler operation. They cannot supply a return path in the
inspected operational SCC adjacency. This is a source-created retained pair,
but **C and P are not in one SCC in this finite operational prefix**. No
claim about their SCC in the user's source-Value-reference graph follows.

## Source-Value ownership remains unproved

For this pair, `P ↝op C` is established as a physical payload incidence at
creation. That does not establish a source-Value edge. Before asking whether a
return path **C → … → P** exists in the approved graph, the owner/reference
meaning of each payload incidence must be established. The source-Value bridge
is missing already for `P ↝op C` and the Function ports; a missing physical
return incidence cannot be promoted to a semantic missing-edge result.

The two smallest attempted completions identify the responsible seam:

| Attempted completion | Actual native construction |
| --- | --- |
| Compare C with P in either subtype direction | `candidate_apply_value` stores the other row on the higher-level owner P in both cases (`candidate_extrusion.rs:815–824`). Both create operational `P ↝op C` payload incidence on different bound sides; neither creates operational `C ↝op P`. Whether either incidence is a source-Value edge is unproved. |
| Compare C with a Function having a Value port P | Structural dispatch extrudes at `L(C)=2` before insertion (`lib.rs:12412–12454`). A level-3 occurrence of P becomes a level-2 copy. C's stored Function payload contains that copy. It cannot be declared a semantic reference to P merely because P was the original comparison port. |

These are static discriminators, not invented source histories or additional
probes. A longer return path must contain an actual upward step if the
current bound ceiling premise holds. The earlier Value rank note investigates
that preservation premise; this packet does not re-prove it or treat its
conditional consequence as a normality certificate.

## Continuing the exact fixture through capture and later propagation

The source continuation gives a more direct operational trace than the rank
alone. It also builds cycles in the scanner's bound-payload adjacency; absence
of the particular parent from those cycles must not be mistaken for absence of
source recursion.

At the first `direct` installation,
`install_candidate_local_term` stores only `LocalScheme {root=P,boundary=2}`
(`candidate_scheme.rs:1315–1334`). It creates no bound or family edge. No
later Name in this exact fixture resolves to `direct`. Its surviving
metadata is therefore not an operational payload incidence to P. N's stored
demand contains P, while F's extruded demand contains C. The operational
adjacency has no F → N incidence; the actual recursive Name insertion adds
N → F. Whether these incidences belong to the semantic Values of N/F remains
unproved.

For the next binding `helper y = loop y`, write H for the helper Lambda root,
Y for its parameter, Q for its body Apply result, and Nh for that callee
Name. All four have level 3. The still-open loop initializer F remains at
level 2. The same Name/Apply owners produce operational payload incidence
Nh → F and the negative demand with fields Y,Q. Its replay at F extrudes the
argument positively and the result negatively to level 2, creating distinct
retained pairs `(Yc,Y,Positive,2)` and `(Qc,Q,Negative,2)`. The physical
payload links are **Y ↝op Yc** and **Q ↝op Qc**; F's second upper Function
contains Yc,Qc. Their source-Value-reference status remains unproved.
Neither that demand nor helper's own positive Lambda Function has a P port.
The helper Lambda's fields are Y,Q, and its boundary is 2.

The final `helper x` in loop's body is a published Local use at level 2.
Capture from H expands H,Y,Q (levels 3) and discovers shared Yc,Qc (levels 2).
It reads Y's upper Yc and Q's lower Qc with their exact owner and side.
The shared copies have no Value bounds from their creation; no Value port
from this capture reaches P or N. Fresh reconstruction gives H*,Y*,Q* at
level 2, retains Yc,Qc, and restores:

```text
H*.lower = Function+(Y*, effects, Q*)
Y*.upper contains Yc
Q*.lower contains Qc
```

These are the actual field/side constructors at
`candidate_scheme.rs:566–621,1008–1021,1141–1157,1227–1266`.
Capture's extra context-payload expansion at `:750–789` discovers Effect
tails, not hidden Value ports to P. Fresh evidence stores are not variable
payload incidences. None of H*,Y*,Q* receives a retained extrusion parent
merely by this allocation.

Let J be the `helper` Name row, R the result of `helper x`, and B the final
Block/body row of loop, all at level 2. The subsequent links and propagation
are owned as follows, under the same successful finite-control hypotheses as
the prefix:

| Actual comparison/restoration | Operational payload incidence produced |
| --- | --- |
| Fresh root H* linked to J | H* → J (equal-level row admission). |
| H*'s restored lower Function replayed against J | J owns that lower Function with fields Y*,Q*. |
| Apply demand on J has fields X,R | J owns the upper demand Function; its result comparison is Q* <: R. |
| Q* <: R with Q*'s restored lower Qc | Q* → R, then replay Qc <: R stores Qc → R. |
| Block final-expression Group links R to B | R → B. |
| Later loop Lambda supplies Function+(X,effects,B) at F | F owns that lower Function. |
| This Lambda compared with F's second demand Function−(Yc,effects,Qc) | Result child B <: Qc stores B → Qc. |

The exact row writer is `candidate_extrusion.rs:815–830`, its lower/upper
replay is `:763–802`, Function children are `lib.rs:12493–12530`, and Group
emission/admission is `candidate_source.rs:459–467` /
`shadow_apply.rs:1327–1330`. Consequently this bounded static continuation
derives the cycle **Qc → R → B → Qc** in the current operational
bound-payload adjacency. It does not establish a source-Value cycle or an
operational Qc → Q incidence: original Q remains the level-3 parent with its
outward payload incidence Q → Qc. P is likewise reached only from the older N
demand, not from C or this cycle. Argument comparisons also reach only the
remapped/shared parameter fields, not P or Q.

The final outer `loop` Name captures the actual F payload, now containing
the two rebuilt demands and the admitted Lambda. Its Function ports and
reachable row bounds involve C, Yc, Qc, X, B, R and helper-use rows at level 2.
They do not include original P merely because C has P in the separate parent
registry. `capture_candidate_graph_inner` starts at F and expands its owned
rows/ports (`candidate_scheme.rs:746–789`); it does not walk the registry
backwards. The published loop use at level 1 remaps these local rows to
fresh level-1 identities, preserving the cycle's captured sides and sharing.
It does not remap a parent record to equate fresh C with original P.

For a future source use of the published direct result P, the same existing
Local constructor would classify P local at boundary 2, retain shared C at
level 2, and restore operational payload incidence **fresh-P → C**. This is a
conditional statement about that constructor, not a newly checked fixture or
an assertion that such a use appears here. It still supplies no operational
C → original-P incidence. Thus this route supplies no source-Value ownership
law at the actual source emission, capture traversal or fresh reconstruction
seams.

Later Lambda admission first constructs a positive Function from the actual
parameter and body endpoints (`lib.rs:11233–11260,11342`), then admits its
root comparison. The Function fields are outward payload handles regardless
of contravariant comparison decomposition at `lib.rs:12493–12530`. Every
induced row/row or row/Function task again reaches the two owners above.
Recursive Name links remain genuine comparisons against the open initializer;
the family label does not add a reverse edge.

Published local Names take a different, concrete path:

- Capture records a row as local when its level exceeds the lexical boundary
  and it is generic (`candidate_scheme.rs:300–326`). Only local row owners
  have their bound payloads captured (`:566–621`); each side stays attached
  to its actual owner.
- `prepare_candidate_fresh_use` maps local rows to fresh use-level rows and
  retains shared identities (`:1008–1021`). All four Function fields use that
  joint remap (`:1141–1157`). Allocation does not retain an extrusion parent.
- `begin_candidate_fresh_bound` restores the captured side on its remapped
  owner (`:1227–1266`), then the Local cursor finally links the fresh root
  to the occurrence (`:1500–1519`). Freshening both P and C therefore does
  not create a retained parent record between their fresh counterparts.
- The actual lexical owner supplies `boundary B ≤ use level U`: Block
  publication and lexical stack restoration are at
  `crates/yu-hir/src/module/local_source.rs:366–373,396–437,637–647,819–829`,
  with the source level schedule above. Together with shared generic rows
  having `L≤B`, this gives the prior restoration ceiling premise; a
  nongeneric-row writer or native Value level update would need separate
  source evidence. Current nongeneric test mutations are not such evidence.

An equal-level nephew/uncle cycle in the operational payload graph remains
compatible with these observations. The reference theory's four-variable
operation trace explicitly derives one, but has no exact Yulang AST and does
not put either retained direct parent/copy pair in that SCC. It cannot finish
the source-to-operational ownership bridge.

## Operational consumer and the unresolved source correspondence

`settle_candidate_intrusion` follows both stored bound lists and the outward
Function payload fields (`candidate_intrusion.rs:390–413,445–468`). Function
vertices subdivide this operational bound-payload adjacency. An Effect-origin
path cannot return to Value in this scanner. It then qualifies the retained
canonical pair by equal component IDs (`:477–491`), without adding metadata
edges. This describes the implementation graph only.

If a path `C → … → P` is present in the implementation payload graph, the
scanner can qualify the pair. This does not show that the same path belongs to
the user's source-Value graph. The test adapter `close_cycle` in
`candidate_intrusion_tests.rs:45–55` forcibly restores `C → P`; it demonstrates
consumer operation on an installed graph, but bypasses the owning source
construction just identified. No test execution here validates that bridge.

The prior rank note's hypothesis is that every installed Value bound has
structural ceiling no greater than its owner, with levels stable before the
first Value merge. Its conclusion excludes a return path to the higher-level
parent. That is a conditional operational consequence of the current native
writers. It does not establish that those writers completely implement the
user-selected natural inference algorithm, that an intended source can never
require intrusion, or that a Value pair should be disallowed from an SCC.

Exact blocker: no authenticated source-to-Value ownership law has been
identified for the bound and Function payload incidences above, including the
incidence created by extrusion and those restored by freshening. Direct
admission stores on one owner; structural admission reconstructs a payload;
fresh allocation creates no parent record. Whether these constructors produce
the approved source-Value references remains OPEN. This bounded trace does not
claim exhaustive source nonexistence or authorize a source restriction or
implementation change.

Semantic adequacy is not established by this trace. The source continuation
shows which equal-level cycles the pinned implementation's operational graph
constructs and which retained higher-level pairs it does not join in the
inspected history. The proof that these payloads represent the user's source
Value references, and that copying preserves the required identities, remains
the open algorithm/source correspondence obligation. The user-selected
operation cannot be retired or silently redefined from this implementation
trace.

Recommended next action: define and prove the source-Value ownership map for
actual source, extrusion and freshening constructors, then compare its edge
set with the operational scanner on this fixture. Do not use the physical
return-edge analysis as a semantic SCC conclusion before that bridge closes.

## Checks, dependencies, and limits

Commands: bounded `rg`, `sed`, `cat`, `sha256sum`, read-only `git status`,
`git rev-parse`, `git branch --show-current`, `git show`, and dependency-scoped
`git diff <baseline> -- <paths>`. The source dependency diffs are empty.
An initial guessed HIR path `src/shadow/local_source.rs` did not exist;
the corrected owner is `src/module/local_source.rs` above. No source
enumeration, mutation, seed/range, executable oracle, or acceptance experiment
was run. Independent oracle comparison is inapplicable: the compiler's
constructors, payload fields and consumer are distinct inspected owners, but
share the same native level and polarity conventions.

Source SHA-256 values:

```text
candidate_source.rs    13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49
candidate_scheme.rs    9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1
candidate_extrusion.rs fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0
candidate_intrusion.rs aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0
intrusion tests        61e30f6fc52097ac8a3be3577284d45baa27ab528c4a7f109e3bfcedb405fd46
candidate_context.rs   4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987
lib.rs                 c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94
shadow_apply.rs        230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6
term.rs                75506948ec8043c9d5b4d0369ae94ed31c940aae0bc930ae1099bc1c758bb615
HIR local_source.rs    906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed
```

Frozen research/authority dependencies:

```text
native-value-reference-scc-map.md              66f8f068c453d491d45c09fe22a27f7a63ea5a31ca200b4cb15c4c21f4dbaad0
simple-sub-value-reference-scc.md               8dd8eb55ac9d9df75980182cb5483f9394674a94f77c9d70d12f89b5be0d24e6
local-restoration-value-scc-preservation.md     3dfd8ba4b21b76ee434a6b30697c5197213eae0679b84b98a6908e8a512fe6c4
parent-copy-scc-intrusion.md (current decision) 2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0
parent-copy-scc-intrusion.md (baseline)         8ae4348a93dce6df1852a34b2294ebc5e4e256d8b018c1f6eaad42c502470a8e
top-level-principles.md                        edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389
```

Resource use: lightweight shell reads only; zero Cargo/build/test/probe
processes, benchmark samples, or children. CPU/RAM peaks and elapsed wall time
were not measured; no explicit numerical wall budget was supplied. Whole
source inference, abnormal-state reuse, effects/protection, complete Call,
soundness, principality and production cutover are unverified. Future Value
payload variants, Value level changes, nongeneric metadata writers or
Effect-to-Value references invalidate the corresponding bounded observations.
At final source recheck, HEAD was
`0adb53649c5d47d262073b81abac1576a5b56687`; all named compiler/HIR dependency
diffs against the pinned baseline remained empty, and supplied note/decision
hashes remained unchanged from their recorded working-tree snapshots.

## Commit packet

- Exact leased path: `notes/progress/2026-10-11-source-qualified-value-parent-copy-scc.md`.
- Baseline: `330d5432aff4b1f9655d501e17a9eefb7e75e098`.
- Dependency changes: no compiler dependency changed. The accepted
  parent-copy decision differs from baseline at the hashes above; both
  supplied reference notes are frozen working-tree inputs. This leaf changed
  none of them.
- Review status: the initial compiler-referee BLOCKING finding was closed by
  a primary textual repair recasting every adjacency/cycle as operational
  bound-payload evidence and restoring source-Value ownership as the first OPEN
  premise. The same reviewer completed the narrow delta review with no residual
  finding. No source SCC witness or theorem closure is claimed.
- Checks run: bounded static owning-source reads/searches, source baseline
  diffs, dependency hashes, and artifact whitespace check; no execution.
- Proposed commit message: `research: trace recursive source bound-payload prefix`.
- Shared-record delta: link this as an operational prefix, not source SCC
  evidence; preserve source-Value ownership, scanner equivalence and parent/
  copy adequacy as OPEN. No authority or compiler file was edited.
