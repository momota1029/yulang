# Value-reference graph: constructor and transport falsification

Status: frozen research-only source audit and conditional transport obstruction; unreviewed
Parent Value-reference / retained-parent-copy SCC gate: OPEN
Baseline: `0af7aa73f17841d01df0cff0b13e42b2eef6a114`, `research/simple-sub-intrusion`
Exclusive lease: this file; leaf, no delegation

## Objective, authority and result

Attack a direct mathematical owner/reference graph at native constructors and
transport owners, without deriving semantic edges from comparisons or storage.
The original theorem still ranges over every supported source program, every
actual inference history, and every retained distinct Value extrusion pair.
The required graph has Value variables as vertices; `u -> v` means that the
value owned by `u` references `v`. Parent/copy equality requires mutual
reachability before that equality. Cross-family references remain allowed;
Effect references use a separate relation.

Governing sections: `2026-10-10-parent-copy-scc-intrusion.md`, **Selected operation
and compiler responsibility**, **Value-reference SCC clarification**, **Retained
boundary**; `2026-10-11-yulang-inference-top-level-principles.md` §§1–5 and
**Evaluation**; `rules/design-authority.md`, **Authority order**; and
`rules/compiler-engineering.md`, **Natural compiler behavior and proof-obligation
economy** and **Deterministic Simple-sub inference**. The source-reference repair
draft supplies candidate notation, not authority to identify the mathematical
graph with a source-syntax-only graph.

Result: no genuine counterexample to the approved graph or intrusion operation
was established. Two shortcuts are discriminated: source Name incidence does
not identify all native Function ports, and native polarized extrusion cannot
in general be transported by one uniform unpolarized row renaming. The decisive
OPEN premise is the mathematical owner law for formal/occurrence rows and bound
Lambda argument/result ports. The governing definition does not by itself
establish whether those ports are references in the owning value. This audit
does not choose the answer.

The frozen owner-introduction and mutual-Name bridge already establish an
original-root source SCC and a retained joint Name route certificate. Their
module-Name SCC enumeration is not repeated here. Their unresolved native
Name/Lambda interpretation remains unresolved.

## 1. Minimal formal-parameter discriminator

Compare the two source constructors:

```yulang
my ignore x = 0
```

```yulang
my id x = x
```

Hypotheses for this bounded crosswalk: successful source formation and ordinary
native Lambda admission, distinct original raw rows, and no intervening equality
or formal annotation. No runtime execution, acceptance test or extrusion
reachability is assumed.

HIR creates a Lambda for the parameter and resolves the second source's body
Name to that parameter (`yu-hir/src/module/local_source.rs:286–317,636–657`).
In the source-syntax-only owned-body walk, `ignore` has no Name reference to
`x`; `id` has one, owned by its Lambda/binding rather than by the parameter.
This is a fact about that source walk, not a determination of the mathematical
Value graph's entire adjacency.

The native constructor allocates an expression component even for a parameter
Name, but uses `CandidateEndpoint::Parameter` as its computation endpoint
(`candidate_source.rs:187–201,209–217`). Let `P` be the formal Value row.
`admit_lambda_fact` always reads `P` as its argument port
(`lib.rs:11233–11246`). For `ignore`, its result is the literal component `I`;
for `id`, its result is that same `P` with positive polarity
(`lib.rs:11247–11260`). Both introductions form the complete four-port positive
Function (`lib.rs:11342–11362`):

```text
ignore: Function+(P-, entry-, return+, I+)
id:     Function+(P-, entry-, return+, P+).
```

Therefore the candidate shortcut “the original owner's source Name targets
are exactly all Value ports of its native Function” fails already at the
unused-parameter Lambda: its argument port exists with no such Name occurrence.
This refutes that equivalence, not a mathematical interpretation in which
bound Function ports themselves are justified owned references. Whether such
an interpretation is the approved relation is precisely the missing premise.

For `id`, aliasing the Name endpoint to `P` does not establish `P -> P`.
The source reference has the Lambda as its source owner; the incoming formal
has no owned initializer in these records. Assigning `C(P)=Ref(P)` just because
the Name endpoint is `P` would assume the owner law being investigated. The
allocated but bypassed occurrence component also needs an explicit scope rule
if the interpretation is claimed on all allocated Value identities.

This is a distinct obstruction from the prior mutual module-Name identity seam:
perfect resolution and route provenance cannot decide the meaning of a formal
whose row serves both parameter and body-result typing roles.

## 2. Conditional obstruction to uniform copy transport

Consider the actual positive Function shape introduced for `id`, and invoke
native positive extrusion at target level `t`, under these explicit guards:
`level(P)>t`; successful allocations and the whole operation; the same original
canonical `P` on both ports; and no intervening equality of new copies.
This is a conditional operational derivation. The displayed top-level source
alone does not establish that this invocation occurs in an actual history.

`candidate_extrusion.rs:4–5,73–94` keys the operation by endpoint, polarity and
target level. Its Function case traverses the argument at opposite polarity
and the result at the original polarity (`:224–249`). The two visits are thus

```text
(P, Negative, t) -> Cminus
(P, Positive, t) -> Cplus.
```

Because the keys differ and `level(P)>t`, each visit allocates a fresh row and
retains its actual parent (`:95–123`). Under the stated no-equality guard,
`Cminus != Cplus`. Rebuilding the Function uses those mapped ports separately
(`:325–350`). Hence no single function `tau` on unpolarized original rows can
both reproduce that native output by `tau(P)=Cminus` on the argument and
`tau(P)=Cplus` on the result.

The falsified candidate premise is uniform port transport, not the existence of
an owned-reference transport law. A valid law may require the justified
constructor/port context already used by extrusion. The source Name `x` alone
does not determine which copied port owns its mathematical reference. Copying
selected upper/lower bounds or recording parents supplies no answer by itself.
No semantic edge, parent/copy SCC or equality necessity is inferred here.

Failure conditions for this discriminator: `level(P)<=t` shares the original;
distinct input canonical rows remove the common-parent premise; intervening
equality removes distinctness; a graph interpretation that never identifies
its reference transport with both Function ports is outside the shortcut.

## 3. Other constructors and consumers: bounded coverage

| Owner/path | Actual evidence | Remaining owner/reference premise |
| --- | --- | --- |
| Module Name / recursion | Frozen mutual-Name bridge retains owner, target, occurrence and completed route together | Does not establish whether occurrence row owns a reference or represents the target's obtained value/type; no repetition of the established SCC result |
| Forming local initializer | `candidate_source.rs:300–305,380–390` keeps the open initializer endpoint and links a self-use to its Name component | Local Name link is a typing admission; its owner construction must be stated independently |
| Block / initializer | Separate initializer/install scheduling and final expression (`candidate_source.rs:288–336,461–469`; `local_source.rs:795–827`) | Block containment does not establish outgoing owned references; each initializer owner and final-value forwarding need their own interpretation |
| Apply | Callee, argument and result endpoints are retained; `shadow_apply.rs:1331–1383` constructs a negative Function demand | Demand comes from the use site. Its argument/result ports do not by themselves identify references owned by the callee or application result |
| Generalization / local use | Local scheme retains `(id,root,boundary)`; use captures graph then prepares fresh map (`candidate_scheme.rs:1316–1335,1362–1378`) | Captured graph is rows, leaves, bounds, effect operands and polarized Functions (`:36–108`); transport of that typing graph is not yet transport of the approved reference graph |
| Shared captures / levels | Capture marks generic rows using levels/metadata (`candidate_scheme.rs:301–325`); fresh use jointly remaps canonical rows and shares nongeneric/outside rows (`:1008–1019`) | Exact sharing/copying rule is available, but semantic reference endpoints must be supplied before its adequacy can be proved |
| Function variance / effects | Extrusion reverses argument Value/Effect polarity and preserves result Value/Effect polarity (`candidate_extrusion.rs:224–249`) | Variance is a typing transport rule, not reference direction. Effect ports cannot silently become Value-reference paths |
| Intrusion consumer | `candidate_intrusion.rs:390–468` visits stored row bounds and positive/negative Function ports; pair comparison is at `:477–486` | Scanner relation needs a constructor-derived correspondence to the approved relation before pair qualification can be justified |

These locators identify actual producer/consumer responsibilities; the table
does not claim exhaustive source coverage or a failure in an executed history.
The selected same-SCC parent/copy equality aligns with the design text. The
missing correspondence concerns its antecedent graph, not permission to remove
or weaken that equality. The consumer's current mixed endpoint traversal does
not itself establish the separate Value/Effect interpretation required here.

## 4. Evidence limits, checks and next action

Method: one static constructor/transport attack. No executable checker, Oracle,
instrumentation, build or test was run. There is consequently no independent
execution oracle, seed/range, mutation campaign or bounded enumeration claim.
Source syntax and native crosswalk share the pinned HIR/name-resolution
assumptions. The copy obstruction is derived from actual source code under its
explicit invocation guards; it is not a toy checker assuming transition rules.

Commands: bounded `cat`, `rg`, `nl -ba`/`sed`, `sha256sum`; read-only
`git rev-parse HEAD`, `git branch --show-current`, `git status --short`, and
`git diff 0af7aa73f17841d01df0cff0b13e42b2eef6a114 -- <exact dependencies>`.
The dependency diff was empty. Initial combined captures truncated; decisive
rules and constructors were reread in bounded captures. No Git mutation,
shared-record write, compiler/test edit, external contact or child spawn.
Up to five lightweight read commands were batched; actual process overlap was
not measured. Zero heavy/probe processes and zero measurement samples ran.
CPU, RSS and reasoning wall time were not
measured. The packet supplied no numeric resource bound; work stopped after
this precise obstruction. Runtime model/effort metadata is unavailable.

No dependency was changed. The pinned dependency snapshot is unchanged from
the baseline; the two prior frozen artifacts have SHA-256 respectively
`f9c9d648d2bcfb91e97c2549c06819608860a73e0b59831695347be691946943` and
`9f83f10566b11861a8b8079efff3bcb7dabd153287583d00e6ba71e50c988caa`.

Unverified: authentic source arrival at the conditional extrusion invocation,
native owned-value semantics for all rows, copy/reference transport, recursive
pair reachability, scanner equivalence, complete Call, soundness, principality,
Effect hygiene and production cutover. This producer supplies complementary
falsification evidence and does not independently certify its own output.

Recommended next action: give the constructive owner lane the formal/Lambda
case above and require an explicit mathematical law deciding which bound
argument/result ports are references in the owned value, how parameter Name
aliasing respects that law, and how its port context survives polarized
extrusion. Apply that law to the existing Name certificate and consumer; another
source-syntax walk or payload SCC count would leave this premise untouched.

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-11-value-reference-graph-independent-falsification.md`.
- Baseline SHA: `0af7aa73f17841d01df0cff0b13e42b2eef6a114`.
- Changed dependency hashes: none; inspected production and frozen dependencies match the baseline.
- Claim/review: unreviewed bounded source discrimination and conditional operational obstruction; parent gate OPEN; writes stopped before submission.
- Checks already run: static constructor/consumer reads, baseline/branch/status, exact dependency diff, SHA-256 snapshot and note inspection. No tests/builds.
- Proposed checkpoint message: `research: audit Value owner ports and polarized reference transport`.
- Shared-record deltas left to primary/curator: record the formal/Lambda owner law as the decisive OPEN premise; reject only syntax/port equivalence and uniform port-renaming shortcuts under their explicit premises; preserve the approved graph meaning, original theorem scope and all existing parent gates.
