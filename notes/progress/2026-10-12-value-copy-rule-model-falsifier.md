# Value-copy incidences: creation cut and smallest conditional discriminator

Date: 2026-10-12
Status: frozen bounded source characterization and finite model calculation; independently reviewed, minor wording repair incorporated
Baseline: `c9c2581308586dbc87542629d7389de2d2c77156`, branch `research/simple-sub-intrusion`
Exclusive lease: this file only; complementary falsifier, no delegation
Parent qualification/equality, source correspondence, soundness and principality gates: OPEN

## Objective, authority and method

Compare only these two candidate rules for actual extrusion/freshening copies:

- **A:** a copy inherits its source owner's resolved Name incidences, with each
  target remaining the original resolved binder Value row.
- **B:** extrusion/freshening alone adds no Value-reference incidence. Only an
  explicit source construction can assign incidences to a new row.

Neither changes the original owner's incidences, native copy domain, polar
maps, fresh-use map, providers, source binding identities or selected equality.
These are candidate completions, not adopted semantics. The pending question
is an input describing the comparison, not an approved answer.

Governing authority is `2026-10-10-parent-copy-scc-intrusion.md`, **Selected
operation and compiler responsibility**, **Value-reference SCC clarification**,
**Apply-result source-fragment ownership**, **Nested Apply membership**,
**Definition-root Value ownership**, and **Retained boundary**;
`2026-10-08-source-generalize-definition.md`, §§2–5; and the top-level inference
principles §§1–5 and **Evaluation**. Apply/root Name edges and their actual
resolved binder targets are fixed. Comparisons, stored bounds, Function ports,
selected providers and parent metadata do not supply those edges. In
particular, the approved cross-level root cycle is `O→E→O`, independent of
the distinct actual pairs `(C,B,+,1)` and `(D,R,-,1)`.

Method: inspect the six assigned Rust constructor/consumer owners at the
baseline, use the frozen native derivations only within their stated scopes,
then perform one deterministic in-memory JavaScript calculation. This is
complementary falsification, not the constructive theorem lane or an
independent review. No compiler implementation/test change was authorized.

The older native-row bridge note's *unselected definition-root forwarding*
alternative is historical after the current approved definition-root clause.
This packet uses its allocation/source locators, not that earlier alternative.

## Actual source-owner facts

| Owner and lines | Inspected operation | Relevant boundary |
| --- | --- | --- |
| `candidate_source.rs:168–217,369–411` | Registers expression components, aliases formal Names to the actual formal endpoint, retains module/local Name actions and Apply callee/argument/result coordinates | No result-owned list of resolved Name incidences is constructed |
| `candidate_source.rs:307–329,445–495` | Installs unannotated locals from initializer endpoints; retains distinct Lambda/body and Block/final coordinates; forwards the formed body to the definition root by a typed Link | Typed links do not create the approved root incidence or a target at an extrusion copy |
| `local_source.rs:286–367,529–581,635–657` | Builds Lambda/formal scopes, nested initializers and publication; constructs Apply; resolves Names to Parameter/Local/ModuleDef identities | Name resolution retains actual lexical/module identities, not a polar copy choice |
| `shadow_apply.rs:1024–1037,1331–1383` | Allocates expression components and creates the four-port negative Apply demand with its actual result endpoint | Demand ports/providers are not source incidences |
| `candidate_extrusion.rs:5,90–163,224–249` | Memoizes by endpoint/polarity/target, allocates wrong-level rows, retains the parent before selected-bound copying, visits all four Function ports | No Value-reference incidence payload is copied; polarity does not select a new Name target |
| `candidate_scheme.rs:36–108,981–1020,1316–1382` | Captures typed rows/nodes/bounds/evidence, uses one canonical row remap, keeps nongeneric/low-level anchors, installs actual local roots | No source-incidence field or reference-closed capture domain; fresh use does not create extrusion-parent provenance in this allocation branch |
| `candidate_intrusion.rs:358–488` | Scans lower/upper payloads, Function ports and Effect dependencies, then compares components for actual retained parent/copy pairs | It does not consume an explicit approved Value-reference adjacency |

Thus current absence of incidence copying cannot certify B: the approved
original Apply/root incidences are themselves missing at these owners. The
existing SCC scanner also cannot be used as an oracle for either policy.

The inspected unannotated local installer stores the source initializer
endpoint as its root. Later local use links a reconstructed root to a distinct
Name facade. Neither operation inspected here registers an extrusion copy as
a separately resolved binder Value target. This is a bounded source fact, not
a universal claim about every annotated/foreign/later source path.

## Creation-cut finite combinatorial lemma

Let a finite original graph be `G=(V,E)`. An event creates fresh vertices `N`
disjoint from `V`. Keep every old incidence unchanged. Under A, add only edges
`n→b` with `n∈N` and `b∈V`, inherited from the copy's original owner. Under B,
add none. No explicit source constructor adds an incoming edge to `N` during
this cut, and no old edge is redirected.

**Conditional finite lemma:** A and B have identical SCC partitions: the SCCs
of G plus singleton SCCs for N. Neither qualifies any retained distinct pair
`(copy∈N,parent∈V)` at this cut.

Derivation: an original vertex reaching a new vertex would require a first
edge crossing from V to N. Neither policy supplies such an edge. A new vertex
can enter V but cannot return to N, and no edge joins two new vertices.
Original reachability therefore remains unchanged and every new SCC is a
singleton. Parent provenance alone cannot supply the missing crossing.

This lemma is about a supplied finite transition. It does not prove that
every source/copy event has these hypotheses or that qualification stays
unchanged after future source construction. Fresh use has no extrusion-parent
record merely because its row is new. If a future source rule assigns a copy
as the actual resolved binder target, its original-owner incoming incidences
are an additional operation outside this lemma.

## Assigned source shapes and exact maps

All Y3 claims below are static constructor characterization conditional on
successful recovery-free LocalSource formation and completed allocation/source
actions. No source string was executed. The original Simple-sub calculations
are those in the frozen notes, not complete Yulang Call/effect derivations.

| Shape | Fixed original source incidence | Actual native map premise | A/B difference |
| --- | --- | --- | --- |
| `my id x = x` | definition root `I→X`; body Parameter Name aliases X | One fresh-use canonical map, with I and X generic when captured above the boundary; original two-port identity reuses one `X_u` in both ports | A gives `I_u→X`; B gives none. No extrusion pair or SCC difference in this determined projection |
| `my konst x = 0` | No body Name incidence on K | Generic formal X can freshen; literal result stays ground; captured generic root K may freshen | Neither policy has an outgoing K incidence to add; no difference here |
| `konst 1` | Apply result `R→K`, regardless of returned literal provider | This simple same-level Call does not itself force an extrusion copy of R; copying R requires an additional actual event | If such an event copies R, A adds `R_copy→K`, B does not. No return path follows, and the additional event is unestablished here |
| Exact nested conditional/infix `odd/even` | Approved `O→E`, `E→O` across lexical levels | Exact ordinary HIR admission/generation remains unestablished in the frozen derivations | Root SCC is fixed in both; no copied-row history for that exact text is asserted |
| Call-bearing analogue `my odd n = { my even n = odd(n); even(n) }` | `O→E,A`; `E→O,B`; `R→O,B`; `S→E,A` | Actual polar prefix `m(B,+,1)=C`, `m(R,-,1)=D`; local-use map `μ(E)=E_u`, `μ(B)=B_u`, `μ(R)=R_u`, with C,D anchored at level 1 | A adds `D→O,B`, `E_u→O,B`, `R_u→O,B`; B adds none from copying. Adjacency differs; determined SCCs and pair qualification agree |

For the analogue, the two formals A/B are distinct despite identical spelling.
The extrusion map is signed; the local-use map is one shared unsigned
canonical map. A targets B, not C or B_u, and O, not a fresh root. Neither
policy widens either copy domain through source references. Copies of formal
B have no approved outgoing incidence in the determined projection. A's
six added edges consequently leave `{O,E}` as the sole nontrivial SCC and
leave both `(C,B)` and `(D,R)` unqualified in that projection.

Unknown Lambda/Block/wrapper incidences and later source actions are not
claimed absent from the complete graph. The finite calculation uses only
determined edges; it is not a proof of either pair's nonmembership in the
full source graph.

## Smallest conditional SCC/qualification discriminator

Use two distinct vertices p and c and retain `Parent(c,p,polarity,target)`.
Before copying, grant an actual original-owner self-reference `p→p`. At the
copy cut, A adds `c→p`; B does not. Later, grant a separately source-produced
incoming incidence `p→c`. The chronology avoids assuming an incoming edge
to a not-yet-allocated copy.

```text
A: p→p, c→p, p→c   SCC={p,c}; retained pair qualifies.
B: p→p,      p→c   SCC={p},{c}; retained pair does not qualify.
```

Two distinct vertices are minimal for distinct parent/copy qualification.
At the premise level, each of these changes destroys A's qualification:
remove the later incoming incidence; replace A with B; or remove the
pre-copy `p→p` source incidence and recompute A's inherited incidences, which
also removes `c→p`. These are premise-removal checks, not independent edge
deletions from the completed A graph: deleting only `p→p` after the other two
edges are present leaves the path `p→c→p`. The self-reference can be motivated
by a recursive definition's original Name occurrence, but the conjunction
with an actual extrusion parent and later `p→c` is not established by any
assigned source example.

**Exact missing Y3 owner:** a source binding/publication or other explicitly
approved incidence constructor must make c the actual binder Value row
targeted by a Name owned by p, while preserving c's distinct retained
extrusion provenance. The inspected unannotated local installation and Name
resolution do not do this. Merely mapping an old Name to c would contradict
its fixed original binder target unless that mapping has a separately approved
source identity correspondence. No currently supported incoming-copy rule is
asserted. The model is not a source-qualified counterexample to either policy
or to equality preservation.

## Calculation, reproducibility and oracle limits

One `functions.exec` JavaScript calculation computed reflexive transitive
closure by Floyd–Warshall, grouped vertices with mutual reachability, and
compared the supplied graphs. It did not invoke a shell/interpreter or write a
checker file. No random seed: complete masks `0..15` selected all four possible
edges among two old vertices; masks `0..3` selected later edges from either old
vertex into the one new copy of old vertex 0. The inheritance snapshot was
taken before the later incoming edges.

Results:

- 16 creation-cut graphs: zero A/B SCC differences; zero qualifying pairs.
- 64 graphs with the hypothetical later incoming edges: 30 SCC differences,
  26 differences in qualification of `(copy=2,parent=0)`.
- The two-vertex witness and each of three premise-removal/recomputation
  checks gave the outcomes above. They do not delete `p→p` from the completed
  A graph while retaining inherited `c→p`.
- The 15-vertex native analogue projection had 8 original and 6 inherited
  edges: A/B SCC partitions agreed; both actual retained pairs were false in
  both projections.

The graph input generation and relevant computation can be reproduced in any
JavaScript environment with this deterministic core (vertex 2 is the copy):

```javascript
function reach(n, edges) {
  const r = Array.from({length:n}, (_,i) =>
    Array.from({length:n}, (_,j) => i === j));
  for (const [a,b] of edges) r[a][b] = true;
  for (let k=0;k<n;k++) for (let i=0;i<n;i++) for (let j=0;j<n;j++)
    r[i][j] ||= r[i][k] && r[k][j];
  return r;
}
function partition(n, edges) {
  const r=reach(n,edges), seen=new Set(), out=[];
  for (let i=0;i<n;i++) if (!seen.has(i)) {
    const group=[];
    for (let j=0;j<n;j++) if (r[i][j] && r[j][i]) {
      group.push(j); seen.add(j);
    }
    out.push(group);
  }
  return JSON.stringify(out);
}
const universe=[[0,0],[0,1],[1,0],[1,1]];
let creationDifference=0, creationQualified=0, laterDifference=0, pairDifference=0;
for (let mask=0;mask<16;mask++) {
  const old=universe.filter((_,i) => mask>>i & 1);
  const copied=old.filter(([a]) => a===0).map(([,b]) => [2,b]);
  creationDifference += partition(3,old.concat(copied)) !== partition(3,old);
  const creation=reach(3,old.concat(copied));
  creationQualified += creation[0][2] && creation[2][0];
  for (let later=0;later<4;later++) {
    const incoming=[0,1].filter(i => later>>i & 1).map(i => [i,2]);
    const A=old.concat(copied,incoming), B=old.concat(incoming);
    laterDifference += partition(3,A) !== partition(3,B);
    const a=reach(3,A), b=reach(3,B);
    pairDifference += (a[0][2] && a[2][0]) !== (b[0][2] && b[2][0]);
  }
}
// Observed: 0, 0, 30, 26.
```

This calculation is independent of the Rust SCC implementation, but both
candidate graphs share supplied source incidences, chronology and copy rules.
It validates finite consequences of those assumptions, not source generation,
Call semantics, typing soundness, or a new transport rule. No Oracle, second
source-semantics implementation, Scala execution or authentic source-history
oracle was used. Failure conditions include any unmodeled incoming incidence,
redirection/canonicalization, different source owner, different copy domain,
or failure of the retained-parent/source-identity premises. Enumerated counts
are exhaustive only for the stated tiny envelope.

## Conclusion and next action

The assigned constructor facts and approved original incidences force neither
A nor B. Generalize fixes actual bindings/providers, per-instance description
frames and monomorphic alias sharing; those commitments do not specify whether
a new description row owns source incidences. A retains original binder targets;
B leaves original-owner incidences intact. No contradiction with those approved
commitments was established for either candidate. Their agreement at a creation
cut does not establish equality safety or make the choice immaterial.

The decisive unresolved premise is the copied-row incidence rule and the
independent source producer of an incoming path to an actual extrusion copy.
Another equivalent graph probe cannot establish it. Correct qualification
remains A/B under the obligation-economy rules; reconstructing Name identity
from bounds remains D. This finite envelope supplies no source-supported
SCC/qualification discriminator and leaves all original parent gates OPEN.

Recommended next action: the primary adjudicates the pending copy-content
choice against the approved source construction, obtains its required scoped
decision if no existing authority fixes it, and assigns the exact binding/
incidence owner correspondence before using a copied-row SCC to justify
equality. The incoming-copy premise stays separately OPEN.

## Checks, resources and frozen dependencies

Checks already run: bounded `cat`, `rg`, `sed`, `tail`; read-only baseline and
branch inspection; `git diff --name-only BASE --` for the twelve tracked direct
semantic/source inputs (empty); SHA-256 capture; one finite in-memory graph
calculation. No Cargo, compiler/test invocation, broad search, Oracle run,
benchmark, Git mutation, child, shared-record change or production edit.
Budget: ≤30 minutes, one graph calculation, zero heavyweight processes. Static
reads used at most two lightweight processes at once. CPU/RSS and complete
reasoning wall time were not instrumented; no resource peak is claimed.

Unverified: exact conditional/infix source admission; full completed Call and
effect processing; annotated/foreign constructor paths; rollback/replay
incidence transport; arbitrary source/use histories; actual incoming-copy
incidence; equality safety; soundness/principality; public inference and cutover.

Direct dependency SHA-256 snapshot (all twelve tracked files matched the pinned
baseline; pending question is separately hashed and is not authority):

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `fd07ecc76e9df0b1937f72e74ce4a35b982b51031b04022672228e307d03615c` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/theory/2026-10-12-value-reference-transport-proof.md` | `9cb143d542d9b79f4c5762e3392a6daeb94cbd71020817524e990aeb426ad0b4` |
| `notes/theory/2026-10-12-odd-even-parent-copy-scc-derivation.md` | `238e21c0a027aa9f0ca14c563c3fbaa11188ee268e8b819a049f81dd6afd5830` |
| `notes/theory/2026-10-12-odd-even-native-value-row-bridge-proof.md` | `3812f87e7d0a83dcc6d65470a8274bdcb6d6c79f3f0655840c835d01a7802fc6` |
| `questions/2026-10-12-value-reference-copy-content-owner/question.md` | `c0eafaf39e9ae034fef68f06eacc9bfce6b71c4b55fa0c32892d826606d406b1` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/shadow_apply.rs` | `cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |

## Commit packet

Exact leased/changed path:
`notes/progress/2026-10-12-value-copy-rule-model-falsifier.md`.
Baseline: `c9c2581308586dbc87542629d7389de2d2c77156`.
Changed dependency hashes: none at this snapshot. Review status: independent
`compiler_referee` found no blocking or major issue and one minor
minimality-wording finding, repaired above by distinguishing premise
removal/recomputation from deleting a final graph edge. This remains a
research-only finite characterization/conditional discriminator; no theorem
closure, production conformance or implementation authority. Checks already
run: source reads, baseline/hash comparison, one finite graph calculation;
no compiler tests/builds. Proposed research-checkpoint commit message:
`research: compare Value-copy incidences at creation and incoming-reference cuts`.
Shared-record deltas intentionally left for the primary/curator: record
creation-cut SCC agreement separately from adjacency differences; keep the
later incoming-copy source owner and actual pair qualification OPEN; record
that neither candidate is forced/refuted by the assigned constructor corpus.
No shared record or question bundle was edited. Writes stop at submission.
