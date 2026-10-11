# Value parent/copy reachability: native construction obstruction

Date: 2026-10-11
Status: independently reviewed bounded operational derivation; original
source/inference parent obligation remains OPEN.
Compiler baseline: `330d5432aff4b1f9655d501e17a9eefb7e75e098`.
Simple-sub reference: `9bae772624c23b52a93c1b226157e16898b4d9db`.
Exclusive lease: this note only. Leaf; no delegation, compiler edits, tests,
builds, executable probes, Oracle runs, or Git mutations.

## 1. Frozen question, quantifiers, and claim classes

The assigned question is whether **some authentic supported Yulang source
construction makes a distinct retained Value extrusion parent/copy pair share
an SCC of actual Value references**. Keep the source's scopes, lexical binders,
occurrences, annotation coordinates, extrusion polarity, parent identity, and
target level fixed. Comparisons and parent metadata are not reference edges.
No extra source restriction, mandatory annotation, early solving rule, or
independent choice of a witness/port is permitted.

There are two different bridges:

1. **Operational bridge O:** the actual native source actions, accumulation,
   extrusion and fresh restoration emit the payload references scanned by
   `settle_candidate_intrusion`, preserving the rank below.
2. **Semantic bridge S:** those emitted payloads account for every Value
   reference and inference dependency required by the supported source meaning,
   including all subsequent consumers. O does not imply S.

This note constructs O for the enumerated current native Value mutation owners
and derives their nonreachability consequence. A compiler-referee review found
no flaw in this bounded derivation and kept S as the semantic blocker.
It refutes candidate *histories* needing an upward reference at those owners.
It gives no authentic qualifying source witness. The original source/inference
question retains its OPEN status because S and the required ordinary-inference
conclusion have not been established. This is neither a normality/redundancy
theorem nor a counterexample to the user's selected intrusion operation.

The precise operational statement is:

> For every finite authentic native history beginning at `try_new_candidate`,
> with original source identities and actual actions, after completed Value
> insertions/extrusion/restoration steps and before the first hypothetical Value
> merge, every installed bound satisfies R. Every retained Value extrusion
> event `(copy,parent,polarity,target)` satisfies P. Consequently no such
> distinct event pair qualifies in the scanned Value-reference graph, and
> there is no first Value parent/copy merge on those histories.

Authentic means the current collection, source scheduler, lexical resolution,
module SCC routing and native candidate consumers produce the operations; it
does not mean a graph installed through test helpers. Type-error continuation
is included when these operations return normally. Suspension adds no hidden
reference: completed retained steps and the next executed step are covered.
No assertion is made about reuse of a failed half-completed private operation
without its owning invariant or restoration. New producers, mixed legacy
sessions, arbitrary API-injected graphs, and semantics/publication/Call/hygiene/
principality closure are outside this operational derivation.

Method: a constructor induction and first-merge contradiction, followed by
earliest-constructor analysis of attempted reverse paths. No checker assumes
or simulates the transitions.

## 2. Authority and exact owning sources

The primary's user-selected graph controls: vertices are Value variables;
edges are actual references in their values. Parent-to-child and nephew-to-uncle
references are admissible shapes. The Authority is
`notes/design/2026-10-10-parent-copy-scc-intrusion.md`, “Direct decision”,
“Selected operation and compiler responsibility”, “Value-reference SCC
clarification”, and “Retained boundary”; and
`notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§1–5,
“Evaluation”, and “Authority and integration”. Workflow scope is governed by
`rules/design-authority.md` “Authority order” and “Natural compiler behavior
and proof-obligation economy”; `rules/compiler-engineering.md` of the same
section name and “Deterministic Simple-sub inference”; `rules/research-lab.md`
“One semantic baseline, explicit dependency invalidation”, “Evidence quality
and stopping unproductive loops”, and “Writes, artifacts and review snapshots”;
`rules/git-concurrency.md` “Disjoint-file mode”; and
`rules/agent-orchestration.md` “Proof delegation and decomposition” and “Model
routing and Astra escalation”.

Inputs are the primary-designated reviewed reference note
`2026-10-11-simple-sub-value-reference-scc.md`, native map
`2026-10-11-native-value-reference-scc-map.md`, and previous rank derivation
`2026-10-11-local-restoration-value-scc-preservation.md`. Their headers are
historical producer status; this producer does not independently certify them.
The rank proof's compiler hashes match this packet's source. The updated
parent-copy decision includes the accepted Value-reference clarification;
its current hash differs from the earlier rank note's recorded decision hash.
No old comparison-graph premise is imported.

All Rust locators below are relative to `crates/yu-solver/src/` unless named.

| Responsibility | Actual owner | Evidence used |
| --- | --- | --- |
| Value variable payload | `lib.rs:734`, `:3968` | Value endpoints are rows, Functions or leaves; four lists retain both bound sides |
| Function payload | `term.rs:196`, `:1126–1165` | Immutable argument/result Value handles, two Effect handles, validated sorts/polarities |
| Physical Value insertion | `candidate_extrusion.rs:406–507` | Selected list append; comparison alone creates no edge |
| Extrusion event and copied payload | `candidate_extrusion.rs:83–156`, `:308–355`; `candidate_intrusion.rs:171–222` | Strictly lower fresh row, actual parent record, source link, recursively rebuilt selected bounds |
| Ordinary admission/replay | `lib.rs:12320–12500`, `:13744–13759`; `candidate_extrusion.rs:808–832` | Native dispatch, level-selected row owner, structural extrusion before application |
| Source Lambda/signature | `lib.rs:11233–11362`; `candidate_effect.rs:1355–1443` | Actual Value ports precede their ordinary comparisons |
| Capture/fresh restoration | `candidate_scheme.rs:300–326`, `:569–621`, `:1008–1019`, `:1109–1157`, `:1227–1266` | Local owner capture, one joint row remap, same physical side restored |
| Lexical level/use | `candidate_source.rs:251–326`, `:375–388`, `:532–541`; `crates/yu-hir/src/module/local_source.rs:366–373`, `:396–437`, `:637–647`, `:819–829` | Containing-boundary ownership and descendant use level |
| Internal/module use | `candidate_scheme.rs:843–918`, `:952–974`; `lib.rs:15765–15785` | Open-root links before capture; published module boundary zero |
| SCC qualifier/equality | `candidate_intrusion.rs:391–468`, `:477–490`, `:545–593` | Reference traversal, actual event qualification, representative/level merge |

The reference's actual independent storage owner is
`/home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala:106–159,166–185,209–227`.
It has both bound lists and Function/Record references, but neither retained
extrusion-parent records nor the selected intrusion consumer. It is an
independent source for storage/copy behavior, not an oracle for Yulang semantics.

### Concrete represented values and their contained references

Define the **represented payload** V(v) by the actual Value variable object,
not by the orientation of a comparison: `InferenceSession::bounds[v]` owns
four arrays of Value endpoints. A row endpoint is a reference to another
session variable object; a Function endpoint is a reference to an immutable
`TermNode` whose argument/result fields contain further Value handles. A leaf
contains none. Let `occ` collect those contained Value handles through immutable
Function syntax, stopping at each row. Then the literal payload edge is

```text
v →payload w iff some endpoint physically contained in V(v) has w in occ.
```

This ownership has a separate construction/consumer bridge. Source component
and live-variable handles resolve to exactly those session row objects
(`lib.rs:11382–11411`); source Lambda builds its Function using the actual
parameter/body handles (`:11233–11342`). The Function term constructor stores
these fields without reversing the argument reference (`term.rs:1126–1165`).
Scheme capture independently exposes a Value handle as `Endpoint::Value`,
then `Node::Row`, and a Function as `Node::Function` with contained children
(`candidate_scheme.rs:330–407,420–493`). `expand_row` reads the owning payload
and captures both lists while preserving the bound's owner and side
(`:569–621`). Fresh reconstruction remaps the resulting row/Function handles
jointly, and `begin_candidate_fresh_bound` chooses the captured owner before
installing the mapped endpoint (`:1008–1019,1127–1157,1227–1266`). It therefore
restores contained-handle references rather than inferring them from an
inequality. Copying changes the referenced object according to that same
explicit remap; it is not an inverse semantic guess from a stored constraint.

Only after deriving this represented payload relation does comparison dispatch
determine **which object's payload changes**. Consequently R follows from the
actual owner and actual contained rows, not from declaring that a judgment
`a<:b` is an edge. This proves correspondence with literal retained Value
payload references. Whether this is a complete representation of the user's
required source values is exactly S, still OPEN; a field inventory cannot
decide that semantic premise by itself. If the required Value representation
includes another source-owned reference outside these payloads, this operational
exclusion does not apply to it until its producer/consumer bridge is supplied.

## 3. Constructor preservation and the all-writer premise

For a live Value row let L be its level. Define H(row)=L(row), H(leaf)=0,
and H(Function)=max(H(argument Value),H(result Value)). Structural recursion
ends at row occurrences, whose bounds are a separate graph edge. Immutable
Function syntax is a DAG. Both Effect ports still participate in construction,
transport and Call; this numeric measure does not erase them.

The installed-bound premise and the actual extrusion-event premise are:

```text
R: H(item) <= L(owner), on either installed Value-bound side.
P: L(copy) = target < L(parent), for each retained Value extrusion event.
```

The exhaustive *native installed-bound* bridge has these cases:

1. Initial/allocated rows have empty bounds and `non_generic=false`
   (`lib.rs:10052–10103,10156–10176`). Source levels initialize before fact
   admission. This establishes R vacuously, without constraining which source
   binder/annotation may occur.
2. Row/row native application stores the lower-level row on the higher-level
   owner (`candidate_extrusion.rs:815–824`). Equal levels are permitted; only
   one selected bound side is inserted. Replay-generated comparisons use this
   same owner. R follows directly.
3. Row/Function application first extrudes the structural endpoint to the
   receiving row's level (`lib.rs:12412–12454`). The original unextruded
   bound is not inserted when it changes: the rewritten comparison is queued.
   Function/Function comparison decomposes ports and introduces no new bound
   by itself. Leaves are rank zero; duplicate, incompatible-shape and
   Bottom/Top branches install no offending Value reference.
4. In extrusion, a visited row at level at most T is returned unchanged;
   otherwise it is copied to T and memoized before selected-bound traversal.
   A returned row therefore has H at most T. Function reconstruction uses the
   returned Value ports; hence its H is at most T. Deferred `Work::Bound`
   inserts only that reconstructed endpoint into a copy at T. This proves R
   for both polarities and cycles through row bounds. The original-to-copy
   source insertion preserves R and the retention check establishes P.
5. Fresh restoration captures bounds only from local owners: `expand_row`
   returns for shared rows. There is no native production setter making a
   Value row nongeneric; initialization, rollback restoration and merge OR
   are the relevant metadata writes. Before a first Value merge the flag stays
   false. Therefore every shared Value row in a captured graph has level at
   most boundary B, and every captured owner is local. Module B=0. Lexical
   Local uses have U>=B because publication remains within the containing
   Block, its descendants, or the actual open-initializer link. Fresh mapping
   gives each local owner level U, each local reference level U and each shared
   reference level at most B<=U. Function reconstruction uses one joint remap.
   Restoring the captured side directly thus preserves R, even without any
   replay child and in the actual interleaved bound order.
6. A Value parent/copy merge is the remaining production Value-bound writer
   and the only native post-initialization Value level/representative change.
   Exclude its first occurrence below; do not assume its preservation in order
   to exclude it. Effect merges alter Effect representatives and may invalidate
   processing generations, but do not change Value levels or Value ports.

The caller search identifies no further native Value list writer. Signature
construction's direct insertions are Effect-only; Value signatures allocate
rows/Functions and emit comparisons. Context-bound maps and F5c draft bounds
are different payloads, not writes to `InferenceSession::bounds`.
The legacy direct-list append and destructive row aging in `lib.rs:11535,
13806–13953` are bypassed by native dispatch at `:12459` and `:13748–13750`.
Test-only injections are not authenticated source operations. These exclusions
come from actual branch/caller ownership, not a new language support rule.

Source actions cover literals, operations, parameters, groups, ascriptions,
Lambda, Apply, Local install/use/annotation, recursive open links and module
uses (`candidate_source.rs:329–460,649–681`). Each either makes no Value bound
or enters one of cases 2–5. This is sufficient to transfer R to *emitted*
native histories regardless of the particular source-level levels used by
ordinary comparison constructors. The lexical argument is needed specifically
where restoration inserts the captured physical side without reorienting it.

Saved-count restoration and its zero-product retirement do not evade this
proof: insertion already obeys R (`candidate_extrusion.rs:673–677,715–719`);
any later executed Value child returns through cases 2–4 (`:736–760`). Stored
constraints do not prove that all expected consequences execute. Complete
replay/activation remains a separate consumer obligation.

Rollback restoring a proved prior prefix preserves R by restoring its rows,
levels and metadata together (`lib.rs:9450–9464`). No full abnormal restoration
contract is assumed. A failed operation's un-restored intermediate state is
outside the stated history claim, not permission to publish or reuse it.

## 4. Reference paths and exclusion of the first qualifying pair

An actual direct bound gives owner→referenced row. A structural bound gives
owner→Function→contained Value row, including the outward argument reference
whose *comparison* polarity is reversed. Thus R implies that every segment
between consecutive Value-row visits has nonincreasing level.

The current SCC graph subdivides those variable-only reference edges with
Function nodes. Subdivision preserves mutual reachability of Value rows.
Its Effect-only branches have no edge back to Value; entering one cannot
manufacture a Value return path. The native map's endpoint/port analysis
applies to this frozen representation, not to future payload variants.

Assume a first qualifying Value merge. Earlier native steps preserve R by §3;
before this first merge no Value representative or level has changed after
initialization. Every retained event therefore still satisfies P. Qualification
requires a path copy→…→parent, hence L(parent)<=L(copy). P says the opposite.
Contradiction. A hypothetical earliest SCC qualification already gives the
same contradiction, independently of whether a dirty scan has run yet.

This is a constructor proof of an operational exclusion, not a successful
execution, independent review, or proof that the graph accounts for all required
source meaning. Parent provenance does not become adjacency to escape it.

## 5. Earliest constructor obstructing attempted histories

Fix an actual retained event C=copy(P,p,T), with L(C)=T<L(P).

| Attempted needed reference | Earliest actual obstruction | Actual reference/result |
| --- | --- | --- |
| Add C→P by comparing C<:P | `candidate_apply_value:815–824` chooses P as physical lower-bound owner | P→C; the comparison does not reverse storage |
| Add C→P by comparing P<:C | Same owner selection, opposite stored side | P→C again |
| Store Function(...,P,...) on C, at either Value port/polarity | `dispatch_live_item`, `lib.rs:12412–12454`, before insertion | P is visited above target T and replaced by the real polarity-specific P copy; the stored Function refers to that returned copy, not P |
| Recover P inside a selected bound copied into C | `candidate_extrude` row visit at `:83–124` | Every visited row above T is mapped to a copy at T; every preserved row is at most T |
| Freshen P and C to equal use level and retain the old parent event for them | `prepare_candidate_fresh_use:1008–1019` allocates fresh-use rows without `retain_extrusion_parent` | Sharing/cycles can be copied jointly, but the original event still names the original rows; no fresh event is fabricated |
| Restore an unchanged higher P into owner C through a shared capture | Capture classification plus use level, `candidate_scheme:300–326,569–570,1008–1019` | A retained shared P has level at most B<=U; a local captured P is remapped to U, as is the restored local owner |

For paths with more rows, some segment would have to ascend above T; the same
rank exclusion applies to that segment's owning constructor. Merely appending
`C.lower=[P]` in a synthetic state skips precisely the actual owner/rewriting
step being tested. It is a discriminator, not an authentic source history.

The reference trace's P(2), C(1), U(0), N(0) has genuine U→N→U references,
including N's stored Record field U. It satisfies R. Its event pairs P/C,
P/U and C/N each remain strictly ordered; SCC {U,N} contains none of those
pairs. Native Functions can likewise contain references to shared rows at an
allowed level, and a copied nephew can reference a low-enough uncle. Raw
family SCCs and structural self recursion therefore are not ruled out by R.
The reference trace is not a parsed Yulang witness, and its Record is not a
native Value constructor. Replacing its Record by an assumed Function does
not authenticate the missing source emissions or create a qualifying pair.

### Concrete source rule: local function returning its own binding

Consider the supported source form

```text
my outer = { my f x = f; f }
```

This is a constructor derivation; this packet has not parsed or executed it.
It uses the existing parameterized-local self rule, not an added source
restriction. HIR `Work::Initializer` publishes the temporary self identity
before the function body and restores it before ordinary publication
(`crates/yu-hir/src/module/local_source.rs:320–373`). The source scheduler
visits the containing Block at level 1 and the f initializer at level 2. Let
P be that initializer's Lambda root, X its formal Value row and N its body
Name occurrence row. All have level 2. The original f binder is fixed.

The Name's actual constructor sees the active initializer and emits
`Action::Link { endpoint:P, target:N }`, not a fresh-use operation or an
extrusion (`candidate_source.rs:302–305,381–385`). Its execution calls the
ordinary link admission (`:657–661`, `candidate_scheme.rs:1338–1345`). Native
row/row application stores N in **P's** upper payload: the literal represented
reference is P→N. No parent record is created by that constructor. In
particular N is not an extrusion copy C of P. Treating source occurrence
coordinates as extrusion children is the earliest unauthenticated step in
that candidate history.

The later Lambda constructor builds the actual Function
`F(X,argument_effect,result_effect,N)` and admits `F<:P`
(`lib.rs:11233–11362`). Its Value ports have level 2; structural extrusion
returns them unchanged at target 2 and inserts F into P's lower payload.
Thus P's represented value actually contains X and N through F. Opposite-bound
replay then explicitly generates `F<:N` from the retained upper N
(`candidate_extrusion.rs:764–805`); child generation/activation is owned by
`candidate_context.rs:2911–2991,3011–3041`. The generated child, when its
ordinary drain completes, stores F in N's lower payload. That gives a real
structural self-reference N→N, with no extrusion parent event. The initial
P→N and P→F→N references are established by physical constructor steps
regardless of using that later activation consequence.

After local publication, the final f occurrence uses `Action::Local`, boundary
1 and use level 1. Capture classifies P,X,N as local, maps all three jointly
to fresh rows P',X',N' at 1, and rebuilds F with those actual handles. The
recursive occurrence inside the captured Function therefore points to N',
not the old P or old N. This route preserves the represented recursive shape
and the original binder's use independence; it makes no retained extrusion
event for P'/P or N'/N. It does not supply a qualifying parent/copy SCC.

For this specific attempted history, the absent `C→P` is a correctly absent
**literal payload edge**: its proposed C is an occurrence/fresh-use coordinate,
not the recorded child of an extrusion. The source self dependency is emitted
by the open link and actual Function result port. It is not lost by dropping
a parent-reference field at that constructor. This local statement does not
prove that every source rule or every real extrusion correctly represents its
required semantic dependencies; the universal S premise remains unresolved.

## 6. Exact missing premise and proof-obligation economy

The rank argument does **not** identify a semantically missing constructor.
No source-qualified required reference conflicting with R has been established
here. Absence of qualifying SCCs alone cannot distinguish these possibilities:
the selected conditional operation has no current qualifying Value input; a
required source dependency was omitted earlier; or another open semantic/
consumer premise invalidates using this operational result for inference.
Adjudication must use an actual source-owned dependency, not family diagrams.

The exact remaining premise is S: for every supported source constructor and
its original binder/occurrence, show that the emitted native constraints,
copied/restored payloads and activated consumers represent its required Value
references and joint inference meaning. A concrete falsifier is a supported
source with a required retained parent occurrence whose earliest emission or
restoration replaces/omits it without the governing semantics licensing that
change. This note identifies the operations to inspect if such a source is
supplied; it does not invent that semantic requirement or certify extrusion's
approximation as adequate.

The previous conditional rank proof and the independent reference-family trace
already attack different aspects of the question. Another synthetic reverse
edge or rank restatement cannot settle S. Under the economy audit, the decisive
missing premise is class A/B insofar as required for source correctness or
ordinary inference. Arbitrary API graph/family characterization is class C
unless separately required. Current parent events and capture sides already
retain canonical construction facts; reconstructing parent identity from equal
levels would introduce class D debt and would be wrong. No class is relabeled
to close a gate, and no new certificate/semantic layer is proposed.

Next action: for the remaining parent gate, a bounded source/consumer packet
must fix the **required source dependency** to be represented at the
structural-extrusion or fresh-use owner. Preserve complete Call,
effects/hygiene, attachment/provider identities, witness correlation, residual
lineage, source Generalize, soundness and required principality in that packet.
No normality or redundancy conclusion follows.

## 7. Checks, dependencies, resources, and omitted verification

Commands: bounded `cat`, `sed`, `rg`, `head`, and `sha256sum` static source
reads; initial read-only `pwd`/`git rev-parse HEAD` confirmed the assigned
compiler baseline. No other Git command or Git mutation ran. Actual mutation
owners, caller routes, native/legacy guards, lexical scheduling and SCC
consumers were inspected. No tests, builds, probes, Oracle executions,
benchmark samples, or child jobs ran. This is static evidence, not execution
or independent certification.

Initial independent policy/input reads used at most five short shell calls
concurrently; subsequent constructor inspection was sequential. No heavy
process ran. CPU/RAM peaks and exact total elapsed wall time were not measured;
no explicit numerical wall-time allocation was supplied. Verification and
global process-budget ownership remain with the primary.

Requested routing: normal `gpt-6.1-sol` / `high` proof leaf; `.codex/config.toml`
registers `prover` and that default, while its role omits model/effort pins.
Observed effective runtime model/effort metadata: **unknown**. No routing
override, hot reload, or Astra execution is claimed.

Direct dependency SHA-256 (rehash before handoff):

```text
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df  crates/yu-solver/src/candidate_effect.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987  crates/yu-solver/src/candidate_context.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
75506948ec8043c9d5b4d0369ae94ed31c940aae0bc930ae1099bc1c758bb615  crates/yu-solver/src/term.rs
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  crates/yu-hir/src/module/local_source.rs
3dfd8ba4b21b76ee434a6b30697c5197213eae0679b84b98a6908e8a512fe6c4  notes/theory/2026-10-11-local-restoration-value-scc-preservation.md
8dd8eb55ac9d9df75980182cb5483f9394674a94f77c9d70d12f89b5be0d24e6  notes/theory/2026-10-11-simple-sub-value-reference-scc.md
66f8f068c453d491d45c09fe22a27f7a63ea5a31ca200b4cb15c4c21f4dbaad0  notes/progress/2026-10-11-native-value-reference-scc-map.md
2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0  notes/design/2026-10-10-parent-copy-scc-intrusion.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9  reference/shared/src/main/scala/simplesub/Typer.scala
```

No dependency was edited by this leaf. The Rust hashes match the preceding
rank/map dependency capture. Current note/authority hashes, rather than their
historical embedded status or hashes, pin the accepted clarification. Full
source-semantic correspondence, activation/replay completeness, failed-state
reuse, publication, all joint Call/effect interpretation and principality
remain unverified. No code/assertion/test obligation is adopted by this note.

## Commit packet

- Exact leased path: `notes/theory/2026-10-11-value-parent-copy-reachability-proof.md`.
- Baseline: `330d5432aff4b1f9655d501e17a9eefb7e75e098`;
  changed dependency hashes by this worker: none; hashes above freeze inputs.
- Review/status: compiler-referee reviewed research-only constructive
  operational derivation and earliest-constructor obstructions. Original
  source/inference gate OPEN. No authentic qualifying source witness and no normality or
  redundancy claim.
- Checks already run: named static source/caller/level/metadata inspection and
  dependency SHA-256 capture; final rehash recorded in the handoff. No
  executable verification.
- Proposed checkpoint message:
  `research: isolate native Value parent-copy reachability obstruction`.
- Shared-record deltas left to primary/curator: link the operational rank
  derivation and earliest-constructor table; distinguish raw family SCC from
  actual event qualification; record S as the remaining source/consumer
  premise without promoting the original source/inference, soundness,
  principality, Call/hygiene or cutover gates. No shared record was edited.
