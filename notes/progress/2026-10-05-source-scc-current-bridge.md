# Source/SCC finiteness: pinned current implementation correspondence

Date: 2026-10-05
Status: Frozen, unreviewed research checkpoint; bounded source inspection and conditional bridge
Baseline: `a4cfe9babacd0a7094d25beeec73104613b74b95`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151`
Lease: this file only
Implementation authority: none

## Objective, method, and authority

Audit which finite-instance premises follow from the approved F0–F2 foundation,
which are visible only in the current implementation, and which remain additional
obligations for its successor. Method: pinned Git-object reads and a structural
counting derivation over the inspected collector and routing loops. This lane
neither proves nor falsifies another lane's abstract SCC recurrence.

The Authoritative foundation is
`notes/design/2026-09-20-constraint-collection-scc-foundation-draft.md`:
status/scope lines 3–22; Oracle lifecycle 48–78; static boundary 84–131;
collection ownership 138–174; execution exclusion 185–197; F0–F2 214–253;
deferred semantic gates 327–339. The source-generator package
`notes/design/2026-10-04-source-generated-callback-structural-theorems.md`
is a Reviewed conditional theorem, with no implementation authority (4–9).
Its §5 generator (508–547) is explicitly monomorphic; it is not an already
implemented compiler contract. Accepted assignment boundary: preserve F5 as the
implementation being replaced, and derive no general source-wide or successor
conformance claim from it.

## What is established at the stated boundaries

| Boundary | Fact supported by the pin | Exclusion or necessary premise |
|---|---|---|
| Authoritative F0–F2 | One sealed finite definition/use batch; complete endpoint resolution before a static plan; IDs retain occurrence payloads; internal/incoming partition and dependency-first order. | No occurrence values, schemes, instantiation, or publication in F0–F2 (foundation 122–131, 163–174, 246–253). Thus this gate cannot prove finite scheme copies. |
| Theorem-scoped §5 source generator | A finite derivation with finite annotation schemas emits finite local data; preallocated monomorphic recursive references reuse binder endpoints (520–545). | Polymorphic recursion with unbounded instances is explicitly excluded. This theorem generator must be independently justified if used as a compiler bridge (535–538). |
| Current collector | One loop over HIR items, then one pending-use endpoint pass, then one sealed plan (solver `lib.rs` 815–889, 1008–1140, 1213–1232). | The admitted shape is narrow: integer/name bindings or a Lambda whose immediate body is integer/name; nested Lambda bodies are errors (913–965). There is no inference here for general application/Record/selection source generation. |
| Current SCC plan | Use IDs are checked unique, arc payloads retained, and partitioned by endpoint component; dependency sinks are scheduled (solver `scc.rs` 212–293, 416–457, 475–508). | Finite definition-dependency data is distinct from a finite graph of scheme instances or generated constraint descriptors. |
| Current executor | Each frozen component and each internal/incoming payload is traversed once by these execution loops; internal uses route live roots; incoming routes read installed schemes (solver `lib.rs` 12973–13006, 13893–13980, 13985–14008, 14877–14898). | Successful one-shot execution, valid batch/plan, and successful called operations. This inspection does not prove termination of generalization or live constraint closure. |
| Current structured incoming copy | Quantifiers and recursive bound binders receive one substitution entry each; recursive occurrences read that entry; bounds/predicate are restored from one scheme (14527–14660, 14255–14271, 14382–14398). | Finite, well-formed closed scheme and terminating traversal; successful resource admission. Effects are restricted in the inspected Function path (14290–14298, 14417–14424). No successor constraint-generator correspondence follows. |

The current code adds occurrence components and name constraints after the
foundation; those facts must not be attributed to F0–F2 itself. Conversely,
F0–F2's exclusion of values must not be read as a statement about current F5.
No judgment about conformity to the uninspected intervening gates is made.

## Counting derivation with explicit hypotheses

Let `D` count Binding items in a finite HIR input accepted by the inspected
collector, and `U` count its retained resolved module-definition occurrences.
Assume endpoint lookup succeeds and identity/allocation checks do not fail.

1. At most one pending resolved use is appended for a Binding: the whole-body
   Name branch (1008–1037) and Lambda branch (1038–1076) are disjoint; the latter
   examines exactly one immediate body Name. Expression items have no parent
   definition. Therefore **for this inspected collection path, `U <= D`**.
   This is not a bound for the full language's intended future collector.
2. The endpoint pass visits every pending record once (1088–1140). The SCC
   builder rejects duplicate use IDs (243–255), groups without dropping arc
   payloads (272–293), and moves each payload into either the same-component
   internal list or target-component incoming list (416–451). Thus
   `sum internal + sum incoming = U` for a successfully built plan.
3. The executor's component iteration is over the frozen dependency-first plan
   (12973–12978); its internal and incoming loops consume those lists
   (12980–13000, 13925–13980). Hence at most `U` use-routing calls are reached
   in one execution, and exactly `U` finish if execution succeeds. An error can
   stop earlier; retries and partial execution are not asserted to be additional
   successful routes. `route` and the Bottom shortcut guard one route per use
   ID (15017–15022, 15055–15059, 14907–14912).
4. For an incoming use `u`, suppose its installed scheme `S_u` has a finite
   quantifier list and finite recursive-bound list. The substitution loops
   (14535–14589) allocate at most `q(S_u)+r(S_u)` fresh rows, where `r` counts
   distinct listed recursive binder ordinals not already assigned. Positive
   and negative Recursive leaves read that existing substitution
   (14264–14271, 14391–14398); they do not recursively instantiate a new scheme.
   Consequently the finite set of reached incoming uses has at most
   `sum_u (q(S_u)+r(S_u))` fresh rows allocated by these loops, conditional on
   successful finite scheme formation. This statement counts these allocations
   only; constraint closure may allocate other objects.
5. To strengthen that row count into termination/finiteness of each complete
   scheme-copy traversal, additionally require the traversed constructor child
   relation to be finite and well founded after Recursive nodes are treated as
   leaves. `closed_parts` memoizes a Positive/Negative ID after visiting children
   (14211–14241, 14329–14331, 14333–14363, 14456–14458). Finite node count alone
   does not discharge that premise: a raw constructor child cycle would revisit
   an unfinished ID. Whether the closed-scheme owner enforces the required
   representation invariant is outside this inspected dependency set. No claim
   is made that such a raw cycle is constructible through current APIs.

Items 1–3 are bounded implementation characterization by source inspection;
item 4 is a conditional count for the named allocation loops; item 5 identifies
an unverified representation premise. These are not independently reviewed
results, source-rule proofs, total-inference termination, or successor adoption.
Function argument/result part products (14311–14326, 14438–14453) can be large;
finite expansion under the extra premise is not a polynomial resource bound.

## Small discriminating derivation

In proof notation, let a finite closed identity scheme be `forall a. a -> a`,
and let two distinct external static occurrences refer to it. The current
structured incoming path assigns separate fresh rows on the two invocations
of 14535–14552, with each invocation's Quantified leaves reading its own row.
The scratch is cleared between incoming invocations (14973). By contrast, §5's
monomorphic name clause is `T_e = T_x` (526), and monomorphic recursive
references retain the same binder endpoint (532).

This is a minimal sharing discriminator for two external occurrences: one
provider and two retained use IDs. It is a derivation from the inspected
operations, not an executed raw-source fixture and not a counterexample to §5.
Both constructions remain finite. Its point is that the monomorphic generator's
finite-generation proof does not itself justify polymorphic freshening; that
extra finite-copy argument must be supplied separately.

## Frozen Oracle correspondence and independence

The frozen Oracle offers independent historical implementation evidence for
the open/closed operation distinction, rather than a second checker supplied
with the same transition axioms:

- Oracle `crates/infer/src/scc.rs` 1–10, 45–59 explicitly supports late
  method/conformance dependencies and an incremental graph, unlike the static
  F0–F2 boundary.
- Internal uses and newly merged cycles emit open-use events (277–315).
  On ready-component removal, a QuantifyComponent event precedes an
  InstantiateUse event per retained incoming use, then predecessors are
  reconsidered (329–358).
- Oracle `crates/infer/src/analysis/session/instantiate.rs` 311–339 processes
  the supplied finite batch; 363–368 requires an available scheme;
  410–454 selects a finalized/imported or ordinary scheme-instantiation route.

These reads corroborate ownership and ordering only. They do not independently
prove finite source generation, enumerate all caller-produced events, or prove
finite descriptor cloning; the actual Oracle clone owners and their transitive
callers were not audited. Oracle and foundation share the selected lifecycle
and practical accepted-input intent. The theorem generator shares only part
of that structural language, and its monomorphic restriction is material.
There was no executable oracle comparison, mutation campaign, seed/range,
random search, fixture run, or checker whose assumptions could certify rules.

## Exact successor premise gap and next action

The useful bridge is **a finite static occurrence set plus an independently
proved finite-copy operation for every occurrence**. The pinned foundation
supports the first conjunct for its own sealed admitted envelope. The current
implementation exhibits an explicit copy design, with the conditional counts
above, but is the implementation being replaced. The §5 source generator
supplies finiteness for monomorphic recursive references, not arbitrary
polymorphic instance generation. None of the inspected sources establishes
all of the following successor obligations:

1. Its full admitted source derivations enumerate all static uses, including any
   solve-discovered dependency, under a selected sealed/recollection or readiness
   lifecycle.
2. Every published scheme is finite in the successor representation; recursive
   occurrences refer to preallocated binders; every copy preserves that finite
   representation without starting an unbounded new instance sequence.
3. The successor's generator emits exactly the separately justified structural
   obligations, and preserves required effects, guards, permissions and joint
   relations. Finite structure does not establish those semantic correspondences.

Recommended next action: assign a separate audit of the successor's specified
scheme representation/copy owner against obligations 1–2, with source-to-copy
identity pins and explicit late-dependency handling. If no such specified owner
exists, return this exact missing production-independent premise to the primary;
another finite toy recurrence probe cannot supply it.

## Commands, coverage, resources, and omissions

Budget: at most ten sequential lightweight shell commands; one command process
at a time, sequential Git-object subprocess reads; no builds, tests, probes,
benchmarks, children, Git mutations or shared-record edits. Ten commands total
including rule reads, pinned document/source excerpts, object/path location,
hash capture, this exclusive write, and final text/hash inspection. Each read
command reported approximately 0.1 seconds or less; cumulative CPU/RSS and
end-to-end wall time were not measured. No claim about peak memory is made.
Some broad locator output was truncated; conclusions use the subsequently
read exact excerpts listed above. Rules were initially read from the worktree,
then byte-checked equal to their pinned objects before freezing. All semantic
and implementation evidence was read from the pinned committed objects.

No abstract recurrence attack, unrestricted source theorem, polymorphic
recursion proof, scheme-owner validation, generalization termination proof,
constraint solver termination proof, dynamic method/role/conformance audit,
error/retry invariant proof, accepted raw-source behavior, performance result,
or successor conformance was verified. No independent review was performed
on this producer's note. Shared task/index/theory records and question bundles
were neither inspected nor written. The primary owns dependency revalidation
against integration HEAD and all shared-record updates.

## Dependency snapshot

All line numbers above refer to the indicated pinned revision. SHA-256 values:

| Revision | Path | SHA-256 |
|---|---|---|
| baseline | `notes/design/2026-09-20-constraint-collection-scc-foundation-draft.md` | `37a2799288db0081cf3f32c7f6860c376ff0b2ce3249397cd9c23c7a89fedeaa` |
| baseline | `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` | `568bb4649ba278519f3ad01af2091dd1baaca42850cd19e3b5734b3c47c2eefe` |
| baseline | `crates/yu-solver/src/lib.rs` | `a2103c6735d7a4efad00231f973544dda59d42219dbf83439fffc17889168e59` |
| baseline | `crates/yu-solver/src/scc.rs` | `3cfce9acfddd77838398cd95cd13c053f71f27a8367b07175a83c825d68a8df8` |
| Oracle | `crates/infer/src/scc.rs` | `5c0c70a4681db1c9687bc0da5c5ac70cfcad9f9f286778d87811b832dc4506e6` |
| Oracle | `crates/infer/src/analysis/session/instantiate.rs` | `bf21175f47df78f35f2070fea51b3483d59a91ac4a606bace9e24f32878c2d19` |
| baseline | `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| baseline | `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| baseline | `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| baseline | `rules/orchestration-budget.md` | `32174c0eb14314df334499586b43db3074de4662fdc908da60eb1a24e1dc3716` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-05-source-scc-current-bridge.md`.
- Baseline SHA: `a4cfe9babacd0a7094d25beeec73104613b74b95`.
- Dependency hashes changed by this worker: none; pinned snapshot above.
  Current integration-HEAD comparison remains primary-owned.
- Review status: frozen, unreviewed research checkpoint; bounded characterization
  and conditional counts only; no gate closure or implementation authority.
- Checks run: exact committed excerpts, rule-byte equality, recorded dependency
  SHA-256/blob pins, exclusive output creation, final note structure/hash check.
  No compiler tests or experimental checks.
- Proposed message: `research: audit pinned source and SCC finite-instance correspondence`.
- Shared-record deltas intentionally deferred: primary may link this artifact
  from `tasks/current.md`, `tasks/research-lab.md`, and the governing theory map;
  retain finite static planning separately from the missing successor finite-copy
  and source-generator premises. No design/index status promotion is supported.
