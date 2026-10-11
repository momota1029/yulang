# Nested source Value references: preserved active ancestor

Date: 2026-10-11
Status: independently reviewed, frozen research-only bounded constructor derivation.
Parent source/algorithm adequacy and authentic parent/copy SCC gates: OPEN.
Primary baseline: `330d5432aff4b1f9655d501e17a9eefb7e75e098`.
Exclusive lease: this file. Leaf; no delegation, compiler edits, execution,
tests, builds, Oracle, formatting, or Git commands.

## Objective, authority and method

Inspect a nested lexical cycle in which an active ancestor function returns a
descendant function and that descendant references the ancestor. Locate the
first preserved or replaced reference to the original ancestor, using actual
HIR identities, source actions, Function ports and capture/restoration owners.
This differs from a rank proof and from the earlier `loop y` application
fixture: the minimal candidate returns the ancestor as a value and returns
the helper without calling it.

Governing sections are the current accepted
`notes/design/2026-10-10-parent-copy-scc-intrusion.md`, “Direct decision”,
“Selected operation and compiler responsibility”, “Value-reference SCC
clarification” and “Retained boundary”; and
`notes/design/2026-10-10-local-self-recursive-binding.md`, “Selected source
behavior”, “Proposed source-to-solver seam”, “Required invariants and evidence”
and “Review boundary”. The latter explicitly requires a nested helper's use
of an active outer recursive binder to use the same open root.
`notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§1–3 and
“Authority and integration” preserve natural inference and original proof
obligations. `rules/design-authority.md`, “Authority order”;
`rules/research-lab.md`, “One semantic baseline, explicit dependency
invalidation”, “Evidence quality and stopping unproductive loops” and
“Writes, artifacts and review snapshots”; and `rules/git-concurrency.md`,
“Disjoint-file mode”, bound this assignment.

Inputs include the latest
`notes/theory/2026-10-11-value-parent-copy-reachability-proof.md` and
`notes/progress/2026-10-11-source-qualified-value-parent-copy-scc.md`.
Their operational exclusion and open semantic premise are not re-proved or
certified here. The primary supplied the current accepted decision snapshot;
its Value clarification differs from the baseline decision file. The source
hashes below match the latest notes' recorded baseline hashes. No Git baseline
inspection was performed under this packet's no-Git constraint.

Claim class: conditionally reviewed bounded source-to-constructor derivation,
with a minimal candidate family member. This is not an executed source witness,
theorem of source acceptance, all-source characterization, or counterexample to
intrusion. In particular, nonreachability of a retained pair would not
establish ordinary inference adequacy.

## Minimal candidate and explicit hypotheses

```yulang
my outer = { my f x = { my g y = f; g }; f }
```

There is one active local ancestor `f`, one nested parameterized helper `g`,
one ancestor Name in `g`'s body, and one returned helper Name. Both headers
use the already represented parameterized local-function form. Removing
the helper loses the requested nested shape; removing its ancestor Name
loses the dependency; replacing the returned helper with another value loses
the selected outward path. This is structural minimization within this
return-only family, not a globally shortest-byte witness.

Hypotheses:

1. The ordinary syntax/HIR carrier forms the indicated two nested Blocks,
   two local function binders and their Lambda/Name forms. Exact bytes have
   not been parsed here. Existing fixtures corroborate the nested grammar
   and lexical-resolution route; their test assertions were read, not run.
2. Candidate collection and native source scheduling use the frozen owners
   below. Allocations and identity checks succeed; no test injection,
   mutated external session or reused failed operation is substituted.
3. The named admissions, restoration steps and queued Value replay children
   complete before the next dependent source step/capture. The note shows
   their concrete producers, but does not prove whole-run termination or
   every replay's eventual delivery.
4. Rows in this prefix remain generic with their initialized identities and
   levels. No prior qualifying Value equality changes those endpoints.

The exact return-only source has not been independently assigned a complete
semantic/local-law derivation. The scoped nested-block addendum
`2026-10-06-nested-block-function-source-realization-addendum.md` §2 fixes
return/capture for its exact `apply/step` candidate; it is corroborating
context, not authority to extend that document's scope to this candidate.
The local-self decision does independently fix the active ancestor identity.

## HIR and scheduler map

Let F be f's initializer Value root, X its formal, G g's initializer root,
Y its formal, N the `f` Name in g's body, J the returned `g` Name, and B the
inner Block/f-body root.

| Owner | Actual construction | Result for this candidate |
| --- | --- | --- |
| HIR `local_source.rs:320–373` | Push the parameterized local's temporary self identity before its body; restore and publish afterward. | f remains visible while g's initializer is formed. g/y do not shadow f. |
| HIR `local_source.rs:396–437,637–647` | Lexical push/restore and identifier lookup use the latest binding. | N resolves to the original `HirLocalId` of f, not a new helper-local f. |
| HIR `local_source.rs:819–829` | Initializers are formed in sequential order, then final expression; scope restoration follows. | J resolves to published g; the final outer f resolves to published f. This adds no mutual-recursive sibling group. |
| `candidate_source.rs:251–305` | Start at 1; Block initializers add one; Lambda/body preserve the level. Track active parameterized initializer endpoints. | F,X,B,J have level 2; G,Y,N have level 3. g's publication boundary is 2; f's is 1. |
| `candidate_source.rs:381–388,657–669` | An active Local Name emits/executes an ordinary Link; a published Local Name uses the scheme route. | N uses Link(F,N) before g/f installation. J freshens g after installation, while F is still active. |

The source rule does not block the nested shape. A proposed forward reference
between adjacent local sibling binders would instead fail the sequential HIR
visibility rule. A proposed ordinary nonfunction self initializer is outside
the selected self-binding seam; no such form is needed here.

## Exact retained ancestor reference and ordinary cycle

All Function arrows below project actual stored Value argument/result fields;
comparison orientation does not define adjacency.

1. **The earliest ancestor dependency is preserved at N.** The open Link
   compares F with N. Native row admission
   (`candidate_extrusion.rs:815–824`) physically stores F in N's lower
   list, because N is level 3 and F is level 2. Thus **N → F**.
   No capture/freshening is used for this recursive occurrence. This is
   the same original open F required by the selected nested-helper rule.

2. g's Lambda constructor builds a positive Function with actual Value
   fields Y and N (`lib.rs:11233–11260,11342–11362`), and installs it on G.
   At target 3, extrusion returns both fields unchanged
   (`candidate_extrusion.rs:83–95`); hence **G → Y,N** through that Function.
   g installation retains `LocalScheme {root=G,boundary=2}`
   (`candidate_scheme.rs:1316–1334`). Installation itself adds no edge.

3. **The first freshening replaces descendant coordinates and preserves F.**
   J is the published g use at level 2. Capture classifies G,Y,N as local
   (`level>boundary=2`) and F as shared (`level=boundary=2`)
   (`candidate_scheme.rs:300–326`). It captures N's lower F and G's lower
   Function, stopping bound expansion at shared F (`:567–621`).
   Joint mapping creates G*,Y*,N* at level 2 and retains the exact F identity
   (`:1008–1021`). Function reconstruction uses Y*,N* (`:1141–1157`).
   Owner/side restoration installs **N*.lower F** and
   **G*.lower Function⁺(Y*,effects,N*)** (`:1221–1266`). Therefore
   **N* → original F** survives. Capture did not infer that edge from parent
   metadata, and it did not silently snapshot a fresh F while F was active.

4. The Local cursor compares G* with J after restoration
   (`candidate_scheme.rs:1500–1519`). Equal-level admission stores J in
   G*'s upper list. Opposite-bound replay
   (`candidate_extrusion.rs:763–802`) requests the restored positive Function
   against J. When its queued child is consumed, J receives that Function,
   with the exact same Y*,N* fields. The block's Group relation then compares
   J with B (`candidate_source.rs:459–467`; `shadow_apply.rs:1327–1330`).
   Equal-level admission stores B in J's upper list; replay installs the
   same Function on B. Its ports are level 2, so target-2 extrusion does
   not replace N* or F.

5. f's later Lambda uses X and B as actual Value fields and installs its
   positive Function on F. Both are level 2 and survive target-2 extrusion.
   The resulting actual payload paths are

   ```text
   F → Function⁺(X,...,B) → B
   B → Function⁺(Y*,...,N*) → N*
   N* → F
   ```

   Thus **F → B → N* → F** is a conditional real-reference cycle containing
   the original ancestor F and a returned descendant Function instance.
   The candidate adjacency definition follows these owned lists and outward
   Function fields (`candidate_intrusion.rs:389–413,445–468`). This trace does
   not claim that an SCC scan runs on this prefix: `settle_candidate_intrusion`
   returns early when no parent records exist (`:370–373`). No rank-only
   argument or comparison-as-edge convention is used to obtain this cycle.

Replay is an explicit premise at step 4, not an invisible saturation rule.
Its origin-pair producer is `candidate_context.rs:2911–2987`; queued child
consumption and delivery are at `:3058–3119`. The fresh bounds retain use
evidence before the ordinary G*→J comparison. No test helper installs B's
Function directly. A scheduler failure before the named child completes
invalidates the cycle conclusion, while steps 1–3 still identify the
preserved ancestor dependency in their completed prefix.

## Where identity replacement occurs, and its limits

The returned helper is an ordinary fresh g instance. G* is **not** an
extrusion copy of G: `prepare_candidate_fresh_use` allocates it without
`retain_extrusion_parent`. Neither the lexical child g nor N's occurrence
identity creates an extrusion-parent event for F. The stated cycle therefore
does not place a retained parent/copy pair in one SCC merely because it
contains a lexical ancestor and a helper instance.

For this return-only construction, the named Value admissions either link
rows or install Functions whose ports already fit their receiving level;
fresh-use allocation is the only stated Value identity replacement. No named
step creates a retained Value extrusion pair. Effects still have their own
ports and transitions; this statement does not erase them or characterize
their SCCs. Future callers/ascriptions may create genuine Value extrusion
events and are outside the traced family.

After f publication, the final outer f use captures F and this cycle at
boundary 1. F,B,N* and the other level-2 local rows are then jointly remapped
to new use-level-1 rows. That is the **first named operation replacing F**
on this outward path. It preserves the captured cyclic sides and sharing,
and makes no retained event `(Ffresh,F)`. The source rule selects later
capture/freshening, while the authoritative source Generalize definition
`2026-10-08-source-generalize-definition.md` §2 requires preserving independent
instantiation versus monomorphic aliases, fixed providers, anchors and the
complete simultaneous relation. The constructor trace alone does not prove
all of those semantic premises. Accordingly, replacement here is the selected
use route, with semantic adequacy still conditional; this note does not
certify general freshening or extrusion as lawful on all supported sources.

There is no required original-ancestor occurrence lost at steps 1–5 under
the selected active-root rule. An alleged qualifying extrusion pair based on
G*/G, N*/N, or the lexical relationship g/f first becomes unauthenticated at
its claimed parent-event creation. To falsify the original adequacy premise,
a different source family must fix an **actual recorded extrusion parent**
and independently justify why that exact original endpoint must remain on a
return path after copying. This packet supplies neither that endpoint nor a
new source restriction to exclude it.

## Checks, coverage, resources and frozen dependencies

Commands run: bounded `cat`, `sed -n`, `rg -n`, `rg --files` and `sha256sum`
over the named rules, skill, authority, previous notes and owning source.
A first search guessed a nonexistent HIR test path and absent `spec/`; the
HIR test was located at `crates/yu-hir/src/tests/local_self_recursive_binding.rs`
and read. No source execution/parse, checker, test, build, Oracle, mutation,
Git command, model-policy change or child launch ran. No seeds or enumeration
ranges apply; the completed constructor analysis covers one minimal candidate
at one helper depth, plus the selected final fresh-use seam. Deeper helper
families, annotations, calls, module recursion and abnormal reuse are omitted.

There is no executable oracle. HIR lexical resolution independently grounds
the endpoint supplied to source Link relative to bound storage/capture;
all inspected owners share the compiler's ID, level, polarity and genericity
conventions. Their agreement is source/artifact correspondence, not independent
proof of the source semantic laws. The semantic/lifecycle/Call/hygiene,
termination, soundness, principality and full cutover gates remain unverified.

Resource use: one reasoning leaf, short file-read/hash utility processes,
zero compute probes/build processes, zero benchmark samples. Peak CPU/RSS,
aggregate process count and exact elapsed wall time were not measured; the
packet supplied no numeric wall-time limit. No resource escalation occurred.
Initial batched reads exceeded their total capture limit; relevant authority
and constructor slices were subsequently reread narrowly.

Frozen direct SHA-256 dependencies (source hashes match the preceding notes):

```text
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987  crates/yu-solver/src/candidate_context.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6  crates/yu-solver/src/shadow_apply.rs
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  crates/yu-hir/src/module/local_source.rs
4e2b9bc5210358059533cbe3b7fc2202daf64123b77e7333f198eb707eb7b59c  crates/yu-hir/src/tests/local_self_recursive_binding.rs
39c64235bf61ebeeae18667eed527f784d2f9eb2713f4b91d9cbb7ab7d2afa8a  notes/theory/2026-10-11-value-parent-copy-reachability-proof.md
d73496fc376a9970d3a72e49208c3857e885b18b5ab2de074bc2cceae81a8a76  notes/progress/2026-10-11-source-qualified-value-parent-copy-scc.md
2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0  notes/design/2026-10-10-parent-copy-scc-intrusion.md
38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895  notes/design/2026-10-10-local-self-recursive-binding.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38  notes/design/2026-10-08-source-generalize-definition.md
750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0  notes/design/2026-10-06-nested-block-function-source-realization-addendum.md
```

Recommended next action: have the primary adjudicate the active-root preserved
reference trace against the original source adequacy premise, then assign its
specific remaining **genuine extrusion-parent** source owner. Another lexical
family diagram or rank-only probe would leave that premise untouched.

## Commit packet

- Exact leased path: `notes/progress/2026-10-11-nested-source-value-reference-search.md`.
- Baseline SHA: `330d5432aff4b1f9655d501e17a9eefb7e75e098`.
- Dependency changes authored: none. Current decision hash above is the
  accepted primary-supplied clarification; baseline decision hash reported by
  the preceding note is `8ae4348a93dce6df1852a34b2294ebc5e4e256d8b018c1f6eaad42c502470a8e`.
  Source dependencies match the preceding baseline captures; no independent
  Git equality check is claimed. Primary owns final dependency revalidation.
- Review status: regression-auditor review closed its bounded constructor
  finding after one precision repair; no parent gate closure or implementation
  authority.
- Checks already run: targeted lexical/action/port/capture/restoration/replay/
  scanner reads and SHA-256 capture. No source execution.
- Proposed research-checkpoint message:
  `research: trace preserved ancestor reference through returned local helper`.
- Shared-record deltas intentionally left to primary/curator: record this
  conditional ordinary cycle and exact preserved active-root reference;
  distinguish fresh-use and lexical children from actual extrusion copies;
  keep semantic adequacy and authentic retained-pair SCC gates OPEN. No shared
  task/index/design/theory/question-board record was edited.
