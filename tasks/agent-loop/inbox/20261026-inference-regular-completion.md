# Constructive regular-graph completion and preservation

Date: 2026-10-26. Producer: `/root/regular_completion`, generic `lean_prover` leaf.
Parent: `/root`; original target remains the full `SourceProblem.InferenceSoundness`.
Frozen parent-supplied baseline: `eb3eef2f6a29d9c2a6132d648866c60900db276c`, branch `yulang3`.

Status: both new source modules are checker-accepted; every originating constant
has a printed type and transitive axiom audit. Fresh independent review and
integration remain primary-owned. No whole-source or native-implementation
closure is claimed. **WRITES STOPPED** after this handoff and the two leased
source copies; no child, background process or Git operation remains.

## Exact delivered paths

- `notes/theory/lean/YulangClosure/SimpleSubRegularGraphExtension.lean`
- `notes/theory/lean/YulangClosure/SimpleSubRegularCompletion.lean`
- This handoff: `tasks/agent-loop/inbox/20261026-inference-regular-completion.md`
- Owned isolated source/cache/evidence: `/workspace/scratch/f98087c7ac1a/inference-completion/`.

No base module, root import, shared status, compiler file, toolchain, manifest,
dependency, Git index/ref, or other worker output was changed. The isolated
project was copied before construction; all eight imported project source
modules still match the repository byte-for-byte at freeze.

## Governing source and unchanged parent

Read `.codex/agents/lean-prover.toml`, root `AGENTS.md` / `AGENTS.pre-sprint.md`,
`rules/goal-driven-sprints.md`, `rules/design-authority.md`, the proof skill and
its `sources.md` / `execution.md`, and the actual relevant Lean definitions.
The governing inference policy is
`notes/design/2026-10-11-yulang-inference-top-level-principles.md`, sections 1–5.
The original scope is `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
section 1 and `docs/yulang-whole-proof-closure-ja.md` sections 1 and 4.
The current source map and immediate gap are
`notes/progress/2026-10-26-inference-soundness.md`, “Final connection”, and
`tasks/agent-loop/inbox/20261026-inference-regular-publication.md`.

The unchanged parent is `YulangClosure.SourceProblem.InferenceSoundness`:
for every supported source, generated constraint problem and successful solution,
construct an original source derivation and the same-scoped witness. This packet
removes the exact-existing-node decoding premise of the intermediate regular
publication bridge. It neither narrows that source theorem nor supplies its
missing native/source correspondence.

## Construction and decisive invariant

Namespace `YulangClosure.SimpleSub.RegularExtension` defines
`Extends source target := ∀ k, ∃ suffix, target k = source k ++ suffix`.
This is literal finite-table prefix preservation, with fixed numeric identities
in both kind tables. No old node is rewritten; old cycles are allowed unchanged.
`appendNode` appends one node only to its own kind table. `appendNode_extends`
and `appendNode_valid` are proved from the list construction.

The extension module derives preservation of:

- successful existing lookups and reference existence;
- exact earliest-node search (`findNode`), so successful decoder IDs remain fixed;
- structural expansion, layers and the independent all-depth `RegularSub` relation;
- actual `Extrusion`, every `ConstraintStep` constructor and complete `ConstraintHistory`;
- certificate closure, and acceptance/checkStore success when the target is valid;
- successful term, constraint and complete-store decoding, and store satisfaction.

These are forward preservation statements. Graph validity is necessary for
`accepts` because it checks every new node, not only the old certificate. The
completion construction proves that target validity; it does not hide it in a
supplied preservation law. No converse about new/missing old references is claimed.

Namespace `YulangClosure.SimpleSub.RegularCompletion` supplies actual executable
`intern`, `completeTerm`, `completeConstraint`, `completeStore` and `completedStore`.
`intern` reuses the first exact existing node; otherwise it appends the desired
node and returns the old table length. Recursive completion processes children
first and creates every missing atom/bottom/top, all-four-port Function, nil,
finite row suffix, tuple suffix and tuple-payload node needed by the existing
decoder. Graphs stay finite because each is a pair of lists and recursion is on
the finite input syntax/store. This is proof-side finite graph completion, not
a proposed Rust production algorithm or new runtime requirement.

`Shape` distinguishes plain nodes, records with their actual label list, tuples,
and variants with their actual tag list. `Lawful base refs term shape` contains:

- a correctly kinded actual `base.lookup` for each variable occurrence;
- structural legality for atoms, bottom, top and all four Function children;
- a record-shaped tail and a fresh label for record cons (optional bits retained);
- a tuple-shaped tail for tuple cons;
- a tuple-shaped payload, variant-shaped tail and fresh tag for variant cons.

It does **not** contain decoding success, a subtype comparison, semantic model,
certificate, history, or arbitrary preservation hypothesis. It permits row-tail
variables and payload variables whenever their actual existing nodes have the
required shape. Initial `graph.Valid` establishes references and uniqueness in
existing nodes. The constructor cases derive validity of all appended nodes.
The unguarded executable algorithm is total as an `Option` function; no claim
says an arbitrary unlawful input produces a valid graph. `completedStore` has a
default result for failure, and `completedStore_correct` proves that branch is
unreachable under the stated validity/legality premises.

## Application to the previous publication theorem

`completeTerm_correct` constructs a target and identity, the actual execution
equation, and `Built`: prefix extension, target validity, actual successful
`RegularPublication.decodeTerm`, and the exact resulting row shape.
The graph may initially extend the graph supplying variable witnesses; this
strong induction invariant lets siblings accumulate nodes in one shared graph.

`completeStore_correct` completes the entire finite inventory jointly.
`completedStore_correct` exposes its computable result and derives
`decodeStore result.1 refs store = some result.2`.
`completedStore_accepts` transports any old accepted certificate to this
constructed valid extension.

`completed_history_store_sound` directly calls the existing `history_store_sound`
with the derived decode equation. `completed_publication_with_clients` directly
calls `publication_history_with_clients` for the constructed graph and pair list.
It retains the original bounded clauses, guard/closure/image assumptions,
finite-use bounds, syntax-only inventory coverage, actual regular history and
terminal finite certificate acceptance. One transported reference assignment
serves every original publication use and every later client together.
**No desired decoder-success equation is supplied by the caller.**

The concrete sparse example initially contains full record/tuple/variant nodes
but lacks their nil auxiliaries; `missing_nil_rejected` checks that old decoding
fails. The joint completion then decodes all three carriers plus a cyclic
Function, with output IDs 1/2/3/4, and keeps cyclic node 4 exactly
`function 4 0 0 4`. Its two effect ports resolve in the separate effect table.
The graph's validity and lawful inventory are independently constructed.

## Exact remaining premise and next integration seam

The previous “all exact nil/suffix/payload nodes already present” requirement is
replaced by an initial valid finite graph plus the explicit variable-reference,
row-shape and uniqueness facts above. Missing constructor inventory is now
constructed; it is not another caller equation.

The native owner must still supply faithful initial references/graph validity,
the actual finite publication/client inventory and its `LawfulStore`, scoped
publication guard conditions, and the concrete history. Final acceptance is
still explicit here. The primary's separately owned
`SimpleSubRegularDecision` is an independent next seam for constructing/checking
the final certificate; this packet does not import or rely on that concurrent
module, and does not assert it independently reviewed.

Union/intersection completion returns `none` explicitly and its rejection is
proved in `lattice_completion_unsupported`; lattice support is another packet.
The base graph still has no alias-only nodes. Full native row width/presence/
matching, ordinary coalescing, original source generation, contextual Call and
effect interpretation, source/native trace/serialization and the unchanged
whole-language inference theorem remain open. Exact finite-list carriers here
do not decide those source semantics. Existing cycles are preserved but no
missing cyclic semantic model is synthesized from arbitrary constraints.

## Pinned execution and actual results

Pinned native executable:
`/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`.

Observed versions:

```text
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
```

Ordinary sandbox `lake env lean --version` failed with exit 1:
`error: could not detect the configuration of the Lake installation`.
The session-authorized escalated execution of the same installed native tool
succeeded; no installation, global default or dependency change was made.
All compilation/audit invocations were sequential in the isolated project,
with `LEAN_NUM_THREADS=1`, project `-j1 -M1024`, and `timeout 120`.
The finite packet used seven focused builds and two audit invocations (nine
checks), below the assigned sixteen-check bound. Peak RSS was not separately
measured; the reported memory bound is Lean's configured 1024 MiB limit.

Final successful commands, from the isolated project:

```sh
LEAN_NUM_THREADS=1 timeout 120 /workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake build +YulangClosure.SimpleSubRegularCompletion
LEAN_NUM_THREADS=1 timeout 120 /workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake env lean -j1 -M1024 AuditCompletion.lean
```

Both final wrappers preserve the underlying exit status and returned 0.
`check07.log` records both source modules built successfully, including the
final convenience preservation lemmas. `audit02.log` is the complete successful
audit with every originating constant's full type and transitive axiom result.
The root import/full default-target integration remains primary-owned.

Audit scope is **all originating constants**, not only public source theorems:

| Module | All constants | Theorem constants |
| --- | ---: | ---: |
| `SimpleSubRegularGraphExtension` | 42 | 36 |
| `SimpleSubRegularCompletion` | 249 | 137 |
| Total | 291 | 173 |

Each declaration was located by exact environment origin module, including
private helpers, equation theorems, generated matchers and inductive/derived
constants. The audit rejects project axioms and rejects any transitive axiom
outside `propext`, `Classical.choice`, `Quot.sound`. Actual complete results:
151 constants have no axioms; 119 use `[propext]`; 21 use
`[propext, Quot.sound]`; none use `Classical.choice`, `sorryAx`, native-evaluation
assumptions or any project axiom. The main completion/publication theorems use
`[propext, Quot.sound]`. The audited files contain no `sorry`, `admit`, project
axiom, checker bypass, `native_decide`, external implementation annotation or
other source-search match for those forbidden proof shortcuts.

## Material failure and repair evidence

All failed logs are retained in the owned scratch directory; none was replaced
by a successful log. `check01`, `check03`, `check04`, `check06` are failures;
`check02`, `check05`, `check07` are successful builds.

- `check01.log`: namespace collisions between extension theorem names and imported
  decoder definitions, a cons-append simplification, inaccessible indexed state
  binders and a variable-kind inference placeholder. Repaired by distinct lemma
  names, explicit list reduction, index-inferred constructor arguments and a
  separate checked-reference lemma. `check02` then built the extension.
- `check03.log`: `intern` reduction needed to consume the find result before
  unfolding `findNode`; function reference membership needed the empty-list
  disjunction removed. Both repaired explicitly.
- `check04.log`: four projections `bt.valid.valid_lookup` resolved to Function;
  replaced with the actual `Graph.valid_lookup bt.valid`. `check05` then built
  the whole completion/publication theorem and concrete examples.
- `check06.log`: added `Extends.check_store` exposed the local theorem-name
  collision `accepts source`; qualified the intended `Regular.accepts`.
  `check07` passed with the entire final surface.
- `audit01.log`: audit counter metavariables were inferred as `MessageData` from
  pretty printing; supplied explicit `Nat` types. No proof axiom failure occurred.
  `audit02` passed every one of the 291 originating constants.

Early build wrappers ended by printing the log and therefore returned shell 0
even for failed builds; the logs explicitly retain `error: build failed`.
Those are not reported as passing checks. The two final commands capture and
return the real tool status. The first audit was run after the failed final
convenience-lemma attempt, so only `audit02` after `check07` is final evidence.

## Source and evidence hashes

All source hashes below are SHA256. The eight pre-existing dependencies were
compared with their isolated checked copies and all matched at freeze.

| Module | SHA256 |
| --- | --- |
| `YulangClosure.Contracts` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `YulangClosure.SimpleSubConstraintSoundness` | `33709d3978e8071708c10bba23d85b1b025c11dfd988220501acb7c6e3220293` |
| `YulangClosure.SimpleSubConstraintSyntax` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `YulangClosure.SimpleSubGeneralizationSoundness` | `3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246` |
| `YulangClosure.SimpleSubRegularCompletion` | `d7231d0a3695dba7f3102e5fe235d4d26e34cad78870dbdbae9b7633c42787aa` |
| `YulangClosure.SimpleSubRegularConstraintSoundness` | `1d2266867115fc27afe39dbb80a3ca0e8f75247a2e16b739145137e83999de33` |
| `YulangClosure.SimpleSubRegularGraphExtension` | `0b45d0e6d58701cba9f7df00d2a63897327e357ed3047b36e96d8fb6c49893d8` |
| `YulangClosure.SimpleSubRegularPublication` | `18fc6f138204e1529dcd0bb9c01a20de7444a26e4dadc87677460ccd8ac9fc99` |
| `YulangClosure.SimpleSubRegularSolutions` | `755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29` |
| `YulangClosure.SimpleSubScopedPublication` | `d64e9bffca5d513985237a9ff78dcf3d9e43baae1594edbc93dff4b5410d428f` |

Evidence files retained under the owned scratch directory:

| File | SHA256 |
| --- | --- |
| `/workspace/scratch/f98087c7ac1a/inference-completion/check01.log` | `eee5a32552203334dbec030c4905c88ab427a4360b2b83e929b3afc50cfdeb6b` |
| `/workspace/scratch/f98087c7ac1a/inference-completion/check02.log` | `135e27b8f36c73ddf837b778a7c120ef07b58c067cfb2f75fe1a2db9aed15c1e` |
| `/workspace/scratch/f98087c7ac1a/inference-completion/check03.log` | `37ba30ff212247e8ae5e22319823171a342e2760004bca0ad38365df2b671f77` |
| `/workspace/scratch/f98087c7ac1a/inference-completion/check04.log` | `d6cb83200902d4ba0bbced1cea746b6a9b69abf8c7ca8d2a5e55fa88526202d6` |
| `/workspace/scratch/f98087c7ac1a/inference-completion/check05.log` | `4494c4ece3a788abb12014698c6ef253ba80e4427facc5d7d667eee9e8a483c0` |
| `/workspace/scratch/f98087c7ac1a/inference-completion/check06.log` | `ef81efe2bf3a72bbf67999bfc6bf2141b84f0d9b451f89e0a71fc7b8611dede4` |
| `/workspace/scratch/f98087c7ac1a/inference-completion/check07.log` | `2e9a9b0e6ac3d317673c566d3820a7fd743060202164ac60a7fb739eba05c1ed` |
| `/workspace/scratch/f98087c7ac1a/inference-completion/audit01.log` | `7f75e8e67fead19e678bda4a1bb61b917ca7e18ce825096ecd3af3c3fac75496` |
| `/workspace/scratch/f98087c7ac1a/inference-completion/audit02.log` | `22159635d6d34a1be7787afed73f0783e027fc9e88f06de299686d31c9f82d32` |
| `/workspace/scratch/f98087c7ac1a/inference-completion/project/AuditCompletion.lean` | `b94896c2ab2b1f90ed77e65889d3ebbe5732c8cc54f11c605d03bf7613a89540` |
| `/workspace/scratch/f98087c7ac1a/inference-completion/hashes.json` | `3e6becd6eea32e37ff255a8a5035f88c93ed870fe6d95f18b0f415b4d8a551bd` |

## Exact printed principal theorem types and axiom results

```text
@YulangClosure.SimpleSub.RegularCompletion.completeTerm_correct : ∀ {base : YulangClosure.SimpleSub.Regular.Graph}
  {refs : YulangClosure.SimpleSub.RegularPublication.References} {k : YulangClosure.SimpleSub.Kind}
  {term : YulangClosure.SimpleSub.Term k} {shape : YulangClosure.SimpleSub.RegularCompletion.Shape k},
  YulangClosure.SimpleSub.RegularCompletion.Lawful base refs term shape →
    ∀ (graph : YulangClosure.SimpleSub.Regular.Graph),
      YulangClosure.SimpleSub.RegularExtension.Extends base graph →
        graph.Valid →
          ∃ target identity,
            YulangClosure.SimpleSub.RegularCompletion.completeTerm graph refs term = Option.some (target, identity) ∧
              YulangClosure.SimpleSub.RegularCompletion.Built graph refs term shape target identity
'YulangClosure.SimpleSub.RegularCompletion.completeTerm_correct' depends on axioms: [propext, Quot.sound]
```

```text
@YulangClosure.SimpleSub.RegularCompletion.completedStore_correct : ∀ {graph : YulangClosure.SimpleSub.Regular.Graph}
  {refs : YulangClosure.SimpleSub.RegularPublication.References} {store : YulangClosure.SimpleSub.Store},
  graph.Valid →
    YulangClosure.SimpleSub.RegularCompletion.LawfulStore graph refs store →
      YulangClosure.SimpleSub.RegularExtension.Extends graph
          (YulangClosure.SimpleSub.RegularCompletion.completedStore graph refs store).fst ∧
        (YulangClosure.SimpleSub.RegularCompletion.completedStore graph refs store).fst.Valid ∧
          YulangClosure.SimpleSub.RegularPublication.decodeStore
              (YulangClosure.SimpleSub.RegularCompletion.completedStore graph refs store).fst refs store =
            Option.some (YulangClosure.SimpleSub.RegularCompletion.completedStore graph refs store).snd
'YulangClosure.SimpleSub.RegularCompletion.completedStore_correct' depends on axioms: [propext, Quot.sound]
```

```text
@YulangClosure.SimpleSub.RegularCompletion.completed_publication_with_clients : ∀ {n count : Nat}
  {bounds : List YulangClosure.SimpleSub.ScopedPublication.Bound}
  {beforeCap afterCap beforeUse afterUse : YulangClosure.SimpleSub.ScopedPublication.Flags}
  {roots : List YulangClosure.SimpleSub.ScopedPublication.Row} {uses : List Nat} {q : YulangClosure.SimpleSub.Renaming}
  {graph : YulangClosure.SimpleSub.Regular.Graph} {refs : YulangClosure.SimpleSub.RegularPublication.References}
  {inventory clients : YulangClosure.SimpleSub.Store},
  graph.Valid →
    YulangClosure.SimpleSub.RegularCompletion.LawfulStore graph refs
        (inventory ++
          List.map
            (YulangClosure.SimpleSub.Constraint.rename
              (YulangClosure.SimpleSub.RegularPublication.publicationTransport n count afterUse q))
            clients) →
      YulangClosure.SimpleSub.ScopedPublication.BoundsBounded n bounds →
        YulangClosure.SimpleSub.ScopedPublication.InactiveImages n beforeUse afterUse q →
          YulangClosure.SimpleSub.ScopedPublication.StoppedClosed
              (List.map (YulangClosure.SimpleSub.ScopedPublication.Bound.rename q) bounds) afterCap →
            (∀ (k : YulangClosure.SimpleSub.Kind) (i : Nat), afterCap k i = Bool.false → afterUse k i = Bool.false) →
              (∀ (use : Nat), use ∈ uses → use < count) →
                (∀ (clause : YulangClosure.SimpleSub.Constraint),
                    YulangClosure.SimpleSub.ScopedPublication.Published n
                        (List.map (YulangClosure.SimpleSub.ScopedPublication.Bound.rename q) bounds) afterCap afterUse
                        (List.map (YulangClosure.SimpleSub.ScopedPublication.Row.rename q) roots) uses clause →
                      clause ∈ inventory) →
                  have result :=
                    YulangClosure.SimpleSub.RegularCompletion.completedStore graph refs
                      (inventory ++
                        List.map
                          (YulangClosure.SimpleSub.Constraint.rename
                            (YulangClosure.SimpleSub.RegularPublication.publicationTransport n count afterUse q))
                          clients);
                  ∀ {events : List YulangClosure.SimpleSub.Occurrence} {ref : Nat → Nat → Prop} {birth : Nat → Nat}
                    {last : YulangClosure.SimpleSub.Regular.ConstraintState}
                    {certificate : YulangClosure.SimpleSub.Regular.Certificate},
                    YulangClosure.SimpleSub.Regular.ConstraintHistory result.fst ref birth
                        { obligations := result.snd, occurrences := events } last →
                      YulangClosure.SimpleSub.Regular.accepts result.fst certificate last.obligations = Bool.true →
                        result.fst.Valid ∧
                          YulangClosure.SimpleSub.RegularPublication.PublishedSatisfied result.fst
                              (fun k i =>
                                refs k
                                  (YulangClosure.SimpleSub.RegularPublication.publicationTransport n count afterUse q k
                                    i))
                              n bounds beforeCap beforeUse roots uses ∧
                            YulangClosure.SimpleSub.RegularPublication.StoreSatisfied result.fst
                              (fun k i =>
                                refs k
                                  (YulangClosure.SimpleSub.RegularPublication.publicationTransport n count afterUse q k
                                    i))
                              clients
'YulangClosure.SimpleSub.RegularCompletion.completed_publication_with_clients' depends on axioms: [propext, Quot.sound]
```

```text
@YulangClosure.SimpleSub.RegularExtension.Extends.history : ∀ {source target : YulangClosure.SimpleSub.Regular.Graph},
  YulangClosure.SimpleSub.RegularExtension.Extends source target →
    ∀ {ref : Nat → Nat → Prop} {birth : Nat → Nat} {first last : YulangClosure.SimpleSub.Regular.ConstraintState},
      YulangClosure.SimpleSub.Regular.ConstraintHistory source ref birth first last →
        YulangClosure.SimpleSub.Regular.ConstraintHistory target ref birth first last
'YulangClosure.SimpleSub.RegularExtension.Extends.history' depends on axioms: [propext]
```

```text
@YulangClosure.SimpleSub.RegularExtension.Extends.decode_term : ∀
  {source target : YulangClosure.SimpleSub.Regular.Graph},
  YulangClosure.SimpleSub.RegularExtension.Extends source target →
    ∀ {refs : YulangClosure.SimpleSub.RegularPublication.References} {k : YulangClosure.SimpleSub.Kind}
      {term : YulangClosure.SimpleSub.Term k} {i : Nat},
      YulangClosure.SimpleSub.RegularPublication.decodeTerm source refs term = Option.some i →
        YulangClosure.SimpleSub.RegularPublication.decodeTerm target refs term = Option.some i
'YulangClosure.SimpleSub.RegularExtension.Extends.decode_term' depends on axioms: [propext, Quot.sound]
```

```text
@YulangClosure.SimpleSub.RegularExtension.Extends.accepts : ∀ {source target : YulangClosure.SimpleSub.Regular.Graph},
  YulangClosure.SimpleSub.RegularExtension.Extends source target →
    target.Valid →
      ∀ {certificate : YulangClosure.SimpleSub.Regular.Certificate}
        {demands : List YulangClosure.SimpleSub.Regular.Comparison},
        YulangClosure.SimpleSub.Regular.accepts source certificate demands = Bool.true →
          YulangClosure.SimpleSub.Regular.accepts target certificate demands = Bool.true
'YulangClosure.SimpleSub.RegularExtension.Extends.accepts' depends on axioms: [propext, Quot.sound]
```

The complete 291-constant type/axiom inventory is the hashed `audit02.log` above;
`project/AuditCompletion.lean` is the exact reproducible per-origin audit program.
Fresh independent review remains requested through the parent; this producer
does not certify its own mathematical/source correspondence.
