# Mutual recursion: extrusion identity and the first copy-reference obstruction

Status: frozen, unreviewed bounded source audit and conditional operational derivation
Parent claim: OPEN; no source parent/copy SCC or scanner conformance established
Baseline supplied by primary: `670d1572e`
Exclusive output lease: this file

## Frozen objective and authority

Extend the independently reviewed original-root witness

```yulang
my f x = g;
my g y = f
```

to an actual extrusion-created Value identity. The required conclusion is a
source-qualified inference history with a retained, distinct Value copy `C`
and its actual retained parent `P`, together with source-owned reference paths
`P →* C` and `C →* P` before the equality whose qualification is being proved.
Every identity and map must come from that single source/artifact/history.
Neither existentially chosen row assignments nor identifying a copy with a
binder can satisfy this conclusion. The general parent obligation over all
supported programs, histories and retained pairs remains unchanged.

Authority: `notes/design/2026-10-10-parent-copy-scc-intrusion.md`, **Selected
operation and compiler responsibility**, **Value-reference SCC clarification**,
and **Retained boundary**; and
`notes/design/2026-10-11-yulang-inference-top-level-principles.md`, §§1–5 and
**Evaluation**. The direct user definition fixes Value variables as vertices
and references in their values as edges. Comparison judgments, bound-storage
direction and parent metadata alone supply no edges. Native inference, complete
Call, effect hygiene, soundness and required principality are retained.

Dependency: the reviewed
`notes/theory/2026-10-11-mutual-recursive-value-scc-proof.md` establishes
`F → G → F` for the original source's two distinct actual module root rows.
Its quantification is over successful lowering/session construction; its
conclusion covers those original roots. It expressly supplies no ownership or
reference transport for occurrence rows, fresh uses or extrusion copies.

One attempted source extension is fixed for this audit:

```yulang
my f x = { my inner z = g z; g };
my g y = f
```

`f,g` remain distinct module definitions; `x` belongs only to `f`, `y` only to
`g`, and `z` only to the initializer Lambda of the local `inner` in `f`'s
block. The nested function use is `g z`. The block's result is a separate Name
occurrence `g`. There are no annotations, operations or shadowed module names.
The local initializer has its own owner; its `g z` is not silently included
in the surrounding block-result owner's references.

This exact extension has not been parsed, lowered or executed in this packet.
No independently reviewed artifact establishes its successful source path or
whole inference result. The clauses below therefore freeze two explicit
guards: **H_source**, that the exact extension lowers to the displayed
LocalSource forms and resolutions; **H_prefix**, that its ordinary private
source driver reaches the specified initial call/replay prefix without an
availability error or identity-changing operation. These are unestablished
source/history premises, not facts inferred from successful storage. The
derivation is conditional and is not an authentic parent/copy SCC witness.

## Original roots and the new initializer owner

For the original source, the reviewed result `F ↔ G` is used without another
proof attempt. For the extension, under H_source, lexical/module lookup in
`crates/yu-hir/src/module/local_source.rs:636` resolves both `g` occurrences to
the unique module `g`, `f` in `g` to module `f`, and `z` in `g z` to the local
Lambda parameter. Local binding and parameter construction are at `:738` and
`:757`; the owned Block is constructed at `:809`, and Apply at `:556`.
Collection selects this LocalSource route at `crates/yu-solver/src/lib.rs:1125`.

Use the single actual root map from the reviewed note:
`β(d) = session.live_components[batch.root_component_positions[batch.definitions[d.ordinal].root].component].ordinal`.
The separate result `g` preserves the intended root-reference pattern, while
the Name `f` remains owned by `g`. Establishing `F → G` for this new Block
still requires its source-value ownership clause: the earlier candidate note's
Block/result clause is proposed, not adopted Authority. H_source supplies
forms and resolutions only. Accordingly no new Block root SCC is claimed
here, and the original reviewed theorem certifies only the original source.
The new local initializer's root/parameter/Name rows are separate identities;
none is `F`, `G`, or a source spelling used as a substitute for a row.

## Conditional native prefix: exact levels, routing and copy allocation

The following trace names constructor outputs, not prescribed numeric row IDs.
Let `U` be the actual Value row of the callee Name `g` in `g z`, `Z` the
parameter row for `z`, and `R` the actual result Value component of that Apply.

1. All collected Value components and parameters initially receive level one
   (`lib.rs:10047`, `:10092`). Source planning starts at level one
   (`candidate_source.rs:254`). A Lambda preserves its current source level
   (`:270`), whereas a Block initializer receives `level + 1` (`:288`, `:299`).
   Thus the local initializer Lambda, its `z`, callee Name and Apply result
   receive level two in the plan. `initialize_candidate_source_levels`
   (`:532`) installs those levels on the actual live rows. Definition roots
   retain their initial level one. Consequently, before a modifying event,
   `level(G)=1` and `level(U)=level(Z)=level(R)=2`. This is a source-constructor
   derivation under H_source, not a choice of levels after seeing a copy.

2. Definition SCC members are ordered by their actual definition ordinals
   (`scc.rs:357`); the graph-plan driver installs both active roots/internal
   uses before executing member schedules (`candidate_scheme.rs:869`, `:880`).
   In this source order, `f`'s schedule precedes `g`'s. Planning visits the
   local initializer before its installation and the Block result
   (`candidate_source.rs:288`). Apply visits callee and argument before its
   final action (`:264`, `:395`); the module Name emits its exact
   PendingDefinitionUse and Module action (`:376`).

3. Execution of that Module action selects its actual DefinitionUse
   (`candidate_source.rs:672`). `route_candidate_open_use`
   (`candidate_scheme.rs:938`) validates the active parent/target and calls
   `route_internal`; its actual endpoints are `G <: U`
   (`lib.rs:15765`). Both rows remain distinct. Since `2 > 1`, the candidate
   row/row owner selects `(U, Positive, G)`
   (`candidate_extrusion.rs:815`), recording `G` as a lower of `U`.
   This storage is an operational fact; it is not the semantic edge `U → G`.

4. Apply construction validates the same registered source input, reads `Z`
   through its parameter endpoint and `R` through its actual component, and
   emits `U <: D`, where `D` is its four-port NegativeFunction
   (`shadow_apply.rs:1304`, `:1340`, `:1362`, `:1400`). The effect ports are
   retained exactly; neither is erased or asserted to prove complete Call.
   Extruding `D` to `U`'s level two creates no level-decreasing Value copy.
   Candidate insertion puts `D` on `U`'s upper side and calls replay
   (`candidate_extrusion.rs:829`).

5. The opposite-bound loop reads the retained lower `G`, forms `G <: D`,
   and constructs the actual replay dependency/child
   (`candidate_extrusion.rs:770`, `candidate_context.rs:2911`). This is more
   than merely naming a stored constraint: `candidate_context_drive_replay`
   (`:3110`) calls the no-provenance consumer (`:3089`), which enqueues the
   child item. The ordinary drain is `run_candidate_typed_drain`
   (`lib.rs:12155`); its transport stage pops the worklist (`:12234`), then
   context and dispatch execute it (`:12267`, `:12274`). The initial source
   and empty-weight replay contexts are IDENTITY (`candidate_context.rs:2489`,
   `:2956`), so context execution does not consume this Value task (`:2753`).
   H_prefix still guards successful arrival through this owner chain; this
   audit is not a termination or all-replay-completeness proof.

6. Dispatch of the newly admitted `G <: D` is the actual structural-to-row
   extrusion trigger: NegativeFunction `D` is extruded at `level(G)=1`
   (`lib.rs:12429`). The argument child flips polarity, so the `Z` port is
   visited positively at target one (`candidate_extrusion.rs:231`); the
   result `R` is visited negatively (`:247`). Because `level(Z)=2 > 1`, the
   row Visit allocates `C = fresh_value_at_level(1)` (`:112–120`), then calls
   `retain_extrusion_parent(C,Z,Positive,1)` (`:121`). Fresh allocation uses
   the next checked row ordinal with empty bounds (`lib.rs:10156`), rather
   than a binder or a root map. Parent retention records exactly those actual
   rows (`candidate_intrusion.rs:178`, `:214`). This gives the guarded
   creation pair `(C,P=Z)`, with `C ≠ P` at allocation and `level(C)=1`.
   A separate result copy is not interchangeable with this chosen pair.

7. Extrusion memoizes its joint `(endpoint,polarity,target)` map before
   traversing selected bounds (`candidate_extrusion.rs:122`). It installs a
   one-sided link at the original `Z` (`:123`), transports selected bounds
   onto `C` (`:312`), and reconstructs `D`'s port with `C` (`:324`, `:343`).
   Bound-origin transfer records its actual operation, polarity and target.
   This traces operational copy identity/transport only. It does not establish
   that an owned source value has been constructed for `C`, or that any
   source reference has been retargeted to `C`.

No subsequent local publication, fresh use of `inner`, complete source drain,
successfully inferred scheme, or scanner merge is assumed. The copy creation
above is a conditional finite prefix, not evidence that the exact source ran.

## First missing source-reference premise and stopping point

The requested source graph has no supplied construction clause that makes a
reference occurrence denote `C`, or assigns `C` its own value with transported
references. Source lookup supplies the real parameter target `Z`; `C` is
allocated later by extrusion. Neither `β` for module roots nor the parameter
recipe map maps an owned source occurrence to this new row. Extrusion's local
map retargets type Function ports and selected bound payloads. That fact alone
does not prove the source-reference ownership/transport clause needed here.

In particular, the operational link installed at `Z` is not a proved source
edge `P → C`. The stored reconstructed Function port is not a proved owned
source reference into `C`. Parent metadata supplies neither direction. There
is also no source-owned outgoing reference from `C` with which to derive
`C →* P`. The reviewed `F ↔ G` SCC supplies no incidence connecting this
fresh identity to either root. No path containing `C` follows from that SCC.

Thus there are two explicit unresolved frontiers: the exact new program's
H_source/H_prefix are not independently established, and even granting them
the first semantic bridge is **copy-owned value/reference construction and
transport at the extrusion owner**. Granting source acceptance or successfully
observing this Parent record would remove the first frontier, but would not
remove the second. Conversely, this failure to derive an edge is not a proof
that source references to copies are impossible or that intrusion is redundant.
This packet stops here; it supplies neither a counterexample to the selected
operation nor a source-qualified retained pair in one SCC.

The scanner is a separate consumer: `candidate_intrusion.rs:389` traverses
both stored row sides and structural ports, including Effect endpoints, then
tests retained pairs at `:478`. Its own adjacency may contain operational
paths. Establishing equality between that adjacency (or its Value projection)
and the user's source Value-reference relation requires the missing source
bridge; it is not part of the guarded allocation derivation.

## Proof-obligation economy and one next action

The preceding reviewed candidate relation and original-root proof already
leave copy ownership/transport unresolved. This bounded constructor audit
localizes the same premise at `candidate_extrude`, rather than adding another
conditional graph pattern. No further equivalent SCC lemma is proposed.

Under `rules/compiler-engineering.md`, **Natural compiler behavior and
proof-obligation economy**, reconstructing source-reference ownership from
rows/bounds is D reconstruction debt. The underlying fidelity required to
justify qualifying intrusion remains A/B; this audit does not reclassify or
retire the parent gate. H_source/H_prefix are separate executable/source
coverage duties. The source resolution and extrusion constructors are the
owners that already know, respectively, the original reference target and
the actual copy map.

Next action for the primary: assign the owning source/extrusion bridge that
establishes what value and references `C` actually owns and how occurrences
denote its actual identity, with source-prefix validation kept explicit. Test
whether existing retained construction evidence suffices before authorizing a
certificate change; do not adopt a new relation or add source restrictions to
make this witness close. The parent gate remains OPEN.

## Checks, dependencies and handoff

Checks: read the governing rules, skill, registered prover configuration,
reviewed root proof and direct source owners with `cat`, bounded `rg`/`sed`,
and `sha256sum`; reread this leased note. No builds, tests, Oracle, executable
probe, code edits, delegation or Git mutation. Startup accidentally invoked
read-only `git rev-parse HEAD` and `git status --short` despite the packet's
no-Git instruction; this was reported immediately to the primary, and no
subsequent Git command ran. The supplied baseline is retained; baseline
comparison/integration remains primary-owned.

One bounded derivation. At most four lightweight read processes were concurrent
at startup; later reads and the single artifact write were sequential. Zero
build/probe processes and zero measurement samples. CPU/RAM/wall time were
not measured. Requested route: normal Sol/high. Observed model/effort metadata:
unknown; configuration read is not runtime evidence. No Astra escalation.

Inspected direct dependency SHA-256 snapshot:

| Path | SHA-256 |
|---|---|
| `notes/theory/2026-10-11-mutual-recursive-value-scc-proof.md` | `332f757481af278e533f0e5d7eda2b3aa004e75d54f1d3e48c77b8f76d5a786d` |
| `notes/theory/2026-10-11-value-reference-scc-source-bridge.md` | `1bc8b29b7b1f3995bf3adedf604fe15db80be8e4bc8f1d0771644a449d086aef` |
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `crates/yu-solver/src/shadow_apply.rs` | `230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6` |
| `crates/yu-solver/src/scc.rs` | `3cfce9acfddd77838398cd95cd13c053f71f27a8367b07175a83c825d68a8df8` |

No dependency was changed by this leaf. Changed dependency hashes relative to
the supplied baseline were not computed; the primary must revalidate the
snapshot. This is unreviewed research and requires fresh independent review.
Source execution, copy-owned references, scanner equivalence, generalization,
complete Call, effects, soundness, principality and production/cutover remain
unverified. No shared task/index/theory-status record was edited.

Commit packet: exact lease
`notes/theory/2026-10-11-mutual-recursion-parent-copy-proof.md`; baseline
`670d1572e`; only this new research note changed; dependency snapshot above,
baseline deltas unknown; frozen unreviewed conditional/source audit, parent
OPEN; read/hash checks already run, no tests/builds. Proposed message:
`research: locate mutual recursion copy reference ownership obstruction`.
Shared-record delta left to primary/curator: retain the reviewed original-root
SCC result, record this guarded nested-copy constructor route and its source
qualification guards, and leave source copy transport/scanner/parent-pair SCC
and dependent inference gates OPEN.
