# Mutual recursion: source-root SCC versus native payload SCC

Date: 2026-10-11
Status: independently reviewed bounded conditional operational discriminator; parent gates OPEN.
Baseline: `b08ead8f99f4fc80183381b4923ef1e50681e94e`.
Exclusive lease: this note only. Primary owns review and integration.

## Objective, authority, and exact claim

Audit `my f x = g; my g y = f` constructor by constructor in the native
candidate source route. Discriminate its native payload SCC from the reviewed
semantic Value-root SCC; retained-pair creation is separately classified.
This source spelling
already occurs in `crates/yu-solver/src/lib.rs:23072`, within
`f5d_productive_function_recursion_and_unproductive_names`; its assertions were
read, not run, and are not evidence about the candidate graph snapshot below.

Governing sections are `rules/design-authority.md`, “Authority order”;
`notes/design/2026-10-10-parent-copy-scc-intrusion.md`, “Selected operation and
compiler responsibility” and “Value-reference SCC clarification”; and
`notes/design/2026-10-11-yulang-inference-top-level-principles.md`, §§1–3 and
“Authority and integration”. Research ownership follows `rules/research-lab.md`,
“One semantic baseline, explicit dependency invalidation”, “Writes, artifacts
and review snapshots”, and “Evidence quality and stopping unproductive loops”;
`rules/git-concurrency.md`, “Disjoint-file mode”. The `yulang-proofs` skill's
source-bridge boundary applies; this leaf does not delegate constructive work.

The accepted graph has Value variables as vertices and actual references in
their values as directed edges. Comparison direction, parent metadata and
source dependency SCC membership do not themselves create graph edges.

Claim class: **bounded conditional operational discriminator**, not an
executed witness, all-source theorem, independent review, or intrusion proof.
The reviewed original-root theorem is reused without reinterpretation:
`Rf →src Rg →src Rf` in the selected source-reference relation. Under the
following hypotheses, the Value-row projection of the native payload graph
instead has nontrivial operational SCC `{Ng,Nf}`, while its original definition
roots are not mutually reachable. The raw scanner component also includes the
Function nodes that subdivide this cycle. Thus the SCC relation on those same
actual roots differs from the reviewed semantic relation. This source creates
no retained extrusion pair.

1. Ordinary HIR formation resolves the unique module definitions `f` and `g`,
   and collection selects `collect_candidate_mode(..., true, true)` / its
   native candidate source route, without test mutations or prior session state.
2. Checked identity/allocation operations and the ordinary source actions and
   their owned native drains complete successfully. This is a control-flow
   hypothesis, not a measured acceptance/termination result.
3. The snapshot is after both member schedules finish, before any additional
   external source uses or manually supplied constraints. It uses precisely
   the constructor-owned bound/Function representation inspected below.

Operational edges below are derived from actual inserted endpoints and
immutable Function child fields. They are **not** promoted to semantic
source-value reference edges. The current scanner follows these payload edges;
the inspected constructors do not establish that they are the selected semantic
relation. The initial draft conflated those relations; primary feedback
corrected that classification before freeze. The new delta is the concrete
same-root SCC discriminator, not another proof of the semantic mutual SCC or
another root-copy exclusion.

## Prior results reused and novelty boundary

The primary supplied five additional dependencies after the initial source
pass. Their exact claim/review boundaries are preserved:

- `notes/theory/2026-10-11-mutual-recursive-value-scc-proof.md` and
  `notes/progress/2026-10-11-mutual-recursive-value-scc-source-trace.md`:
  independently reviewed bounded source-to-original-root result `Rf ↔src Rg`;
  occurrence factorization and scanner equivalence/inequivalence remain open.
- `notes/theory/2026-10-11-mutual-recursion-parent-copy-proof.md`: reviewed
  conditional nested-source allocation trace, with copy-owned semantic
  references and scanner correspondence open.
- `notes/theory/2026-10-11-mutual-recursion-copy-scc-bridge.md`: frozen
  unreviewed bounded constructor exclusion of direct mutual-root extrusion;
  capture boundary zero is distinct from a live level-zero extrusion target.
- `notes/progress/2026-10-11-extrusion-copy-source-owner-audit.md`: frozen
  unreviewed retained-origin audit; origin recovery does not prove the
  copy-owned Value/reference law.

The new evidence below is the complete relevant native payload adjacency and
its disagreement with the reviewed root SCC on the original retained root
identities. The no-pair observation corroborates prior work and adds no new
parent-gate progress.

## Source objects, levels, and scheduling

Names below are ownership descriptions, not guessed printed row ordinals:

| Object | Owning source identity | Live level |
| --- | --- | --- |
| `Rf`, `Rg` | definition Value roots of `f`, `g` | 1 |
| `Lf`, `Lg` | root Lambda expression Value rows | 1 |
| `Ng` | Name occurrence `g` in `f`'s body | 1 |
| `Nf` | Name occurrence `f` in `g`'s body | 1 |
| `X`, `Y` | formal parameter rows of `x`, `y` | 1 |

HIR formation emits each formal's Lambda with its actual body index at
`crates/yu-hir/src/module/local_source.rs:286–317`. Name lookup first checks
lexical bindings, then resolves a unique module definition at `:636–656`.
Neither `g` nor `f` is shadowed by its body's formal parameter here.

Collection allocates a separate definition root at
`crates/yu-solver/src/lib.rs:993` / `:1676–1696`, and selects the HIR-owned
candidate source at `:1125–1135`. Expression components and formal recipes are
allocated at `candidate_source.rs:187–201`; a module Name keeps its expression
Value endpoint (`:211–217`), rather than becoming the target definition root.
Resolved Name actions retain the module use at `:375–378`, and its use/root
component positions remain distinct at `lib.rs:1300–1324`.

`try_new` initializes every collected Value row to level 1
(`lib.rs:10053–10064`) and every formal row to level 1 (`:10089–10099`). Source
traversal starts at 1 and preserves that level through Lambda and body
(`candidate_source.rs:254–286`); only Block initializers increment it
(`:288–295`), and this source has no Block. Installed level maps at `:532–541`
therefore preserve the displayed levels. `start_candidate_graph` at
`candidate_scheme.rs:675–689` creates graph state without lowering roots.
The later capture boundary 0 at `:897` is a generalization boundary, **not**
a write of live root level 0.

Both module roots and both internal uses are active before member source
schedules execute (`candidate_scheme.rs:842–882`). `Action::Module` recognizes
an active internal use (`candidate_source.rs:672–676`), and
`route_candidate_open_use` validates both roots and calls `route_internal`
(`candidate_scheme.rs:938–944`). `route_internal_inner` requests target root
as lower endpoint and distinct occurrence row as upper endpoint
(`lib.rs:15765–15782`); `route` actually constrains that pair at `:16888`.

## Actual constructor and replay derivation

Write `Ff = Function⁺(X, entry_f, return_f, Ng)` and
`Fg = Function⁺(Y, entry_g, return_g, Nf)`, retaining the actual Effect ports
but omitting them from the Value edge lists. Lambda admission obtains the
formal and body handles at `lib.rs:11233–11260`, allocates its Effect ports at
`:11267–11338`, and constructs this Function at `:11342`.
`term.rs:203–208` owns its four fields; `:1126–1144` validates and interns those
very child handles. The result field is the actual Name occurrence handle.

For equal-level row/row admission, `candidate_apply_value` chooses the lower
endpoint as owner and the upper endpoint as its stored upper bound
(`candidate_extrusion.rs:816–830`). For Function/row admission it chooses
the receiving row as owner and the actual Function as lower bound (`:822`).
The physical insertion happens at `:464–501`; the endpoint held by that
owner's payload determines the outward operational incidence. This alone
establishes no semantic source-reference edge. Candidate dispatch
uses these owners and bypasses legacy paired adjacency/aging
(`lib.rs:13744–13759`).

Taking `f`'s schedule first, the relevant finite steps are:

1. The internal `g` occurrence compares `Rg <: Ng`. Equal levels select
   `Rg.upper += Ng`, establishing the operational incidence `Rg →op Ng`.
2. Lambda admission inserts `Ff` into `Lf.lower`, establishing `Lf →op X` and
   `Lf →op Ng` through its Function fields.
3. The final source Link compares `Lf <: Rf`
   (`candidate_source.rs:493`, `:665–668`). It stores `Rf` in `Lf.upper`,
   establishing `Lf →op Rf`. Replay compares the already stored `Ff` with that
   upper `Rf`, then installs `Ff` into `Rf.lower`. Thus `Rf →op X, Ng`.
4. The internal `f` occurrence in `g` compares `Rf <: Nf`, storing
   `Nf` in `Rf.upper`. Replay installs the existing `Ff` into `Nf.lower`.
   Its actual result field establishes **`Nf →op Ng`**, and its argument field
   establishes `Nf →op X`.
5. Lambda admission installs `Fg` in `Lg.lower`; final Link stores `Rg`
   in `Lg.upper`. Replay installs `Fg` into `Rg.lower`, then against its
   existing upper `Ng` installs `Fg` into `Ng.lower`. Its result field
   establishes **`Ng →op Nf`**, and its argument field establishes `Ng →op Y`.

These replays are actual native owning operations, not assumed closure of
stored comparisons. `candidate_replay_bound` reads opposite bound payloads
and constructs precisely those Function/row tasks
(`candidate_extrusion.rs:763–803`). Bound admission first attaches a retained
relation to the exact bound key (`candidate_effect.rs:426–429`;
`candidate_context.rs:2819–2855`). The newly encountered lower/upper fibers
produce replay children at `candidate_context.rs:2927–2970`; the operation
owns their common task at `:2981–2982`. Queueing that task at `:1837–1841`,
`:3098–3099` feeds the native drain; the ordinary drain pops its worklist at
`lib.rs:12243`. Successful completion of that drain is explicit hypothesis 2.
No pre-existing identical dependency suppresses these first required
Function/row insertions in the empty initial session. Reversing member order
exchanges `f` and `g` and yields the same final payload list.

The relevant completed payloads and projected immediate operational incidences
are:

| Owner | Lower Value payload | Upper Value payload | Immediate operational targets |
| --- | --- | --- | --- |
| `Lf` | `Ff` | `Rf` | `X`, `Ng`, `Rf` |
| `Lg` | `Fg` | `Rg` | `Y`, `Nf`, `Rg` |
| `Rf` | `Ff` | `Nf` | `X`, `Ng`, `Nf` |
| `Rg` | `Fg` | `Ng` | `Y`, `Nf`, `Ng` |
| `Nf` | `Ff` | empty | `X`, `Ng` |
| `Ng` | `Fg` | empty | `Y`, `Nf` |
| `X`, `Y` | empty | empty | none |

All arrows in the preceding native derivation mean **operational payload
incidences `→op`**, including the listed Function-port references. No semantic
source edge is inferred from insertion or propagation. Consequently
The **projection of the operational payload graph onto Value rows** has
nontrivial SCC `{Ng,Nf}`. Roots and root Lambda rows feed it but have no
incoming payload incidence from its members, so those rows are outside that
component. In the scanner's unprojected graph, Function nodes subdivide these
edges; its corresponding raw component also contains `Ff` and `Fg`
(`candidate_intrusion.rs:391–413`, `:445–468`). Function subdivision preserves
reachability between Value rows, but not literal SCC membership before
projection. Effect branches have no return edge to Value in this
representation. These operational statements do not assign semantic values or
source-reference edges to `Ng,Nf`.

## Three relations and the same-identity discriminator

| Relation | Evidence | Bounded conclusion |
| --- | --- | --- |
| Definition/Name dependency relation | `DefinitionUse.parent,target`, source scheduling | The two definitions form a scheduling SCC; this alone proves no Value SCC |
| Selected semantic source-reference relation on actual Value roots | Reviewed source-owned Name and joint root-to-row certificate | `Rf →src Rg →src Rf`; occurrence facades remain distinct identities |
| Native bound/Function payload adjacency | Actual insertion and Function fields, followed by the scanner | `Ng ↔op Nf`; original `Rf,Rg` are not mutually reachable |

The smallest discriminator is the pair of actual original root rows `(Rf,Rg)`
in this two-definition source. The reviewed semantic certificate puts them in
the same SCC: the value owned by `f` contains a Name resolving to `g`, and the
value owned by `g` contains a Name resolving to `f`; the joint root map supplies
their actual Value identities. This uses the accepted source interpretation,
not subtype direction or a dependency SCC as an edge.

The first source-to-native mismatch is at each recursive Name. Native Lambda
construction retains a distinct Name occurrence row `Ng` as its Function
result port (`candidate_source.rs:375–378,445–458`; `lib.rs:11342`). The
module-use route separately admits `Rg <: Ng` (`candidate_scheme.rs:938–944`;
`lib.rs:15765–15782`); at these equal levels the bound writer stores `Ng` on
`Rg` (`candidate_extrusion.rs:816–830`), giving operational incidence
`Rg →op Ng`. It installs no `Ng →op Rg` payload reference. Inferring the
semantic edge `Ng →src Rg` solely by reversing this comparison would violate
the accepted edge definition. The same construction holds for `Rf` and `Nf`.
This identifies where the reviewed
source Name-reference edge fails to transfer to the current payload graph; it
does not by itself prescribe a representation or implementation repair.

In the displayed complete relevant native payload table, the only Value rows
reachable from `Rf`, apart from itself, are `X,Ng,Nf,Y`; none points to `Rg` or
`Lg`. Symmetrically the rows reachable from `Rg` exclude `Rf`. Thus `Rf,Rg`
are in different operational SCCs. This compares the same actual identities,
without relabeling `Ng` as `Rg`, `Nf` as `Rf`, or quotienting distinct rows.

Conditional on successful completion of the finite source/drain steps,
**the current scanner's underlying adjacency has a different SCC relation on
the original Value roots from the accepted semantic source-reference relation**.
This refutes the candidate exact same-identity SCC-correspondence premise on
this bounded domain. It preserves, and depends on, the reviewed root proof.
The prior native payload map cannot be promoted to that exact source-graph
equivalence solely from actual bound/Function child ownership.

The approved intrusion operation consumes the selected semantic Value
reference SCC relation, which includes `Rf,Rg` together for this source. The
scanner would not recover their same-root qualification from its payload graph.
There is no retained pair here, so the scanner early-exits and no missed
required parent/copy equality or incorrect merge is demonstrated. A weaker
equivalence restricted to eligible pairs, or a proved identity transport that
preserves their qualification, is neither proved nor refuted by this pair-free
example. That bridge must be stated separately and cannot silently identify
distinct occurrence and definition rows.

## Extrusion and retained-pair classification

Function/row native dispatch calls positive extrusion at the receiving row's
live level (`lib.rs:12415–12426`). Every Value port above is level 1 and each
receiving row is level 1. The row branch returns the original endpoint when
`original_level <= target` (`candidate_extrusion.rs:90–94`), before allocation
or retention. The Function traverses its actual four ports at `:224–253` and
returns the original Function when none changes at `:325–340`. The freshly
allocated Lambda Effect ports are likewise level 1, so they cause no retained
pair either. Row/row dispatch adds no extrusion call on the candidate route.

Copy allocation and the sole inspected retention call require the strict
opposite branch (`candidate_extrusion.rs:112–123`). That branch is never
reached in this finite trace. Capture at boundary 0 reads the live graph;
it does not extrude it. There are no external uses in the selected source and
no fresh-use restoration is needed to build the cycle.

Thus the extrusion pair inventory starts and stays empty, and no pair has
endpoints in either the reviewed source-root SCC or the operational Name SCC.
This corroborates the prior copy-SCC bridge and is not new parent-gate progress.
Indeed `settle_candidate_intrusion` skips SCC scanning
when parents are empty (`candidate_intrusion.rs:370–373`). The operational graph has the
derived SCC whether or not that optimization scans it. No equality merge
or intrusion event is claimed. Adding a fictional parent record for `Ng,Nf`
or interpreting `Rf <: Nf` as a reverse reference would invalidate the audit.

## Evidence limits and frozen dependencies

This is a native payload derivation using a reviewed semantic source premise;
there is no executable oracle, checker,
seed/range enumeration, mutation run, build, test, or compiler invocation.
The original reference baseline is
`/home/momota1029/rust/simple-sub-reference` at
`9bae772624c23b52a93c1b226157e16898b4d9db`, rechecked by `git rev-parse`.
Its earlier characterization was read as background, but this derivation's
edge and replay conclusions come from Yulang constructors. The reference
provides no independent intrusion oracle or validation of Yulang effects.

Commands: bounded `cat`, `rg`, `rg --files`, `nl -ba ... | sed -n ...`,
read-only `git rev-parse`, `git status --short`, dependency-scoped
`git diff b08ead8f99f4fc80183381b4923ef1e50681e94e -- <named dependencies>`,
and `sha256sum`. The dependency diff was empty; baseline HEAD was unchanged.
One initially guessed HIR path did not exist and was replaced by the actual
`crates/yu-hir/src/module/local_source.rs` locator; a broader search also
reported absent `spec/`. A whole `tasks/current.md` capture was truncated;
its relevant mutual-SCC sections at 10006–10050 and 10225–10245 were read
separately. Search coverage is only the named constructors and this source,
not all HIR/compiler paths.

One lightweight shell/tool process per read batch, at most three independent
lightweight reads concurrently; zero Cargo/build/test/probe processes,
benchmark samples, children, or Git mutations. The 30-minute wall budget was
not exhausted; exact elapsed time, CPU and peak RAM were not measured.
Runtime acceptance, unconditional successful drain progress, failure/retry
reuse, later external uses, source completeness, full Call, soundness,
principality, intrusion adequacy, and production cutover remain unverified.
The derivation fails if source resolution changes, a relevant action/drain
fails, another constructor mutates these rows, live levels change, or the
inspected payload representation ceases to retain the listed child handles.

SHA-256 frozen dependencies:

```text
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  crates/yu-hir/src/module/local_source.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df  crates/yu-solver/src/candidate_effect.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987  crates/yu-solver/src/candidate_context.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
75506948ec8043c9d5b4d0369ae94ed31c940aae0bc930ae1099bc1c758bb615  crates/yu-solver/src/term.rs
2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0  notes/design/2026-10-10-parent-copy-scc-intrusion.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
8dd8eb55ac9d9df75980182cb5483f9394674a94f77c9d70d12f89b5be0d24e6  notes/theory/2026-10-11-simple-sub-value-reference-scc.md
66f8f068c453d491d45c09fe22a27f7a63ea5a31ca200b4cb15c4c21f4dbaad0  notes/progress/2026-10-11-native-value-reference-scc-map.md
88ce1aa652f8d289955b3088e683f1e8d6a8c5c3d4d49258d8f9c390ed9f3dbf  notes/progress/2026-10-11-source-qualified-value-parent-copy-scc.md
332f757481af278e533f0e5d7eda2b3aa004e75d54f1d3e48c77b8f76d5a786d  notes/theory/2026-10-11-mutual-recursive-value-scc-proof.md
d198a3392cee6907b37a3856c3582b05e9bf7ea490876d1a5a3cf38a5d47507a  notes/theory/2026-10-11-mutual-recursion-parent-copy-proof.md
2e797c0004a38ddd2f2c4dd7e75caf04f85c9fd46dcfe2b92ae386e8adf24f23  notes/theory/2026-10-11-mutual-recursion-copy-scc-bridge.md
09ab6c1bbefb495596b795cebff03fa14bb18b434e66c39ddcb4aa249c653bb1  notes/progress/2026-10-11-mutual-recursive-value-scc-source-trace.md
81f5668eb4a66a624cbc82e12af026689bf1b82d97b74ca17c2e6bd9abbd3cd9  notes/progress/2026-10-11-extrusion-copy-source-owner-audit.md
```

Recommended next action: independently review this same-root SCC discriminator
against the reviewed source-root certificate and exact native payload writers.
If accepted, the primary should adjudicate the scanner-correspondence gap and
require its owning source/consumer bridge; keep parent/copy adequacy OPEN.
Do not dispatch another equivalent mutual source or level-only pair probe.

## Commit packet

- Exact leased path:
  `notes/progress/2026-10-11-mutual-recursion-value-scc-source-audit.md`.
- Baseline: `b08ead8f99f4fc80183381b4923ef1e50681e94e`.
- Changed dependency hashes: none relative to this pinned baseline.
- Review: independent `compiler_referee` review found one minor graph-domain
  precision issue and one wording issue; both were repaired and delta-reviewed
  closed. The final note remains a conditional operational discriminator. No
  theorem or production gate closed; the producer does not certify its output.
- Checks already run: narrow source/constructor/replay reads, baseline-scoped
  dependency diff, baseline/reference identity and SHA-256 capture. No tests,
  builds, probes, Oracle calls or compiler execution.
- Proposed checkpoint message:
  `research: distinguish mutual source-root and native payload SCCs`.
- Shared-record deltas left to primary/curator: preserve reviewed semantic
  `Rf ↔src Rg`; record conditional different native root SCCs and operational
  `Ng ↔op Nf`; retain pair-qualified correspondence and parent/copy witness
  gates OPEN. No shared task, index,
  authority or theory map was edited.
