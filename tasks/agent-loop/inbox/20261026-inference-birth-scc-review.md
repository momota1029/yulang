# Independent review: birth-level SCC qualification

Revision: r1. Reviewer: `/root/call_entry_review`, a fresh non-author for this
proof. Requested model/effort: inherited; separately observed runtime metadata:
UNKNOWN. No configured-role execution is claimed. No children or contribution
to the reviewed construction/repairs. Primary-supplied baseline:
`0f6346a2de0a8bff863f41d487eb4b29cf8fb5f3`; no Git command was run.

## Verdict

**CLEAN in the stated finite-graph qualification scope.** No blocking, major,
or minor finding. Recommend accepting the frozen graph theorems with their
explicit premises and source/native boundaries. This is not a proof of
`SourceProblem.InferenceSoundness`, not a correctness proof of native Kosaraju,
and not an implementation or Rust-fixture review.

| Frozen reviewed input | Verified SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/BirthLevelSCC.lean` | `2c76b82d4dc85a4bf4c122731ba014b07df4c863ad679e9a795a57e6546243f0` |
| `tasks/agent-loop/inbox/20261026-inference-birth-scc-proof.md` | `187f80c5ec6eb65dd0e227616f3656b28abb5d129599741d8cab6b796dd84544` |

Both assigned hashes matched at intake and after inspection. All eight entries
in `inference-birth/input-hashes.json` match current source/configuration bytes.
The isolated module, `Contracts.lean`, pin, lakefile, and manifest match the
repository byte for byte. Contracts imports only `Init`; the new module imports
only Contracts.

## Authority and actual contract

Read the October 24 authoritative birth-level design in full, the October 11
inference principles in full, and the relevant BL1/helper and local-equality
sections of the October 24 theory note. The later design explicitly supersedes
the older global-SCC qualification while preserving actual occurrence/pair
identity, source reference edges, and the remaining inference obligations.

`Contracts.lean:80–97` defines `LevelPath` so every edge endpoint lies at one
fixed immutable birth level, with a birth-qualified zero-edge path.
`Qualifies ref birth event` is exactly two such paths at the same level for
the event's origin and receiver. The event also retains its id and complete
signed pair list. The new module uses this existing predicate directly; it
does not redefine qualification as the executable answer.

`Contracts.lean:127–154` separately defines inference soundness, source-scoped
coverage, native correspondence, and inference termination. None of those
definitions is a proved instance, and this module does not supply such an
instance.

## Mathematical and source-correspondence checks

1. **Executable finite reachability is established constructively.**
   `BirthLevelSCC.lean:70–142` defines a finite pivot-closure specification
   over Boolean edges. Soundness constructs finite paths from Boolean results;
   `finiteReach_join` proves closure at a listed intermediate vertex;
   completeness follows by induction on finite paths using the explicit
   `covers : forall v, v in vertices` premise. Duplicates do not invalidate the
   argument. Decidable equality and a finite covering enumeration remain inputs.
   There is no assumed reachability oracle or path-completeness law.

2. **Filtering applies to every traversed edge, and hence every vertex.**
   At `:39–68,144–194`, `SameLevel` conjoins an original edge with endpoint
   birth equality, and `filteredEdge` implements that predicate. The two
   conversion lemmas connect its paths to the actual `LevelPath`; the reverse
   path starts at the level obtained from the first path's target. Thus
   `finite_qualifies_iff` proves executable eligibility equivalent to the
   unchanged `Qualifies` for the same supplied occurrence. This is stronger
   than checking endpoint births after computing global SCCs. No operation
   deletes cross-level edges from the original edge parameter.

3. **Helper filtering is justified by local edges, not assumed for paths.**
   `:198–220` separates semantic Values and helpers with `Sum V H`.
   `planningLevel` agrees with birth only on semantic Values; helpers have a
   separate level map. `PlanningInvariant` at `:204–209` requires every edge
   whose target is a helper to preserve planning level. It imposes no such
   restriction on edges whose target is a semantic Value. `Incidence` is a
   nonempty path with only helpers internally.

   At `:245–265`, induction on `Incidence` derives filtered incidence from
   that local invariant and endpoint equality. Each helper step inherits the
   required equality; the final edge into the semantic target uses the endpoint
   equation. In the other direction, erasing filters and composing their
   level equalities recover the original incidence and equal endpoint births.
   `projection_filter_iff` therefore proves the desired commutation, with no
   whole-path-preservation premise hidden in `PlanningInvariant`.

4. **Path compression is proved independently and then consumed.**
   `:267–315` splits arbitrary finite raw paths at encountered semantic
   Values, obtaining helper-only incidences, and expands each projected edge
   back to its original finite path. Zero-edge semantic reachability is kept
   separately. This gives `compression_iff` without a planning-level premise;
   `filtered_compression_iff` then uses the proved incidence equivalence.
   The proof covers helper cycles traversed finitely and arbitrary sequences
   of semantic vertices; it is not limited to one helper edge.

5. **The strongest application has the expected exact premises.**
   `finite_helper_qualifies_iff` at `:319–329` quantifies over decidable semantic
   and helper types, a finite enumeration covering all nodes, Boolean adjacency,
   immutable semantic births, helper levels, the local `PlanningInvariant`,
   and one unchanged `ExtrusionOccurrence V T I`. It concludes executable
   eligibility of that event's embedded endpoints iff the existing `Qualifies`
   holds for `projectedRef edge`. It does not establish that this projection
   already equals an independently supplied source Ref; the handoff expressly
   leaves that source/native correspondence open.

6. **Singletons and graph counterexamples match the authority.**
   `eligible_refl` at `:158–161` preserves singleton qualification even without
   a self-edge. The three-vertex result at `:333–365` rejects the global-SCC
   shortcut despite equal-birth endpoints. The two-vertex result at `:367–398`
   retains reciprocal cross-birth references while rejecting eligibility.
   These are kernel-reduced finite graph facts. They do not establish a complete
   source typing counterexample or a source-acceptance theorem.

## Severity-tagged scope observations

These are explicit application boundaries, not defects requiring source repair.

| Severity | Exact location | Observation and recommended action |
| --- | --- | --- |
| INFO | `BirthLevelSCC.lean:8–14,70–75,129–142` | The finite recursive closure is a specification algorithm. No native Kosaraju implementation or complexity bound is proved. Keep native algorithm correctness and faithful finite-node/adjacency representation separate. |
| INFO | `BirthLevelSCC.lean:198–220,319–329`; producer handoff `:88–95` | Actual immutable Value births, actual helper planning levels, the local edge invariant, and equality between projected incidence and semantic Ref must be established by the source/native owner. A field name such as planning level does not itself supply these facts. Verify both SCC passes use the justified filtered graph. |
| INFO | `BirthLevelSCC.lean:187–194,317–329`; producer handoff `:137–148` | Eligibility alone does not prove the lawful parent/copy equality consumer, all-clause preservation, source derivations, publication/use transport, or the BL-JOINT shared-witness/telescope obligations. Keep original inference soundness and source-scoped coverage open. |
| INFO | producer handoff `:112–135` | The producer also records a Rust fixture/planner specification inspection. This review does not independently certify that separate inspection or any implementation/test change; the primary has assigned Rust review separately. |

## Checker evidence inspected

No checker rerun was performed or needed. Read the existing commands, versions,
exits, the complete originating-module audit source, and all 57 printed theorem
types and complete axiom reports. The isolated project uses Lean 4.35.0,
`-j1 -M1024`, and no external packages. Logs identify native Lake
`5.0.0-src+eb6cafb` and Lean commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

The initial failed elaboration is retained in `check-01.log` (exit 1 after the
successful Contracts build), and the repaired module build is recorded in
`check-02.log` (exit 0, no warnings). `audit-named.log` records the bounded helper
invocation for all 32 named theorems and exit 0. `audit-all.log` records all 57
originating-module theorem constants, including generated/private helpers, and
exit 0. Its source filters by actual module ownership, rejects originating
project axioms, verifies all required named roots are theorem targets, prints
each type/axiom result, and rejects all non-whitelisted transitive axioms.

Independent read-only parsing confirmed exactly 57 unique ordered BEGIN/END
pairs, exactly 57 matching axiom reports, and all 32 named roots exactly once.
The complete distribution is 37 with no axioms, 19 with `[propext]`, and one
generated theorem, `finiteReach.congr_simp`, with `[Quot.sound]`.

Complete named-theorem axiom grouping, under `YulangClosure.BirthLevelSCC`:

- `[]`: `Reach.trans`, `Reach.mono`, `levelPath_source`, `levelPath_target`,
  `levelPath_toReach`, `reach_toLevelPath`, `mutual_sameLevel_iff`,
  `Incidence.toReach`, `Incidence.erase`, `Incidence.level_eq`,
  `Incidence.filter`, `projection_filter_iff`, `compress_aux`, `compression_iff`.
- `[propext]`: `finiteReach_refl`, `finiteReach_edge`, `finiteReach_sound`,
  `finiteReach_join`, `finiteReach_complete`, `finiteReach_iff`,
  `filteredEdge_iff`, `eligible_refl`, `eligible_reach_iff`,
  `finite_qualifies_iff`, `filtered_compression_iff`,
  `finite_helper_qualifies_iff`, `three_covers`, `endpoint_filter_counterexample`,
  `endpoint_filter_not_qualified`, `two_covers`, `cross_birth_cycle_rejected`,
  `cross_birth_not_qualified`.

No `Classical.choice`, project axiom, `sorryAx`, or other non-whitelisted axiom
is reported. An independent read-only scan of the new module and Contracts
found no `sorry`, `admit`, `axiom`, `sorryAx`, `unsafe`, `native_decide`, or
`debug.skipKernelTC` match. The four elapsed entries sum to approximately
7.316104 seconds; no new reviewer checker time was spent.

| Evidence under `inference-birth/` | SHA-256 |
| --- | --- |
| `check-01.log` | `76a6d457bb0a3f1e201d581928ff099636edcf6cfb4e6a828f9eddf271bede6f` |
| `check-02.log` | `81c347717e5dfff392eaabce998a629709b621099ec2d87a745fbc1211e4d838` |
| `audit-named.log` | `cf8d32fc521eb258513ed7d10664cb117a020ae148505116cb57ea5d46354a6f` |
| `audit-all.log` | `5ae2b47380b94461b2f935f697ef7dec1d92fa645607fc19c4f26439afab0e1f` |
| `project/AuditBirthLevelSCC.lean` | `31c74956e26b5c97e9bfea7df6a4238fe627c25a4d3a56d5db63882efaa301ae` |
| `input-hashes.json` | `5781d46d1b7605b697a705b74c30e54e32a14455f3f9479eca811d7c0f03d22f` |

## Inspected scope and cessation

Inspected the complete 400-line module and frozen producer handoff, governing
source sections, actual Contracts qualification and original inference roots,
isolated input bytes, all complete audit declarations, and retained build
outcomes. Applied the repository AGENTS instructions and `yulang-lean-proofs`
skill already read in this session. Did not read or review current Rust edits,
fixtures, planner implementations, native SCC code, full original-source
inference derivations, or broader integration/default-build changes.

Only this exact leased review receipt was written. No source, cache, Git,
scheduling record, other receipt, or semantics was changed. No descendants or
checker processes were launched. **Review receipt frozen; writes STOPPED.**
