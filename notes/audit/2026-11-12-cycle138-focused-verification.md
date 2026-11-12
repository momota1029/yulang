# Cycle138 focused verification record

Source publication: `575433881b99d9d1e89a51de4cb53b234f846b87`.
Lean4.35.0; 113 distinct audited declarations = 111 public theorems + 2 certificate definitions.
Only propext/Classical.choice/Quot.sound. No full build or frozen Audit execution.

## Focused build

```sh
cd lean
lake build --wfail Yulang.GeneralDictionaryCurrentJournalExamples Yulang.GeneralDictionaryJournalTreeExamples Yulang.GeneralDictionaryJournalTreeFormation Yulang.GeneralDictionaryModeledJointGap Yulang.GeneralDictionaryRefreshGap Yulang.GeneralDictionarySourceChoiceVisibility Yulang.GeneralDictionarySelectedInstanceCoherence Yulang.GeneralDictionaryTerminalClassification
```

```text
✔ [661/661] Built Yulang.GeneralDictionaryTerminalClassification (4.3s)
Build completed successfully (661 jobs).
exit_code: 0
```

## Cycle138

Command: `cd lean && lake env lean --trust=0 Audit/Cycle138.lean`

```text
'Yulang.GeneralDictionaryCurrentJournal.initial_current' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryCurrentJournal.installed_current' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryCurrentJournal.step_current' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryCurrentJournal.trace_current' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryCurrentJournal.initial_trace_current' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryCurrentJournal.recorded_node' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryCurrentJournalExamples.actual_path' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryCurrentJournalExamples.recorded' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryCurrentJournalExamples.current_parent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryCurrentJournalExamples.no_original_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryCurrentJournalExamples.nonvacuous_beyond_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryCurrentJournalExamples.arbitrary_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
exit_code: 0
```

## Cycle138Formation

Command: `cd lean && lake env lean --trust=0 Audit/Cycle138Formation.lean`

```text
'Yulang.GeneralDictionarySourceChoiceVisibility.visible' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySourceChoiceVisibility.singleton_choice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySourceChoiceVisibility.singleton_key_coherence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySourceChoiceVisibility.singleton_selected_coherence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryJournalTreeFormation.initial_source' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJournalTreeFormation.formed_before' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryJournalTreeFormation.formed_after' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryJournalTreeFormation.reachable_positive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySelectedInstanceCoherence.instance_selected' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySelectedInstanceCoherence.recorded_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySelectedInstanceCoherence.recorded_at_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
exit_code: 0
```

## Cycle138Joint

Command: `cd lean && lake env lean --trust=0 Audit/Cycle138Joint.lean`

```text
'Yulang.GeneralDictionaryModeledJointGap.stale_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryModeledJointGap.query' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryModeledJointGap.schema' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryModeledJointGap.every_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryModeledJointGap.models_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryModeledJointGap.journal_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryModeledJointGap.known' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryModeledJointGap.generated_only_root' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryModeledJointGap.no_install' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryModeledJointGap.stable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryModeledJointGap.not_joint' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryModeledJointGap.edge_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryModeledJointGap.acyclic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryModeledJointGap.old_acyclic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryModeledJointGap.report_calculated' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryModeledJointGap.linked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryModeledJointGap.prepared' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryModeledJointGap.ready' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryModeledJointGap.survivor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryModeledJointGap.selected' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryModeledJointGap.modeled_stable_selected_not_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryModeledJointGap.registry_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryModeledJointGap.no_modeledSelectedJoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryModeledJointGap.current_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryModeledJointGap.current_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryModeledJointGap.not_sourceFormed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryJournalTree.recorded_tree' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJournalTree.uniform_dictionary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryJournalTree.missing_packet' depends on axioms: [propext, Quot.sound]
exit_code: 0
```

## Cycle138Refresh

Command: `cd lean && lake env lean --trust=0 Audit/Cycle138Refresh.lean`

```text
'Yulang.GeneralDictionaryRefreshGap.no_known' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRefreshGap.good_journal_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRefreshGap.refresh_unknown' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRefreshGap.generated_only_root' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRefreshGap.no_install' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRefreshGap.stable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRefreshGap.edge_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRefreshGap.acyclic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRefreshGap.old_acyclic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRefreshGap.selected' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRefreshGap.no_evidenceNode' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRefreshGap.not_sourceFormed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRefreshGap.no_bridges' depends on axioms: [propext, Classical.choice, Quot.sound]
exit_code: 0
```

## Cycle138Terminal

Command: `cd lean && lake env lean --trust=0 Audit/Cycle138Terminal.lean`

```text
'Yulang.GeneralDictionaryTerminalRefresh.output_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalRefresh.source_known' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalRefresh.source_unknown' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalRefresh.actual_refresh' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalRefresh.exact_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalRefresh.formed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalRefresh.inhabited' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalRefresh.context_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalRefresh.no_known_distinct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalRefresh.varying_original' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTerminalRefresh.varying_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalRefresh.refresh_large_unknown' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTerminalRefresh.current_query' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalRefresh.current_schema' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalRefresh.every_current_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTerminalRefresh.installs_committed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalRefresh.generated_only_root' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalRefresh.stable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalRefresh.current_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalRefresh.current_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalRefresh.completed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalRefresh.refines' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalRefresh.certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalClassification.edge_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalClassification.acyclic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalClassification.old_acyclic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalClassification.report_calculated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTerminalClassification.prepared' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalClassification.survivor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalClassification.selected' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalClassification.resolved' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalClassification.boundary_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTerminalClassification.classified' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTerminalClassification.two_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
exit_code: 0
```

## Cycle138Tree

Command: `cd lean && lake env lean --trust=0 Audit/Cycle138Tree.lean`

```text
'Yulang.GeneralDictionaryJournalTreeExamples.good_before' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJournalTreeExamples.edge_shape' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJournalTreeExamples.acyclic' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJournalTreeExamples.old_acyclic' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJournalTreeExamples.selected' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryJournalTreeExamples.enabled' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryJournalTreeExamples.feedback_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryJournalTreeExamples.finished_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryJournalTreeExamples.no_child' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryJournalTreeExamples.covered' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryJournalTreeExamples.accessible' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryJournalTreeExamples.good_after' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryJournalTreeExamples.bad_excluded' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryJournalTreeExamples.uniform_dictionary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
exit_code: 0
```

## Diff-only gate

`tools/verify-lean.sh . origin/integration/m1-final --no-build`

```text
verify-lean: . @ 0dc4a882d (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: lean/Audit.lean only appended (plus top import lines)
ok: lean/Audit/Cycle136.lean only appended (plus top import lines)
ok: lean/Audit/Cycle137.lean only appended (plus top import lines)
ok: lean/Audit/Cycle137Finished.lean only appended (plus top import lines)
ok: lean/Audit/Cycle137Followup.lean only appended (plus top import lines)
ok: lean/Audit/Recovery131135.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
exit_code: 0
```

## Import/hash inventory, not semantic coverage

`python tools/boundary-input-inventory.py --check`

```text
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=302; Main=93; Audit=302; ledger mentioned=160. Mention counts are not audit completion counts.
exit_code: 0
```

All 113 exact signatures were obtained by Lean #check with full names/universes, exit 0. The signatures are in the separate cycle138 design appendix.

## Verified publication manifest

All 30 changed source/note files were individually fetched at this immutable source commit and byte-compared. The two frozen files were checked by tree blob SHA. A later documentation-only final commit adds this record, the handoff, and the completed heartbeat without changing these source blobs.

```json
{
  "source_commit": "575433881b99d9d1e89a51de4cb53b234f846b87",
  "source_tree": "ff7a4d3d1711a101f326578a181722e4f90efb9e",
  "tree_truncated": false,
  "tree_entries": 2777,
  "blob_sha1": {
    "lean/Audit/Cycle138.lean": "643172f39771eb68248429bec2351836300cdc92",
    "lean/Audit/Cycle138Formation.lean": "e42f61958ce2522a08cadcc21e03a2131e484761",
    "lean/Audit/Cycle138Joint.lean": "4184712d4864de31c352348f87c6ba5053bce392",
    "lean/Audit/Cycle138Refresh.lean": "a40a660c44c3a8b0108f4669a851e7abd1796881",
    "lean/Audit/Cycle138Terminal.lean": "c8a415bf7b4cffbe54bbdbc9d5df8587e14a10b0",
    "lean/Audit/Cycle138Tree.lean": "8b8c521a10a2f60cc149b5ae93e8b233a89866f8",
    "lean/Yulang.lean": "e9beb13f54f789ed2f5c37640df1386955483c82",
    "lean/Yulang/GeneralDictionaryCurrentJournal.lean": "ec51000a046add77acd98c16f5b9de99e312a955",
    "lean/Yulang/GeneralDictionaryCurrentJournalExamples.lean": "0b120b3bbf91eeac6df8580f5cb56e3f93620975",
    "lean/Yulang/GeneralDictionaryJournalTree.lean": "840c25ecb4d87470fc7df985dd921d53c641a147",
    "lean/Yulang/GeneralDictionaryJournalTreeExamples.lean": "128274d977194d17a2b02fdbba4cca992a7e12b5",
    "lean/Yulang/GeneralDictionaryJournalTreeFormation.lean": "194e436b4476f12ebb2ee943709596c7dd78a848",
    "lean/Yulang/GeneralDictionaryModeledJointGap.lean": "208d79672369f50f0c4d6684f8b5b724a1007a46",
    "lean/Yulang/GeneralDictionaryRefreshGap.lean": "4f3009290311e1c18789888a72a04a2992219696",
    "lean/Yulang/GeneralDictionarySelectedInstanceCoherence.lean": "83d94f2ef7eb9f95b99383f7021855d7c32d442f",
    "lean/Yulang/GeneralDictionarySourceChoiceVisibility.lean": "2e694b601930ef15826af2c05fff20aea09dd678",
    "lean/Yulang/GeneralDictionaryTerminalClassification.lean": "33c13c5d4711ce65d6fe65782db76633aa669c43",
    "lean/Yulang/GeneralDictionaryTerminalRefresh.lean": "c87ce2bc1251f8fc008055ec1207848a9c366e9d",
    "notes/design/2026-11-10-boundary-input-coverage.tsv": "62d320e2494b1403f65d88a9defffd33cfa9f66f",
    "notes/design/2026-11-12-cycle138-current-journal.md": "ceda591404bbb08bef2b5c4f660fa2799ef22142",
    "notes/design/2026-11-12-cycle138-final-terminal-classification.md": "caca3fabeedd0f42214577ff4b8d469ec55a696b",
    "notes/design/2026-11-12-cycle138-journal-tree.md": "55072aa3aeb1f3e7f55df6e8812f3044968888cb",
    "notes/design/2026-11-12-cycle138-module-guide.md": "c4d9b9fb3115381c59dda77294dfc11dab464950",
    "notes/design/2026-11-12-cycle138-positive-terminal-completion.md": "1293d3ce8f40c155e114db982bfd432ecea6615c",
    "notes/design/2026-11-12-cycle138-refresh-evidence-counterexample.md": "196d91f9ccabb7993807710be4044d894183506b",
    "notes/design/2026-11-12-cycle138-scope-repair-obligations.md": "e6bae19caf74c571b92589a102bbb39bc1f78059",
    "notes/design/2026-11-12-cycle138-source-formed-choice-residual.md": "a5989260d4ee439d74ea9e57113208aa7105cf85",
    "notes/design/2026-11-12-cycle138-stale-joint-obstruction.md": "08b0e2fc2da6c0956dadceb78cdaef54035fc953",
    "notes/design/2026-11-12-cycle138-theorem-signatures.md": "40250b4c82ff91cf6023a3bc01e48fd7062ebffa",
    "notes/questions/2026-11-12-cycle138-stable-journal-evidence-scope.md": "4b10da1f94df5f978868a5aa976c34817ca9b92c",
    "lean/Audit.lean": "1cd235e664d51efda50bd37f6751854aea94b10f",
    "lean/README.md": "0b255a4d97ae144984a60e1e7de03c9389b104e8"
  }
}
```
