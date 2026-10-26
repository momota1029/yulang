# Native dictionary denotation r4 — frozen producer handoff

Producer: `/root/source_membership_r4`. Date: 2026-10-26.
Baseline supplied by primary: `37ec9da2aaca2d7b806887d06d9bbd8b0fc5439c`, `yulang3`.
Status: **WRITES STOPPED after this handoff; fresh independent review required. Original Function membership and whole-language proof remain OPEN.**

## 1. Exact outcome and scope

The concrete playground runtime Word/Substitution DAG interpretation is constructed and checked. `YulangClosure.NativeDictionaryDenotation.name_checked_dictionary_denotation` proves the actual Name allocation/guard branch has the same dictionary observation as value substitution, optional raw-caller Assign, then caller substitution, with the same raw defaults, dictionary, member site and witness parameter. Lookup/default failure remains possible. The theorem is universally quantified over complete step payloads and all supplied fixed dictionary/witness values.

`applyDag_denotes` constructs the raw resulting arena/context and simultaneously proves both its decoded ordered action and all old-word meaning preservation. `name_defaults_unchanged` retains the whole raw initializer map's meaning. `initialize_fresh`, non-idempotence and cyclic-default witnesses preserve the implementation's determined choices. No source safety predicate, Function membership, body success, final world or whole `LocalLaws` is a hypothesis.

The original full `ValueMem_F†(W,r,e)`, `PhiW`, `P_F`, descriptor/annotation/history interpretation and `SourceT` do not follow yet. The new note identifies available source `Dict_R`/whole-packet/evidence-template definitions rather than claiming generic dictionary semantics are absent. The exact residual is the actual selected-use/body-template map from one original `nu,K,D,eta0` packet, captures/evidence/adapters and current event to the native `(word,site) -> Label` table, together with source instantiation/alias correspondence. No contradiction or source-qualified counterexample was proved. The actual delayed computation `C` and returned identity `W` remain distinct, and no later fixture Call of `W` was added.

The runtime inspected is `tools/inference-playground/src/runtime`, not solver-native inference. The paper `Dict_R` is a typed nominal dictionary record; the runtime table is a dispatch index. Their names do not establish their correspondence. Allocation failures, the native combined `32_768` work counter and error-path mutation states are not equated to the mathematical total/finite-unfolding functions. Group/Ascription forwarding is reported only for the actual bounded LocalSource owner, retaining its adapter-registration qualification.

## 2. Exact leased outputs and frozen hashes

| Output | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/NativeDictionaryDenotation.lean` | `d44a78f08970a09ca4c3e99a1d8dea846286a299d1a2bc91ec3b5e0eabea9070` |
| `notes/theory/2026-10-26-native-dictionary-denotation.md` | `c72586360b9c6a98c99093c0e239f73f49c0103f2d442f92cd492e1d871d7b3c` |
| `tasks/agent-loop/inbox/20261026-native-dictionary-denotation-r4.md` | Stored externally in task scratch `output-hashes.json` to avoid a self-hash cycle. |

All other repository files are read-only inputs. No Git command, child agent, compiler/Rust edit, root import, shared status, configuration, manifest, question or shared lease was modified. The accepted receiving artifact at parent-supplied commit `2ceba875f` remains byte-identical; `prior-frozen-check.json` preserves its three expected and observed hashes.

Sole new scratch/cache: `/workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/**`.
The previous `/workspace/scratch/f98087c7ac1a/source-membership-r4/**` was read only and remains frozen.

## 3. Original source clauses and represented cases

The construction note contains the complete source-to-definition table. Its decisive original clauses are:

- `notes/theory/2026-10-08-call-semantic-input-realization.md`, §2 and §§4.1–4.2: one original fiber/assignment/current event, immutable binding's actual provider/root and hereditary certificate, same current Name projection.
- `notes/design/2026-10-08-source-generalize-definition.md`, §2; selected `notes/theory/2026-10-08-source-generalize-definition-and-proof.md`, §§3.3 and 6: fixed binding object and dependencies, actual source-provided Specialize mechanism, Established/OneShot installed monomorphic dictionary, same retained execution.
- `docs/yulang-dot-selection-safety-ja.tex`, whole-packet instance, concrete dictionary representation, Hyp/Impl/Assoc finite evidence and M/R/F: one whole instance, shared captures, typed fields and direct argument/result adapters. Opening source/corrected-machine and compiler-accepted-evidence limits remain active.
- `notes/design/2026-10-08-contextual-function-membership-definition.md`, §2: all original independently admitted complete challenges and all observations/developments. This domain was not replaced by the set of successful runtime dictionary queries.

Native covered algebra: optional/empty handles; Step and Join; Assign matching and nonmatching base; ordered Then with arbitrary repeated DAG sharing; old-handle stability; actual guarded Name; raw initializer defaults; finite default chains; lookup at arbitrary full dictionary parameters. Constructor validity hypotheses are explicit successful raw denotations, not descriptor-membership hypotheses. An arbitrary malformed unused Assign replacement can be skipped by native execution; the denotation theorem does not assert equivalence for that malformed state.

Not claimed: Rust binary verification, allocator availability, combined runtime work-budget adequacy, full typed evidence-to-label compilation, full original context/descriptor realization, or equality of complete native worlds before/after a Name read. Receiving receipts remain governed by the earlier frozen artifact and actual native owners.

## 4. Environment, commands and resources

Pinned Lake: `/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`.
Actual Lake: `Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)`.
Actual Lean: `Lean 4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, x86_64 release.

Every checker invocation used the normal authorized `require_escalated` tool path, one CPU affinity `[0]`, `LEAN_NUM_THREADS=1`, `-j1`, `-M1024`, `PYTHONDONTWRITEBYTECODE=1` and owned TMPDIR. The wrapper imposes 119 seconds overall and 1 GiB aggregate sampled RSS; the helper timeout is 115 seconds. The isolated project pin/Lake file/empty dependency manifest are exact input copies. No installation or dependency update occurred.

Budget: 1800 task wall seconds; 12 checker calls, each at most 120 seconds. Used 11 checks. Task elapsed at handoff: 1027.570 seconds. Total checker wall time: 41.285 seconds. Largest checker: 11.065 seconds. Peak aggregate sampled RSS: 927268864 bytes. No timeout or budget termination occurred.

| Receipt | Exit | Wall seconds | Peak aggregate RSS bytes | Source snapshot SHA-256 |
| --- | --- | --- | --- | --- |
| `01-base` | 1 | 1.283 | 632287232 | `c339f20df5b863fe277490096642388e831c36acbdd3b8337a8875ee91af5425` |
| `02-base-repair` | 0 | 2.815 | 910671872 | `bc8c01d2f929561769f191405c0394b14961c70c562342cbbf517c5aec83f190` |
| `03-name` | 1 | 3.338 | 636399616 | `01270f46b719762c578662ae9a744af437b32ec0c215445307e0591cf4bf431a` |
| `04-name-repair` | 0 | 11.065 | 914685952 | `44c1906a72c244537b2375a7a9e508df13e2cd0844b13ac0e8a956af653fe60f` |
| `05-dictionary` | 1 | 2.113 | 645742592 | `0dfa9baaae59b864eb9e9ef1aacb979b66ef132134fd3061d39471e7c5833c92` |
| `06-raw-defaults` | 0 | 5.931 | 924295168 | `5b7c98e7a34550670c0ba30608db65b3dd0638f76a195ee503ad72c2ea8ed28c` |
| `07-raw-dag` | 1 | 2.231 | 651001856 | `49dde3388ec5052834c1e9a29f078aef56402807955c0022bcaf3ccbc52bb3be` |
| `08-raw-dag-repair` | 0 | 5.439 | 926040064 | `b2205581ead7393df9dcc652c279be790c5d8366c1a20198a48e43edd46b0382` |
| `09-originating-census` | 0 | 1.054 | 899969024 | `b2205581ead7393df9dcc652c279be790c5d8366c1a20198a48e43edd46b0382` |
| `10-checked-dictionary` | 0 | 4.992 | 927268864 | `d44a78f08970a09ca4c3e99a1d8dea846286a299d1a2bc91ec3b5e0eabea9070` |
| `11-final-originating-census` | 0 | 1.025 | 901685248 | `d44a78f08970a09ca4c3e99a1d8dea846286a299d1a2bc91ec3b5e0eabea9070` |

Four actual failed proof builds are retained: initial reserved-name/simplification failures; the Name transport pattern/fresh-node normalization repair; initializer reserved-name/default-recursion simplification repair; and a raw DAG Option-bind normalization repair. Their exact diagnostics and immutable per-call sources appear below and in `snapshots/`. These are not mathematical counterexamples. Setup locator misses are separately recorded in `setup-receipt.json`; parent explicitly corrected the native module locator.

## 5. Complete audit and required-root manifest

Authored roots: 37. All originating theorem constants: 131. This census uses the module index of `YulangClosure.NativeDictionaryDenotation`, not a public-name prefix, so private and compiler-generated theorem declarations are included. Every originating theorem receives its complete `#check @name` and transitive `#print axioms`; the printed log contains no ellipsis. Project axiom declarations and dependencies outside the exact whitelist are rejected.

Axiom distribution across all originating constants: {'none': 90, 'propext, Quot.sound': 17, 'propext': 24}. Authored roots: {'propext, Quot.sound': 17, 'propext': 13, 'none': 7}. There is no `sorryAx`, project axiom, `Classical.choice`, native-evaluation axiom or kernel-check bypass in the delivered dependency cone. Ordinary standard `propext` and `Quot.sound` uses are reported without calling the whole module axiom-free. The module imports only `Init`.

Final helper/root audit: `10-checked-dictionary`, exit 0. Final complete census: `11-final-originating-census`, exit 0. These check the same final source hash. Root imports/default aggregate builds were outside this lease and were not run. Independent review is not self-certified by these checks.

```json
{
  "modules": [
    "YulangClosure.NativeDictionaryDenotation"
  ],
  "required_roots": [
    "YulangClosure.NativeDictionaryDenotation.wordAt_bound",
    "YulangClosure.NativeDictionaryDenotation.wordAt_push_old",
    "YulangClosure.NativeDictionaryDenotation.word_push_old",
    "YulangClosure.NativeDictionaryDenotation.append_denotes",
    "YulangClosure.NativeDictionaryDenotation.join_denotes",
    "YulangClosure.NativeDictionaryDenotation.action_append",
    "YulangClosure.NativeDictionaryDenotation.subAt_bound",
    "YulangClosure.NativeDictionaryDenotation.subAt_push_old",
    "YulangClosure.NativeDictionaryDenotation.substitution_push_old",
    "YulangClosure.NativeDictionaryDenotation.then_denotes",
    "YulangClosure.NativeDictionaryDenotation.then_action",
    "YulangClosure.NativeDictionaryDenotation.name_action_none",
    "YulangClosure.NativeDictionaryDenotation.name_action_some",
    "YulangClosure.NativeDictionaryDenotation.context_transport",
    "YulangClosure.NativeDictionaryDenotation.subAt_word_transport",
    "YulangClosure.NativeDictionaryDenotation.substitution_word_push",
    "YulangClosure.NativeDictionaryDenotation.compose_keeps_old",
    "YulangClosure.NativeDictionaryDenotation.name_denotes",
    "YulangClosure.NativeDictionaryDenotation.name_checked_denotes",
    "YulangClosure.NativeDictionaryDenotation.context_fields",
    "YulangClosure.NativeDictionaryDenotation.join_keeps_old",
    "YulangClosure.NativeDictionaryDenotation.assignRaw_denotes",
    "YulangClosure.NativeDictionaryDenotation.assignRaw_keeps_old",
    "YulangClosure.NativeDictionaryDenotation.applyDag_denotes",
    "YulangClosure.NativeDictionaryDenotation.initialize_fresh",
    "YulangClosure.NativeDictionaryDenotation.resolve_default",
    "YulangClosure.NativeDictionaryDenotation.name_keeps_context",
    "YulangClosure.NativeDictionaryDenotation.name_dispatch_meaning",
    "YulangClosure.NativeDictionaryDenotation.name_dictionary_denotation",
    "YulangClosure.NativeDictionaryDenotation.caller_action_not_idempotent",
    "YulangClosure.NativeDictionaryDenotation.name_applies_caller_once",
    "YulangClosure.NativeDictionaryDenotation.cyclic_default_fails",
    "YulangClosure.NativeDictionaryDenotation.empty_defaults_valid",
    "YulangClosure.NativeDictionaryDenotation.initializer_defaults_valid",
    "YulangClosure.NativeDictionaryDenotation.name_defaults_unchanged",
    "YulangClosure.NativeDictionaryDenotation.name_raw_dictionary_denotation",
    "YulangClosure.NativeDictionaryDenotation.name_checked_dictionary_denotation"
  ],
  "originating_theorem_count": 131,
  "all_originating_names": [
    "YulangClosure.NativeDictionaryDenotation.WordNode.join.inj",
    "YulangClosure.NativeDictionaryDenotation.then_action",
    "YulangClosure.NativeDictionaryDenotation.name_action_some",
    "YulangClosure.NativeDictionaryDenotation.compose.eq_1",
    "_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.nameAction.match_1.eq_2",
    "YulangClosure.NativeDictionaryDenotation.substitution_word_push",
    "YulangClosure.NativeDictionaryDenotation.substitution.eq_2",
    "YulangClosure.NativeDictionaryDenotation.action_append",
    "_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.nameAction.match_1.eq_1",
    "YulangClosure.NativeDictionaryDenotation.then_denotes",
    "YulangClosure.NativeDictionaryDenotation.WordArena.push.inj",
    "YulangClosure.NativeDictionaryDenotation.assign.eq_1",
    "YulangClosure.NativeDictionaryDenotation.State.mk.injEq",
    "YulangClosure.NativeDictionaryDenotation.subAt.eq_3",
    "YulangClosure.NativeDictionaryDenotation.NameResult.mk.injEq",
    "YulangClosure.NativeDictionaryDenotation.nameChecked.eq_2",
    "YulangClosure.NativeDictionaryDenotation.WordArena.empty.sizeOf_spec",
    "YulangClosure.NativeDictionaryDenotation.SubArena.push.injEq",
    "_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.subAt.match_1.eq_2",
    "YulangClosure.NativeDictionaryDenotation.compose_keeps_old",
    "YulangClosure.NativeDictionaryDenotation.empty_defaults_valid",
    "YulangClosure.NativeDictionaryDenotation.SubNode.then.sizeOf_spec",
    "YulangClosure.NativeDictionaryDenotation.word.eq_2",
    "YulangClosure.NativeDictionaryDenotation.name_checked_dictionary_denotation",
    "YulangClosure.NativeDictionaryDenotation.Context.mk.sizeOf_spec",
    "YulangClosure.NativeDictionaryDenotation.SubNode.then.inj",
    "YulangClosure.NativeDictionaryDenotation.WordArena.push.injEq",
    "_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.join.match_1.eq_1",
    "YulangClosure.NativeDictionaryDenotation.subAt_word_transport",
    "YulangClosure.NativeDictionaryDenotation.resolve_default",
    "YulangClosure.NativeDictionaryDenotation.instDecidableEqRawContext.decEq._proof_1",
    "YulangClosure.NativeDictionaryDenotation.assignRaw.eq_1",
    "YulangClosure.NativeDictionaryDenotation.SubNode.then.injEq",
    "YulangClosure.NativeDictionaryDenotation.RawContext.mk.inj",
    "YulangClosure.NativeDictionaryDenotation.name_dictionary_denotation",
    "YulangClosure.NativeDictionaryDenotation.State.mk.inj",
    "YulangClosure.NativeDictionaryDenotation.SubArena.brecOn.eq",
    "YulangClosure.NativeDictionaryDenotation.name_checked_denotes",
    "_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.applyDag.match_1.eq_1",
    "YulangClosure.NativeDictionaryDenotation.substitution.eq_1",
    "YulangClosure.NativeDictionaryDenotation.join_denotes",
    "YulangClosure.NativeDictionaryDenotation.applyDag.eq_3",
    "_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.wordAt.match_3.eq_1",
    "YulangClosure.NativeDictionaryDenotation.compose.eq_2",
    "YulangClosure.NativeDictionaryDenotation.RawContext.mk.injEq",
    "YulangClosure.NativeDictionaryDenotation.initializer_defaults_valid",
    "YulangClosure.NativeDictionaryDenotation.SubArena.push.inj",
    "YulangClosure.NativeDictionaryDenotation.instDecidableEqContext.decEq._proof_1",
    "YulangClosure.NativeDictionaryDenotation.wordAt_push_old",
    "YulangClosure.NativeDictionaryDenotation.Assignment.mk.injEq",
    "_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.wordAt.match_3.eq_2",
    "YulangClosure.NativeDictionaryDenotation.nameAction.eq_2",
    "YulangClosure.NativeDictionaryDenotation.WordNode.step.inj",
    "YulangClosure.NativeDictionaryDenotation.wordAt_bound",
    "YulangClosure.NativeDictionaryDenotation.SubNode.assign.injEq",
    "YulangClosure.NativeDictionaryDenotation.name_denotes",
    "_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.word.match_1.eq_2",
    "YulangClosure.NativeDictionaryDenotation.Context.mk.inj",
    "YulangClosure.NativeDictionaryDenotation.name_defaults_unchanged",
    "YulangClosure.NativeDictionaryDenotation.name_raw_dictionary_denotation",
    "YulangClosure.NativeDictionaryDenotation.defaultMeaning.eq_1",
    "YulangClosure.NativeDictionaryDenotation.applyDag.eq_1",
    "YulangClosure.NativeDictionaryDenotation.Context.mk.injEq",
    "YulangClosure.NativeDictionaryDenotation.subAt_push_old",
    "_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.subAt.match_1.eq_1",
    "YulangClosure.NativeDictionaryDenotation.WordArena.push.sizeOf_spec",
    "YulangClosure.NativeDictionaryDenotation.nameAction.eq_1",
    "_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.join.match_1.eq_3",
    "YulangClosure.NativeDictionaryDenotation.nameChecked.eq_1",
    "YulangClosure.NativeDictionaryDenotation.Assignment.mk.inj",
    "YulangClosure.NativeDictionaryDenotation.Assignment.mk.sizeOf_spec",
    "YulangClosure.NativeDictionaryDenotation.instDecidableEqRawContext.decEq._proof_2",
    "YulangClosure.NativeDictionaryDenotation.WordNode.join.injEq",
    "YulangClosure.NativeDictionaryDenotation.WordNode.join.sizeOf_spec",
    "YulangClosure.NativeDictionaryDenotation.compose.eq_3",
    "YulangClosure.NativeDictionaryDenotation.caller_action_not_idempotent",
    "_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.applyDag.match_1.eq_2",
    "YulangClosure.NativeDictionaryDenotation.context.eq_1",
    "YulangClosure.NativeDictionaryDenotation.subAt_bound",
    "YulangClosure.NativeDictionaryDenotation.substitution_push_old",
    "YulangClosure.NativeDictionaryDenotation.initializer.eq_1",
    "YulangClosure.NativeDictionaryDenotation.wordAt.eq_2",
    "YulangClosure.NativeDictionaryDenotation.SubArena.empty.sizeOf_spec",
    "YulangClosure.NativeDictionaryDenotation.name_action_none",
    "YulangClosure.NativeDictionaryDenotation.wordAt.eq_1",
    "YulangClosure.NativeDictionaryDenotation.SubNode.assign.sizeOf_spec",
    "_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.wordAt.match_1.eq_1",
    "YulangClosure.NativeDictionaryDenotation.append.eq_1",
    "YulangClosure.NativeDictionaryDenotation.cyclic_default_fails",
    "YulangClosure.NativeDictionaryDenotation.action.eq_1",
    "_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.subAt.match_3.eq_2",
    "YulangClosure.NativeDictionaryDenotation.join.eq_2",
    "YulangClosure.NativeDictionaryDenotation.subAt.eq_1",
    "_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.join.match_1.eq_2",
    "YulangClosure.NativeDictionaryDenotation.context_transport",
    "YulangClosure.NativeDictionaryDenotation.SubArena.push.sizeOf_spec",
    "YulangClosure.NativeDictionaryDenotation.WordArena.brecOn.eq",
    "YulangClosure.NativeDictionaryDenotation.applyDag_denotes",
    "YulangClosure.NativeDictionaryDenotation.join.eq_3",
    "YulangClosure.NativeDictionaryDenotation.name_keeps_context",
    "YulangClosure.NativeDictionaryDenotation.join_keeps_old",
    "YulangClosure.NativeDictionaryDenotation.RawContext.mk.sizeOf_spec",
    "YulangClosure.NativeDictionaryDenotation.subAt.eq_2",
    "YulangClosure.NativeDictionaryDenotation.subAt.eq_def",
    "YulangClosure.NativeDictionaryDenotation.name_dispatch_meaning",
    "YulangClosure.NativeDictionaryDenotation.join.eq_1",
    "YulangClosure.NativeDictionaryDenotation.WordNode.step.injEq",
    "YulangClosure.NativeDictionaryDenotation.context_fields",
    "YulangClosure.NativeDictionaryDenotation.name_applies_caller_once",
    "YulangClosure.NativeDictionaryDenotation.word_push_old",
    "YulangClosure.NativeDictionaryDenotation.SubNode.assign.inj",
    "YulangClosure.NativeDictionaryDenotation.assignRaw_keeps_old",
    "YulangClosure.NativeDictionaryDenotation.instDecidableEqContext.decEq._proof_3",
    "YulangClosure.NativeDictionaryDenotation.instDecidableEqContext.decEq._proof_2",
    "YulangClosure.NativeDictionaryDenotation.WordNode.step.sizeOf_spec",
    "YulangClosure.NativeDictionaryDenotation.append_denotes",
    "YulangClosure.NativeDictionaryDenotation.initialize_fresh",
    "_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.subAt.match_3.eq_1",
    "YulangClosure.NativeDictionaryDenotation.word.eq_1",
    "YulangClosure.NativeDictionaryDenotation.NameResult.mk.inj",
    "YulangClosure.NativeDictionaryDenotation.dispatchMeaning.eq_1",
    "YulangClosure.NativeDictionaryDenotation.assignRaw_denotes",
    "YulangClosure.NativeDictionaryDenotation.State.mk.sizeOf_spec",
    "_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.wordAt.match_1.eq_2",
    "YulangClosure.NativeDictionaryDenotation.wordAt.eq_3",
    "YulangClosure.NativeDictionaryDenotation.NameResult.mk.sizeOf_spec",
    "_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.word.match_1.eq_1",
    "YulangClosure.NativeDictionaryDenotation.wordAt.eq_def",
    "YulangClosure.NativeDictionaryDenotation.applyDag.eq_2",
    "YulangClosure.NativeDictionaryDenotation.instDecidableEqRawContext.decEq._proof_3",
    "YulangClosure.NativeDictionaryDenotation.applyDag.eq_def"
  ],
  "audit_source_sha256": "29bff20dd4f6bb205980ac10815063abaa115fa89f7b652d2803dbd93ac44ce2",
  "final_source_sha256": "d44a78f08970a09ca4c3e99a1d8dea846286a299d1a2bc91ec3b5e0eabea9070",
  "axiom_whitelist": [
    "propext",
    "Classical.choice",
    "Quot.sound"
  ],
  "import_dependencies": [
    "Init"
  ],
  "default_root_import_changed": false
}
```

## 6. Frozen input snapshots

The supplied commit identity is parent authority; this leaf deliberately ran no Git command to restate it. Exact read input bytes are copied to `inputs/` and hashed below. The final consistency pass found no changed input. The later accepted receiving artifact is explicitly separate from the baseline source set.

| Input path | SHA-256 | Bytes |
| --- | --- | --- |
| `AGENTS.md` | `ce73e9754ba9fd00bd2c4395d322ce77730a26aafb586d51de8ad169d7f8d48f` | 8296 |
| `AGENTS.pre-sprint.md` | `34b8b8169696dcc6a0899204226914d250ddecf6782d14be670b7b2d5352c562` | 23767 |
| `.codex/agents/lean-prover.toml` | `a595880badf28482ad64c61d141e7eaa3781fe079d831e9e5d44b60669181109` | 2505 |
| `.agents/skills/yulang-lean-proofs/SKILL.md` | `05346b8c6e3d9cdd1715da1774bb26cf7bce313233782240b3493bd9ee8754a7` | 7856 |
| `.agents/skills/yulang-lean-proofs/references/sources.md` | `cb3f1009e80f0f9f7a1bf2575b4144e002a72f21e474c66b441e1f626a1e4d4a` | 5330 |
| `.agents/skills/yulang-lean-proofs/references/execution.md` | `a1d8c47550e8925220623e0401410556d92719aff5590c459ac4c2e88306800b` | 5345 |
| `.agents/skills/yulang-lean-proofs/scripts/check_lean.py` | `a4f10b70297cbf4d8b5bc0c7526bc29783eaf417f1f70e53eeea341d1150dde6` | 10178 |
| `rules/design-authority.md` | `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1` | 10512 |
| `rules/goal-driven-sprints.md` | `e50f5d4f79814c87af56e7dc34ddb6ab968abb523826c72ecdc40a8920397c0a` | 16788 |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` | 7582 |
| `tools/inference-playground/src/runtime/dispatch.rs` | `f45057373f2ed3a7b6ce915611db093015fb93cdb05984a5e3b23cfd44720873` | 14030 |
| `tools/inference-playground/src/runtime/program.rs` | `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907` | 100635 |
| `tools/inference-playground/src/runtime/machine.rs` | `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e` | 166139 |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` | 9952 |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` | 70420 |
| `notes/theory/2026-10-23-r342-k0-value-environment-realization.md` | `ab5b86070acbb75639172ce96182a1ea08bdc8fe22f185d691fe542a80fee420` | 34336 |
| `notes/theory/2026-10-23-r342-k0-value-environment-source-census.md` | `18a4eef622ee8feacc8db48d4360321fdcbd8d5f330636866705f42b8551b1b5` | 12540 |
| `notes/theory/2026-10-24-source-core-action-coverage.md` | `36672ef591f42a281a04f14fb7ddc4c5283c119de20fee15168e37cbbf13201a` | 40813 |
| `notes/theory/2026-10-24-source-core-finite-interface.md` | `d37a30f1f59ad327ebcba129db5b069f4eed1f839d1733230863fdb711a16488` | 27818 |
| `notes/theory/2026-10-22-r323-member-dispatch-projection.md` | `3e7e5f74e58d6fcfdf32564a99c1c837a78ba3c53c60e1242ed4b4be6d0d7114` | 7234 |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` | 25 |
| `notes/theory/lean/lakefile.toml` | `cab85ff9a8a7dc5103fe932739dcea0dfc02e6420b1277565449882c802473bd` | 239 |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` | 145 |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` | 10886 |
| `notes/theory/2026-10-08-call-semantic-input-realization.md` | `fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a` | 39961 |
| `notes/design/2026-10-08-contextual-function-membership-definition.md` | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` | 8825 |
| `notes/theory/lean/YulangClosure/SourceIdentityWorld.lean` | `6019fd9d57cde50183e016bd0c72de2c6eee72009065d85119fb0348dbcf0168` | 25976 |
| `notes/theory/2026-10-26-source-function-membership-construction.md` | `0ef65d4de31e7f2686217bfbdd547cd4f077325c45e80660a5791a7e31e9c2eb` | 18566 |
| `docs/yulang-source-type-safety-ja.tex` | `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166` | 184349 |
| `docs/yulang-dot-selection-safety-ja.tex` | `47b7fcec1f501e7c326ab9859885e329aab2730066806ea79212e825ebb32b0b` | 89832 |
| `notes/theory/lean/YulangClosure/SourceFunctionMembership.lean` | `8d370ee57e486ae48607d1bab493ae5135f28bf8a5a7ff1b0ef240fc0247e424` | 7744 |
| `tasks/agent-loop/inbox/20261026-source-function-membership-r4.md` | `9747fc7520a713c644ad33b219013043ab819f58460f63b390343a5c0960238f` | 29902 |

## 7. Complete originating-module theorem types and transitive axioms

```text
YULANG_AUDIT_MODULE YulangClosure.NativeDictionaryDenotation 131
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.WordNode.join.inj
@YulangClosure.NativeDictionaryDenotation.WordNode.join.inj : ∀ {Step : Type} {left right left_1 right_1 : Nat},
  YulangClosure.NativeDictionaryDenotation.WordNode.join left right =
      YulangClosure.NativeDictionaryDenotation.WordNode.join left_1 right_1 →
    left = left_1 ∧ right = right_1
'YulangClosure.NativeDictionaryDenotation.WordNode.join.inj' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.WordNode.join.inj
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.then_action
@YulangClosure.NativeDictionaryDenotation.then_action : ∀ {Step : Type}
  {words : YulangClosure.NativeDictionaryDenotation.WordArena Step}
  {subs : YulangClosure.NativeDictionaryDenotation.SubArena} {first second : Option Nat}
  {a b : List (YulangClosure.NativeDictionaryDenotation.Assignment Step)},
  YulangClosure.NativeDictionaryDenotation.substitution words subs first = Option.some a →
    YulangClosure.NativeDictionaryDenotation.substitution words subs second = Option.some b →
      ∀ (c : YulangClosure.NativeDictionaryDenotation.Context Step),
        Option.map (fun as => YulangClosure.NativeDictionaryDenotation.action as c)
            (YulangClosure.NativeDictionaryDenotation.substitution words
              (YulangClosure.NativeDictionaryDenotation.compose subs first second).fst
              (YulangClosure.NativeDictionaryDenotation.compose subs first second).snd) =
          Option.some
            (YulangClosure.NativeDictionaryDenotation.action b (YulangClosure.NativeDictionaryDenotation.action a c))
'YulangClosure.NativeDictionaryDenotation.then_action' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.then_action
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.name_action_some
@YulangClosure.NativeDictionaryDenotation.name_action_some : ∀ {Step : Type}
  (value current : List (YulangClosure.NativeDictionaryDenotation.Assignment Step))
  (caller input : YulangClosure.NativeDictionaryDenotation.Context Step) (cell : Nat) (item : Step),
  YulangClosure.NativeDictionaryDenotation.action
      (YulangClosure.NativeDictionaryDenotation.nameAction value current caller cell (Option.some item)) input =
    YulangClosure.NativeDictionaryDenotation.action current
      (YulangClosure.NativeDictionaryDenotation.assign
        { scope := cell, replacement := { base := caller.base, word := caller.word ++ [item] } }
        (YulangClosure.NativeDictionaryDenotation.action value input))
'YulangClosure.NativeDictionaryDenotation.name_action_some' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.name_action_some
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.compose.eq_1
YulangClosure.NativeDictionaryDenotation.compose.eq_1 : ∀ (subs : YulangClosure.NativeDictionaryDenotation.SubArena)
  (second : Option Nat), YulangClosure.NativeDictionaryDenotation.compose subs Option.none second = (subs, second)
'YulangClosure.NativeDictionaryDenotation.compose.eq_1' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.compose.eq_1
YULANG_AUDIT_BEGIN _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.nameAction.match_1.eq_2
@_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.nameAction.match_1.eq_2 : ∀
  {Step : Type} (motive : Option Step → Sort u_1) (item : Step) (h_1 : Unit → motive Option.none)
  (h_2 : (item : Step) → motive (Option.some item)),
  (match Option.some item with
    | Option.none => h_1 ()
    | Option.some item => h_2 item) =
    h_2 item
'_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.nameAction.match_1.eq_2' does not depend on any axioms
YULANG_AUDIT_END _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.nameAction.match_1.eq_2
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.substitution_word_push
@YulangClosure.NativeDictionaryDenotation.substitution_word_push : ∀ {Step : Type}
  {words : YulangClosure.NativeDictionaryDenotation.WordArena Step}
  {subs : YulangClosure.NativeDictionaryDenotation.SubArena} {handle : Option Nat}
  {as : List (YulangClosure.NativeDictionaryDenotation.Assignment Step)},
  YulangClosure.NativeDictionaryDenotation.substitution words subs handle = Option.some as →
    ∀ (node : YulangClosure.NativeDictionaryDenotation.WordNode Step),
      YulangClosure.NativeDictionaryDenotation.substitution (words.push node) subs handle = Option.some as
'YulangClosure.NativeDictionaryDenotation.substitution_word_push' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.substitution_word_push
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.substitution.eq_2
@YulangClosure.NativeDictionaryDenotation.substitution.eq_2 : ∀ {Step : Type}
  (words : YulangClosure.NativeDictionaryDenotation.WordArena Step)
  (subs : YulangClosure.NativeDictionaryDenotation.SubArena) (i : Nat),
  YulangClosure.NativeDictionaryDenotation.substitution words subs (Option.some i) =
    YulangClosure.NativeDictionaryDenotation.subAt words subs i
'YulangClosure.NativeDictionaryDenotation.substitution.eq_2' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.substitution.eq_2
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.action_append
@YulangClosure.NativeDictionaryDenotation.action_append : ∀ {Step : Type}
  (a b : List (YulangClosure.NativeDictionaryDenotation.Assignment Step))
  (c : YulangClosure.NativeDictionaryDenotation.Context Step),
  YulangClosure.NativeDictionaryDenotation.action (a ++ b) c =
    YulangClosure.NativeDictionaryDenotation.action b (YulangClosure.NativeDictionaryDenotation.action a c)
'YulangClosure.NativeDictionaryDenotation.action_append' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.action_append
YULANG_AUDIT_BEGIN _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.nameAction.match_1.eq_1
@_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.nameAction.match_1.eq_1 : ∀
  {Step : Type} (motive : Option Step → Sort u_1) (h_1 : Unit → motive Option.none)
  (h_2 : (item : Step) → motive (Option.some item)),
  (match Option.none with
    | Option.none => h_1 ()
    | Option.some item => h_2 item) =
    h_1 ()
'_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.nameAction.match_1.eq_1' does not depend on any axioms
YULANG_AUDIT_END _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.nameAction.match_1.eq_1
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.then_denotes
@YulangClosure.NativeDictionaryDenotation.then_denotes : ∀ {Step : Type}
  {words : YulangClosure.NativeDictionaryDenotation.WordArena Step}
  {subs : YulangClosure.NativeDictionaryDenotation.SubArena} {first second : Option Nat}
  {a b : List (YulangClosure.NativeDictionaryDenotation.Assignment Step)},
  YulangClosure.NativeDictionaryDenotation.substitution words subs first = Option.some a →
    YulangClosure.NativeDictionaryDenotation.substitution words subs second = Option.some b →
      YulangClosure.NativeDictionaryDenotation.substitution words
          (YulangClosure.NativeDictionaryDenotation.compose subs first second).fst
          (YulangClosure.NativeDictionaryDenotation.compose subs first second).snd =
        Option.some (a ++ b)
'YulangClosure.NativeDictionaryDenotation.then_denotes' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.then_denotes
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.WordArena.push.inj
@YulangClosure.NativeDictionaryDenotation.WordArena.push.inj : ∀ {Step : Type}
  {old : YulangClosure.NativeDictionaryDenotation.WordArena Step}
  {node : YulangClosure.NativeDictionaryDenotation.WordNode Step}
  {old_1 : YulangClosure.NativeDictionaryDenotation.WordArena Step}
  {node_1 : YulangClosure.NativeDictionaryDenotation.WordNode Step},
  old.push node = old_1.push node_1 → old = old_1 ∧ node = node_1
'YulangClosure.NativeDictionaryDenotation.WordArena.push.inj' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.WordArena.push.inj
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.assign.eq_1
@YulangClosure.NativeDictionaryDenotation.assign.eq_1 : ∀ {Step : Type}
  (a : YulangClosure.NativeDictionaryDenotation.Assignment Step)
  (c : YulangClosure.NativeDictionaryDenotation.Context Step),
  YulangClosure.NativeDictionaryDenotation.assign a c =
    if c.base = Option.some a.scope then { base := a.replacement.base, word := a.replacement.word ++ c.word } else c
'YulangClosure.NativeDictionaryDenotation.assign.eq_1' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.assign.eq_1
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.State.mk.injEq
YulangClosure.NativeDictionaryDenotation.State.mk.injEq : ∀
  (context : YulangClosure.NativeDictionaryDenotation.RawContext) (substitution : Option Nat)
  (context_1 : YulangClosure.NativeDictionaryDenotation.RawContext) (substitution_1 : Option Nat),
  ({ context := context, substitution := substitution } = { context := context_1, substitution := substitution_1 }) =
    (context = context_1 ∧ substitution = substitution_1)
'YulangClosure.NativeDictionaryDenotation.State.mk.injEq' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.State.mk.injEq
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.subAt.eq_3
@YulangClosure.NativeDictionaryDenotation.subAt.eq_3 : ∀ {Step : Type}
  (words : YulangClosure.NativeDictionaryDenotation.WordArena Step) (x : Nat)
  (old : YulangClosure.NativeDictionaryDenotation.SubArena) (first second : Nat),
  YulangClosure.NativeDictionaryDenotation.subAt words
      (old.push (YulangClosure.NativeDictionaryDenotation.SubNode.then first second)) x =
    if x = old.size then do
      let a ← YulangClosure.NativeDictionaryDenotation.subAt words old first
      let b ← YulangClosure.NativeDictionaryDenotation.subAt words old second
      Pure.pure (a ++ b)
    else YulangClosure.NativeDictionaryDenotation.subAt words old x
'YulangClosure.NativeDictionaryDenotation.subAt.eq_3' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.subAt.eq_3
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.NameResult.mk.injEq
@YulangClosure.NativeDictionaryDenotation.NameResult.mk.injEq : ∀ {Step : Type}
  (words : YulangClosure.NativeDictionaryDenotation.WordArena Step)
  (substitutions : YulangClosure.NativeDictionaryDenotation.SubArena) (result : Option Nat)
  (words_1 : YulangClosure.NativeDictionaryDenotation.WordArena Step)
  (substitutions_1 : YulangClosure.NativeDictionaryDenotation.SubArena) (result_1 : Option Nat),
  ({ words := words, substitutions := substitutions, result := result } =
      { words := words_1, substitutions := substitutions_1, result := result_1 }) =
    (words = words_1 ∧ substitutions = substitutions_1 ∧ result = result_1)
'YulangClosure.NativeDictionaryDenotation.NameResult.mk.injEq' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.NameResult.mk.injEq
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.nameChecked.eq_2
@YulangClosure.NativeDictionaryDenotation.nameChecked.eq_2 : ∀ {Step : Type}
  (defaults : Nat → Option YulangClosure.NativeDictionaryDenotation.RawContext)
  (words : YulangClosure.NativeDictionaryDenotation.WordArena Step)
  (subs : YulangClosure.NativeDictionaryDenotation.SubArena) (value : Option Nat)
  (current : YulangClosure.NativeDictionaryDenotation.State) (cell : Nat) (item : Step),
  YulangClosure.NativeDictionaryDenotation.nameChecked defaults words subs value current cell (Option.some item) =
    match defaults cell with
    | Option.none => Option.none
    | Option.some val =>
      Option.some (YulangClosure.NativeDictionaryDenotation.name words subs value current cell (Option.some item))
'YulangClosure.NativeDictionaryDenotation.nameChecked.eq_2' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.nameChecked.eq_2
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.WordArena.empty.sizeOf_spec
@YulangClosure.NativeDictionaryDenotation.WordArena.empty.sizeOf_spec : ∀ {Step : Type} [inst : SizeOf Step],
  SizeOf.sizeOf YulangClosure.NativeDictionaryDenotation.WordArena.empty = 1
'YulangClosure.NativeDictionaryDenotation.WordArena.empty.sizeOf_spec' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.WordArena.empty.sizeOf_spec
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.SubArena.push.injEq
YulangClosure.NativeDictionaryDenotation.SubArena.push.injEq : ∀
  (old : YulangClosure.NativeDictionaryDenotation.SubArena) (node : YulangClosure.NativeDictionaryDenotation.SubNode)
  (old_1 : YulangClosure.NativeDictionaryDenotation.SubArena)
  (node_1 : YulangClosure.NativeDictionaryDenotation.SubNode),
  (old.push node = old_1.push node_1) = (old = old_1 ∧ node = node_1)
'YulangClosure.NativeDictionaryDenotation.SubArena.push.injEq' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.SubArena.push.injEq
YULANG_AUDIT_BEGIN _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.subAt.match_1.eq_2
_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.subAt.match_1.eq_2 : ∀
  (motive : YulangClosure.NativeDictionaryDenotation.SubNode → Sort u_1) (first second : Nat)
  (h_1 :
    (scope : Nat) →
      (raw : YulangClosure.NativeDictionaryDenotation.RawContext) →
        motive (YulangClosure.NativeDictionaryDenotation.SubNode.assign scope raw))
  (h_2 : (first second : Nat) → motive (YulangClosure.NativeDictionaryDenotation.SubNode.then first second)),
  (match YulangClosure.NativeDictionaryDenotation.SubNode.then first second with
    | YulangClosure.NativeDictionaryDenotation.SubNode.assign scope raw => h_1 scope raw
    | YulangClosure.NativeDictionaryDenotation.SubNode.then first second => h_2 first second) =
    h_2 first second
'_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.subAt.match_1.eq_2' does not depend on any axioms
YULANG_AUDIT_END _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.subAt.match_1.eq_2
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.compose_keeps_old
@YulangClosure.NativeDictionaryDenotation.compose_keeps_old : ∀ {Step : Type}
  {words : YulangClosure.NativeDictionaryDenotation.WordArena Step}
  {subs : YulangClosure.NativeDictionaryDenotation.SubArena} {handle : Option Nat}
  {as : List (YulangClosure.NativeDictionaryDenotation.Assignment Step)},
  YulangClosure.NativeDictionaryDenotation.substitution words subs handle = Option.some as →
    ∀ (first second : Option Nat),
      YulangClosure.NativeDictionaryDenotation.substitution words
          (YulangClosure.NativeDictionaryDenotation.compose subs first second).fst handle =
        Option.some as
'YulangClosure.NativeDictionaryDenotation.compose_keeps_old' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.compose_keeps_old
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.empty_defaults_valid
@YulangClosure.NativeDictionaryDenotation.empty_defaults_valid : ∀ {Step : Type}
  (words : YulangClosure.NativeDictionaryDenotation.WordArena Step),
  YulangClosure.NativeDictionaryDenotation.DefaultsValid words fun x => Option.none
'YulangClosure.NativeDictionaryDenotation.empty_defaults_valid' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.empty_defaults_valid
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.SubNode.then.sizeOf_spec
YulangClosure.NativeDictionaryDenotation.SubNode.then.sizeOf_spec : ∀ (first second : Nat),
  SizeOf.sizeOf (YulangClosure.NativeDictionaryDenotation.SubNode.then first second) =
    1 + SizeOf.sizeOf first + SizeOf.sizeOf second
'YulangClosure.NativeDictionaryDenotation.SubNode.then.sizeOf_spec' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.SubNode.then.sizeOf_spec
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.word.eq_2
@YulangClosure.NativeDictionaryDenotation.word.eq_2 : ∀ {Step : Type}
  (arena : YulangClosure.NativeDictionaryDenotation.WordArena Step) (i : Nat),
  YulangClosure.NativeDictionaryDenotation.word arena (Option.some i) =
    YulangClosure.NativeDictionaryDenotation.wordAt arena i
'YulangClosure.NativeDictionaryDenotation.word.eq_2' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.word.eq_2
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.name_checked_dictionary_denotation
@YulangClosure.NativeDictionaryDenotation.name_checked_dictionary_denotation : ∀ {Step World Site Binding : Type}
  (dictionary : World → List Step → Site → Option Binding) (witness : World) (site : Site)
  {words : YulangClosure.NativeDictionaryDenotation.WordArena Step}
  {subs : YulangClosure.NativeDictionaryDenotation.SubArena} {value : Option Nat}
  {current : YulangClosure.NativeDictionaryDenotation.State}
  {v c : List (YulangClosure.NativeDictionaryDenotation.Assignment Step)}
  {caller input : YulangClosure.NativeDictionaryDenotation.Context Step}
  {raw : YulangClosure.NativeDictionaryDenotation.RawContext}
  {defaults : Nat → Option YulangClosure.NativeDictionaryDenotation.RawContext},
  YulangClosure.NativeDictionaryDenotation.DefaultsValid words defaults →
    YulangClosure.NativeDictionaryDenotation.substitution words subs value = Option.some v →
      YulangClosure.NativeDictionaryDenotation.substitution words subs current.substitution = Option.some c →
        YulangClosure.NativeDictionaryDenotation.context words current.context = Option.some caller →
          YulangClosure.NativeDictionaryDenotation.context words raw = Option.some input →
            ∀ (fuel cell : Nat) (instantiate : Option Step),
              (instantiate.isSome = Bool.true → (defaults cell).isSome = Bool.true) →
                ((YulangClosure.NativeDictionaryDenotation.nameChecked defaults words subs value current cell
                        instantiate).bind
                    fun result =>
                    (YulangClosure.NativeDictionaryDenotation.dispatchMeaning result.words result.substitutions
                          (YulangClosure.NativeDictionaryDenotation.defaultMeaning result.words defaults) fuel
                          { context := raw, substitution := result.result }).bind
                      fun key => dictionary witness key site) =
                  (YulangClosure.NativeDictionaryDenotation.resolve
                        (YulangClosure.NativeDictionaryDenotation.defaultMeaning words defaults)
                        (YulangClosure.NativeDictionaryDenotation.nameAction v c caller cell instantiate) fuel
                        (YulangClosure.NativeDictionaryDenotation.action
                          (YulangClosure.NativeDictionaryDenotation.nameAction v c caller cell instantiate) input)).bind
                    fun key => dictionary witness key site
'YulangClosure.NativeDictionaryDenotation.name_checked_dictionary_denotation' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.name_checked_dictionary_denotation
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.Context.mk.sizeOf_spec
@YulangClosure.NativeDictionaryDenotation.Context.mk.sizeOf_spec : ∀ {Step : Type} [inst : SizeOf Step]
  (base : Option Nat) (word : List Step),
  SizeOf.sizeOf { base := base, word := word } = 1 + SizeOf.sizeOf base + SizeOf.sizeOf word
'YulangClosure.NativeDictionaryDenotation.Context.mk.sizeOf_spec' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.Context.mk.sizeOf_spec
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.SubNode.then.inj
@YulangClosure.NativeDictionaryDenotation.SubNode.then.inj : ∀ {first second first_1 second_1 : Nat},
  YulangClosure.NativeDictionaryDenotation.SubNode.then first second =
      YulangClosure.NativeDictionaryDenotation.SubNode.then first_1 second_1 →
    first = first_1 ∧ second = second_1
'YulangClosure.NativeDictionaryDenotation.SubNode.then.inj' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.SubNode.then.inj
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.WordArena.push.injEq
@YulangClosure.NativeDictionaryDenotation.WordArena.push.injEq : ∀ {Step : Type}
  (old : YulangClosure.NativeDictionaryDenotation.WordArena Step)
  (node : YulangClosure.NativeDictionaryDenotation.WordNode Step)
  (old_1 : YulangClosure.NativeDictionaryDenotation.WordArena Step)
  (node_1 : YulangClosure.NativeDictionaryDenotation.WordNode Step),
  (old.push node = old_1.push node_1) = (old = old_1 ∧ node = node_1)
'YulangClosure.NativeDictionaryDenotation.WordArena.push.injEq' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.WordArena.push.injEq
YULANG_AUDIT_BEGIN _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.join.match_1.eq_1
_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.join.match_1.eq_1 : ∀
  (motive : Option Nat → Option Nat → Sort u_1) (h : Option Nat) (h_1 : (h : Option Nat) → motive Option.none h)
  (h_2 : (h : Option Nat) → motive h Option.none) (h_3 : (i j : Nat) → motive (Option.some i) (Option.some j)),
  (match Option.none, h with
    | Option.none, h => h_1 h
    | h, Option.none => h_2 h
    | Option.some i, Option.some j => h_3 i j) =
    h_1 h
'_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.join.match_1.eq_1' does not depend on any axioms
YULANG_AUDIT_END _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.join.match_1.eq_1
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.subAt_word_transport
@YulangClosure.NativeDictionaryDenotation.subAt_word_transport : ∀ {Step : Type}
  {old new : YulangClosure.NativeDictionaryDenotation.WordArena Step},
  (∀ (h : Option Nat) (w : List Step),
      YulangClosure.NativeDictionaryDenotation.word old h = Option.some w →
        YulangClosure.NativeDictionaryDenotation.word new h = Option.some w) →
    ∀ {subs : YulangClosure.NativeDictionaryDenotation.SubArena} {i : Nat}
      {as : List (YulangClosure.NativeDictionaryDenotation.Assignment Step)},
      YulangClosure.NativeDictionaryDenotation.subAt old subs i = Option.some as →
        YulangClosure.NativeDictionaryDenotation.subAt new subs i = Option.some as
'YulangClosure.NativeDictionaryDenotation.subAt_word_transport' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.subAt_word_transport
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.resolve_default
@YulangClosure.NativeDictionaryDenotation.resolve_default : ∀ {Step : Type}
  {defaults : Nat → Option (YulangClosure.NativeDictionaryDenotation.Context Step)} {scope : Nat}
  {parent : YulangClosure.NativeDictionaryDenotation.Context Step},
  defaults scope = Option.some parent →
    ∀ (sub : List (YulangClosure.NativeDictionaryDenotation.Assignment Step)) (fuel : Nat) (items : List Step),
      YulangClosure.NativeDictionaryDenotation.resolve defaults sub (fuel + 1)
          { base := Option.some scope, word := items } =
        YulangClosure.NativeDictionaryDenotation.resolve defaults sub fuel
          { base := (YulangClosure.NativeDictionaryDenotation.action sub parent).base,
            word := (YulangClosure.NativeDictionaryDenotation.action sub parent).word ++ items }
'YulangClosure.NativeDictionaryDenotation.resolve_default' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.resolve_default
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.instDecidableEqRawContext.decEq._proof_1
YulangClosure.NativeDictionaryDenotation.instDecidableEqRawContext.decEq._proof_1 : ∀ (a a_1 : Option Nat),
  { base := a, word := a_1 } = { base := a, word := a_1 }
'YulangClosure.NativeDictionaryDenotation.instDecidableEqRawContext.decEq._proof_1' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.instDecidableEqRawContext.decEq._proof_1
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.assignRaw.eq_1
@YulangClosure.NativeDictionaryDenotation.assignRaw.eq_1 : ∀ {Step : Type}
  (words : YulangClosure.NativeDictionaryDenotation.WordArena Step) (scope : Nat)
  (replacement input : YulangClosure.NativeDictionaryDenotation.RawContext),
  YulangClosure.NativeDictionaryDenotation.assignRaw words scope replacement input =
    if input.base = Option.some scope then
      have joined := YulangClosure.NativeDictionaryDenotation.join words replacement.word input.word;
      (joined.fst, { base := replacement.base, word := joined.snd })
    else (words, input)
'YulangClosure.NativeDictionaryDenotation.assignRaw.eq_1' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.assignRaw.eq_1
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.SubNode.then.injEq
YulangClosure.NativeDictionaryDenotation.SubNode.then.injEq : ∀ (first second first_1 second_1 : Nat),
  (YulangClosure.NativeDictionaryDenotation.SubNode.then first second =
      YulangClosure.NativeDictionaryDenotation.SubNode.then first_1 second_1) =
    (first = first_1 ∧ second = second_1)
'YulangClosure.NativeDictionaryDenotation.SubNode.then.injEq' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.SubNode.then.injEq
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.RawContext.mk.inj
@YulangClosure.NativeDictionaryDenotation.RawContext.mk.inj : ∀ {base word base_1 word_1 : Option Nat},
  { base := base, word := word } = { base := base_1, word := word_1 } → base = base_1 ∧ word = word_1
'YulangClosure.NativeDictionaryDenotation.RawContext.mk.inj' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.RawContext.mk.inj
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.name_dictionary_denotation
@YulangClosure.NativeDictionaryDenotation.name_dictionary_denotation : ∀ {Step World Site Binding : Type}
  (dictionary : World → List Step → Site → Option Binding) (witness : World) (site : Site)
  {words : YulangClosure.NativeDictionaryDenotation.WordArena Step}
  {subs : YulangClosure.NativeDictionaryDenotation.SubArena} {value : Option Nat}
  {current : YulangClosure.NativeDictionaryDenotation.State}
  {v c : List (YulangClosure.NativeDictionaryDenotation.Assignment Step)}
  {caller input : YulangClosure.NativeDictionaryDenotation.Context Step}
  {raw : YulangClosure.NativeDictionaryDenotation.RawContext},
  YulangClosure.NativeDictionaryDenotation.substitution words subs value = Option.some v →
    YulangClosure.NativeDictionaryDenotation.substitution words subs current.substitution = Option.some c →
      YulangClosure.NativeDictionaryDenotation.context words current.context = Option.some caller →
        YulangClosure.NativeDictionaryDenotation.context words raw = Option.some input →
          ∀ (defaults : Nat → Option (YulangClosure.NativeDictionaryDenotation.Context Step)) (fuel cell : Nat)
            (instantiate : Option Step),
            ((YulangClosure.NativeDictionaryDenotation.dispatchMeaning
                    (YulangClosure.NativeDictionaryDenotation.name words subs value current cell instantiate).words
                    (YulangClosure.NativeDictionaryDenotation.name words subs value current cell
                        instantiate).substitutions
                    defaults fuel
                    { context := raw,
                      substitution :=
                        (YulangClosure.NativeDictionaryDenotation.name words subs value current cell
                            instantiate).result }).bind
                fun key => dictionary witness key site) =
              (YulangClosure.NativeDictionaryDenotation.resolve defaults
                    (YulangClosure.NativeDictionaryDenotation.nameAction v c caller cell instantiate) fuel
                    (YulangClosure.NativeDictionaryDenotation.action
                      (YulangClosure.NativeDictionaryDenotation.nameAction v c caller cell instantiate) input)).bind
                fun key => dictionary witness key site
'YulangClosure.NativeDictionaryDenotation.name_dictionary_denotation' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.name_dictionary_denotation
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.State.mk.inj
@YulangClosure.NativeDictionaryDenotation.State.mk.inj : ∀
  {context : YulangClosure.NativeDictionaryDenotation.RawContext} {substitution : Option Nat}
  {context_1 : YulangClosure.NativeDictionaryDenotation.RawContext} {substitution_1 : Option Nat},
  { context := context, substitution := substitution } = { context := context_1, substitution := substitution_1 } →
    context = context_1 ∧ substitution = substitution_1
'YulangClosure.NativeDictionaryDenotation.State.mk.inj' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.State.mk.inj
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.SubArena.brecOn.eq
@YulangClosure.NativeDictionaryDenotation.SubArena.brecOn.eq : ∀
  {motive : YulangClosure.NativeDictionaryDenotation.SubArena → Sort u_1}
  (t : YulangClosure.NativeDictionaryDenotation.SubArena)
  (F_1 :
    (t : YulangClosure.NativeDictionaryDenotation.SubArena) →
      YulangClosure.NativeDictionaryDenotation.SubArena.below t → motive t),
  YulangClosure.NativeDictionaryDenotation.SubArena.brecOn t F_1 =
    F_1 t (YulangClosure.NativeDictionaryDenotation.SubArena.brecOn.go t F_1).2
'YulangClosure.NativeDictionaryDenotation.SubArena.brecOn.eq' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.SubArena.brecOn.eq
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.name_checked_denotes
@YulangClosure.NativeDictionaryDenotation.name_checked_denotes : ∀ {Step : Type}
  {defaults : Nat → Option YulangClosure.NativeDictionaryDenotation.RawContext}
  {words : YulangClosure.NativeDictionaryDenotation.WordArena Step}
  {subs : YulangClosure.NativeDictionaryDenotation.SubArena} {value : Option Nat}
  {current : YulangClosure.NativeDictionaryDenotation.State}
  {v c : List (YulangClosure.NativeDictionaryDenotation.Assignment Step)}
  {caller : YulangClosure.NativeDictionaryDenotation.Context Step},
  YulangClosure.NativeDictionaryDenotation.substitution words subs value = Option.some v →
    YulangClosure.NativeDictionaryDenotation.substitution words subs current.substitution = Option.some c →
      YulangClosure.NativeDictionaryDenotation.context words current.context = Option.some caller →
        ∀ (cell : Nat) (instantiate : Option Step),
          (instantiate.isSome = Bool.true → (defaults cell).isSome = Bool.true) →
            ((YulangClosure.NativeDictionaryDenotation.nameChecked defaults words subs value current cell
                    instantiate).bind
                fun result =>
                YulangClosure.NativeDictionaryDenotation.substitution result.words result.substitutions result.result) =
              Option.some (YulangClosure.NativeDictionaryDenotation.nameAction v c caller cell instantiate)
'YulangClosure.NativeDictionaryDenotation.name_checked_denotes' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.name_checked_denotes
YULANG_AUDIT_BEGIN _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.applyDag.match_1.eq_1
_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.applyDag.match_1.eq_1 : ∀
  (motive :
    YulangClosure.NativeDictionaryDenotation.SubArena →
      Nat → YulangClosure.NativeDictionaryDenotation.RawContext → Sort u_1)
  (x : Nat) (x_1 : YulangClosure.NativeDictionaryDenotation.RawContext)
  (h_1 :
    (x : Nat) →
      (x_2 : YulangClosure.NativeDictionaryDenotation.RawContext) →
        motive YulangClosure.NativeDictionaryDenotation.SubArena.empty x x_2)
  (h_2 :
    (before : YulangClosure.NativeDictionaryDenotation.SubArena) →
      (node : YulangClosure.NativeDictionaryDenotation.SubNode) →
        (i : Nat) → (input : YulangClosure.NativeDictionaryDenotation.RawContext) → motive (before.push node) i input),
  (match YulangClosure.NativeDictionaryDenotation.SubArena.empty, x, x_1 with
    | YulangClosure.NativeDictionaryDenotation.SubArena.empty, x, x_2 => h_1 x x_2
    | before.push node, i, input => h_2 before node i input) =
    h_1 x x_1
'_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.applyDag.match_1.eq_1' does not depend on any axioms
YULANG_AUDIT_END _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.applyDag.match_1.eq_1
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.substitution.eq_1
@YulangClosure.NativeDictionaryDenotation.substitution.eq_1 : ∀ {Step : Type}
  (words : YulangClosure.NativeDictionaryDenotation.WordArena Step)
  (subs : YulangClosure.NativeDictionaryDenotation.SubArena),
  YulangClosure.NativeDictionaryDenotation.substitution words subs Option.none = Option.some []
'YulangClosure.NativeDictionaryDenotation.substitution.eq_1' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.substitution.eq_1
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.join_denotes
@YulangClosure.NativeDictionaryDenotation.join_denotes : ∀ {Step : Type}
  {arena : YulangClosure.NativeDictionaryDenotation.WordArena Step} {a b : Option Nat} {x y : List Step},
  YulangClosure.NativeDictionaryDenotation.word arena a = Option.some x →
    YulangClosure.NativeDictionaryDenotation.word arena b = Option.some y →
      YulangClosure.NativeDictionaryDenotation.word (YulangClosure.NativeDictionaryDenotation.join arena a b).fst
          (YulangClosure.NativeDictionaryDenotation.join arena a b).snd =
        Option.some (x ++ y)
'YulangClosure.NativeDictionaryDenotation.join_denotes' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.join_denotes
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.applyDag.eq_3
@YulangClosure.NativeDictionaryDenotation.applyDag.eq_3 : ∀ {Step : Type}
  (words : YulangClosure.NativeDictionaryDenotation.WordArena Step) (x : Nat)
  (x_1 : YulangClosure.NativeDictionaryDenotation.RawContext)
  (before : YulangClosure.NativeDictionaryDenotation.SubArena) (first second : Nat),
  YulangClosure.NativeDictionaryDenotation.applyDag words
      (before.push (YulangClosure.NativeDictionaryDenotation.SubNode.then first second)) x x_1 =
    if x = before.size then do
      let middle ← YulangClosure.NativeDictionaryDenotation.applyDag words before first x_1
      YulangClosure.NativeDictionaryDenotation.applyDag middle.fst before second middle.snd
    else YulangClosure.NativeDictionaryDenotation.applyDag words before x x_1
'YulangClosure.NativeDictionaryDenotation.applyDag.eq_3' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.applyDag.eq_3
YULANG_AUDIT_BEGIN _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.wordAt.match_3.eq_1
@_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.wordAt.match_3.eq_1 : ∀
  {Step : Type} (motive : YulangClosure.NativeDictionaryDenotation.WordArena Step → Nat → Sort u_1) (x : Nat)
  (h_1 : (x : Nat) → motive YulangClosure.NativeDictionaryDenotation.WordArena.empty x)
  (h_2 :
    (old : YulangClosure.NativeDictionaryDenotation.WordArena Step) →
      (node : YulangClosure.NativeDictionaryDenotation.WordNode Step) → (i : Nat) → motive (old.push node) i),
  (match YulangClosure.NativeDictionaryDenotation.WordArena.empty, x with
    | YulangClosure.NativeDictionaryDenotation.WordArena.empty, x => h_1 x
    | old.push node, i => h_2 old node i) =
    h_1 x
'_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.wordAt.match_3.eq_1' does not depend on any axioms
YULANG_AUDIT_END _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.wordAt.match_3.eq_1
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.compose.eq_2
YulangClosure.NativeDictionaryDenotation.compose.eq_2 : ∀ (subs : YulangClosure.NativeDictionaryDenotation.SubArena)
  (first : Option Nat),
  (first = Option.none → False) →
    YulangClosure.NativeDictionaryDenotation.compose subs first Option.none = (subs, first)
'YulangClosure.NativeDictionaryDenotation.compose.eq_2' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.compose.eq_2
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.RawContext.mk.injEq
YulangClosure.NativeDictionaryDenotation.RawContext.mk.injEq : ∀ (base word base_1 word_1 : Option Nat),
  ({ base := base, word := word } = { base := base_1, word := word_1 }) = (base = base_1 ∧ word = word_1)
'YulangClosure.NativeDictionaryDenotation.RawContext.mk.injEq' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.RawContext.mk.injEq
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.initializer_defaults_valid
@YulangClosure.NativeDictionaryDenotation.initializer_defaults_valid : ∀ {Step : Type}
  {words : YulangClosure.NativeDictionaryDenotation.WordArena Step}
  {defaults : Nat → Option YulangClosure.NativeDictionaryDenotation.RawContext},
  YulangClosure.NativeDictionaryDenotation.DefaultsValid words defaults →
    ∀ (cell : Nat) (parent : YulangClosure.NativeDictionaryDenotation.State)
      {c : YulangClosure.NativeDictionaryDenotation.Context Step},
      YulangClosure.NativeDictionaryDenotation.context words parent.context = Option.some c →
        YulangClosure.NativeDictionaryDenotation.DefaultsValid words
          (YulangClosure.NativeDictionaryDenotation.initializer defaults cell parent).fst
'YulangClosure.NativeDictionaryDenotation.initializer_defaults_valid' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.initializer_defaults_valid
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.SubArena.push.inj
@YulangClosure.NativeDictionaryDenotation.SubArena.push.inj : ∀
  {old : YulangClosure.NativeDictionaryDenotation.SubArena} {node : YulangClosure.NativeDictionaryDenotation.SubNode}
  {old_1 : YulangClosure.NativeDictionaryDenotation.SubArena}
  {node_1 : YulangClosure.NativeDictionaryDenotation.SubNode},
  old.push node = old_1.push node_1 → old = old_1 ∧ node = node_1
'YulangClosure.NativeDictionaryDenotation.SubArena.push.inj' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.SubArena.push.inj
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.instDecidableEqContext.decEq._proof_1
@YulangClosure.NativeDictionaryDenotation.instDecidableEqContext.decEq._proof_1 : ∀ {Step : Type} (a : Option Nat)
  (a_1 : List Step), { base := a, word := a_1 } = { base := a, word := a_1 }
'YulangClosure.NativeDictionaryDenotation.instDecidableEqContext.decEq._proof_1' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.instDecidableEqContext.decEq._proof_1
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.wordAt_push_old
@YulangClosure.NativeDictionaryDenotation.wordAt_push_old : ∀ {Step : Type}
  {arena : YulangClosure.NativeDictionaryDenotation.WordArena Step} {i : Nat} {w : List Step},
  YulangClosure.NativeDictionaryDenotation.wordAt arena i = Option.some w →
    ∀ (node : YulangClosure.NativeDictionaryDenotation.WordNode Step),
      YulangClosure.NativeDictionaryDenotation.wordAt (arena.push node) i = Option.some w
'YulangClosure.NativeDictionaryDenotation.wordAt_push_old' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.wordAt_push_old
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.Assignment.mk.injEq
@YulangClosure.NativeDictionaryDenotation.Assignment.mk.injEq : ∀ {Step : Type} (scope : Nat)
  (replacement : YulangClosure.NativeDictionaryDenotation.Context Step) (scope_1 : Nat)
  (replacement_1 : YulangClosure.NativeDictionaryDenotation.Context Step),
  ({ scope := scope, replacement := replacement } = { scope := scope_1, replacement := replacement_1 }) =
    (scope = scope_1 ∧ replacement = replacement_1)
'YulangClosure.NativeDictionaryDenotation.Assignment.mk.injEq' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.Assignment.mk.injEq
YULANG_AUDIT_BEGIN _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.wordAt.match_3.eq_2
@_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.wordAt.match_3.eq_2 : ∀
  {Step : Type} (motive : YulangClosure.NativeDictionaryDenotation.WordArena Step → Nat → Sort u_1)
  (old : YulangClosure.NativeDictionaryDenotation.WordArena Step)
  (node : YulangClosure.NativeDictionaryDenotation.WordNode Step) (i : Nat)
  (h_1 : (x : Nat) → motive YulangClosure.NativeDictionaryDenotation.WordArena.empty x)
  (h_2 :
    (old : YulangClosure.NativeDictionaryDenotation.WordArena Step) →
      (node : YulangClosure.NativeDictionaryDenotation.WordNode Step) → (i : Nat) → motive (old.push node) i),
  (match old.push node, i with
    | YulangClosure.NativeDictionaryDenotation.WordArena.empty, x => h_1 x
    | old.push node, i => h_2 old node i) =
    h_2 old node i
'_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.wordAt.match_3.eq_2' does not depend on any axioms
YULANG_AUDIT_END _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.wordAt.match_3.eq_2
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.nameAction.eq_2
@YulangClosure.NativeDictionaryDenotation.nameAction.eq_2 : ∀ {Step : Type}
  (value current : List (YulangClosure.NativeDictionaryDenotation.Assignment Step))
  (caller : YulangClosure.NativeDictionaryDenotation.Context Step) (cell : Nat) (item : Step),
  YulangClosure.NativeDictionaryDenotation.nameAction value current caller cell (Option.some item) =
    value ++ [{ scope := cell, replacement := { base := caller.base, word := caller.word ++ [item] } }] ++ current
'YulangClosure.NativeDictionaryDenotation.nameAction.eq_2' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.nameAction.eq_2
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.WordNode.step.inj
@YulangClosure.NativeDictionaryDenotation.WordNode.step.inj : ∀ {Step : Type} {previous : Option Nat} {item : Step}
  {previous_1 : Option Nat} {item_1 : Step},
  YulangClosure.NativeDictionaryDenotation.WordNode.step previous item =
      YulangClosure.NativeDictionaryDenotation.WordNode.step previous_1 item_1 →
    previous = previous_1 ∧ item = item_1
'YulangClosure.NativeDictionaryDenotation.WordNode.step.inj' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.WordNode.step.inj
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.wordAt_bound
@YulangClosure.NativeDictionaryDenotation.wordAt_bound : ∀ {Step : Type}
  {arena : YulangClosure.NativeDictionaryDenotation.WordArena Step} {i : Nat} {w : List Step},
  YulangClosure.NativeDictionaryDenotation.wordAt arena i = Option.some w → i < arena.size
'YulangClosure.NativeDictionaryDenotation.wordAt_bound' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.wordAt_bound
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.SubNode.assign.injEq
YulangClosure.NativeDictionaryDenotation.SubNode.assign.injEq : ∀ (scope : Nat)
  (replacement : YulangClosure.NativeDictionaryDenotation.RawContext) (scope_1 : Nat)
  (replacement_1 : YulangClosure.NativeDictionaryDenotation.RawContext),
  (YulangClosure.NativeDictionaryDenotation.SubNode.assign scope replacement =
      YulangClosure.NativeDictionaryDenotation.SubNode.assign scope_1 replacement_1) =
    (scope = scope_1 ∧ replacement = replacement_1)
'YulangClosure.NativeDictionaryDenotation.SubNode.assign.injEq' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.SubNode.assign.injEq
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.name_denotes
@YulangClosure.NativeDictionaryDenotation.name_denotes : ∀ {Step : Type}
  {words : YulangClosure.NativeDictionaryDenotation.WordArena Step}
  {subs : YulangClosure.NativeDictionaryDenotation.SubArena} {value : Option Nat}
  {current : YulangClosure.NativeDictionaryDenotation.State}
  {v c : List (YulangClosure.NativeDictionaryDenotation.Assignment Step)}
  {caller : YulangClosure.NativeDictionaryDenotation.Context Step},
  YulangClosure.NativeDictionaryDenotation.substitution words subs value = Option.some v →
    YulangClosure.NativeDictionaryDenotation.substitution words subs current.substitution = Option.some c →
      YulangClosure.NativeDictionaryDenotation.context words current.context = Option.some caller →
        ∀ (cell : Nat) (instantiate : Option Step),
          YulangClosure.NativeDictionaryDenotation.substitution
              (YulangClosure.NativeDictionaryDenotation.name words subs value current cell instantiate).words
              (YulangClosure.NativeDictionaryDenotation.name words subs value current cell instantiate).substitutions
              (YulangClosure.NativeDictionaryDenotation.name words subs value current cell instantiate).result =
            Option.some (YulangClosure.NativeDictionaryDenotation.nameAction v c caller cell instantiate)
'YulangClosure.NativeDictionaryDenotation.name_denotes' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.name_denotes
YULANG_AUDIT_BEGIN _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.word.match_1.eq_2
_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.word.match_1.eq_2 : ∀
  (motive : Option Nat → Sort u_1) (i : Nat) (h_1 : Unit → motive Option.none)
  (h_2 : (i : Nat) → motive (Option.some i)),
  (match Option.some i with
    | Option.none => h_1 ()
    | Option.some i => h_2 i) =
    h_2 i
'_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.word.match_1.eq_2' does not depend on any axioms
YULANG_AUDIT_END _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.word.match_1.eq_2
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.Context.mk.inj
@YulangClosure.NativeDictionaryDenotation.Context.mk.inj : ∀ {Step : Type} {base : Option Nat} {word : List Step}
  {base_1 : Option Nat} {word_1 : List Step},
  { base := base, word := word } = { base := base_1, word := word_1 } → base = base_1 ∧ word = word_1
'YulangClosure.NativeDictionaryDenotation.Context.mk.inj' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.Context.mk.inj
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.name_defaults_unchanged
@YulangClosure.NativeDictionaryDenotation.name_defaults_unchanged : ∀ {Step : Type}
  {words : YulangClosure.NativeDictionaryDenotation.WordArena Step}
  {defaults : Nat → Option YulangClosure.NativeDictionaryDenotation.RawContext},
  YulangClosure.NativeDictionaryDenotation.DefaultsValid words defaults →
    ∀ (subs : YulangClosure.NativeDictionaryDenotation.SubArena) (value : Option Nat)
      (current : YulangClosure.NativeDictionaryDenotation.State) (cell : Nat) (instantiate : Option Step),
      YulangClosure.NativeDictionaryDenotation.defaultMeaning
          (YulangClosure.NativeDictionaryDenotation.name words subs value current cell instantiate).words defaults =
        YulangClosure.NativeDictionaryDenotation.defaultMeaning words defaults
'YulangClosure.NativeDictionaryDenotation.name_defaults_unchanged' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.name_defaults_unchanged
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.name_raw_dictionary_denotation
@YulangClosure.NativeDictionaryDenotation.name_raw_dictionary_denotation : ∀ {Step World Site Binding : Type}
  (dictionary : World → List Step → Site → Option Binding) (witness : World) (site : Site)
  {words : YulangClosure.NativeDictionaryDenotation.WordArena Step}
  {subs : YulangClosure.NativeDictionaryDenotation.SubArena} {value : Option Nat}
  {current : YulangClosure.NativeDictionaryDenotation.State}
  {v c : List (YulangClosure.NativeDictionaryDenotation.Assignment Step)}
  {caller input : YulangClosure.NativeDictionaryDenotation.Context Step}
  {raw : YulangClosure.NativeDictionaryDenotation.RawContext}
  {defaults : Nat → Option YulangClosure.NativeDictionaryDenotation.RawContext},
  YulangClosure.NativeDictionaryDenotation.DefaultsValid words defaults →
    YulangClosure.NativeDictionaryDenotation.substitution words subs value = Option.some v →
      YulangClosure.NativeDictionaryDenotation.substitution words subs current.substitution = Option.some c →
        YulangClosure.NativeDictionaryDenotation.context words current.context = Option.some caller →
          YulangClosure.NativeDictionaryDenotation.context words raw = Option.some input →
            ∀ (fuel cell : Nat) (instantiate : Option Step),
              ((YulangClosure.NativeDictionaryDenotation.dispatchMeaning
                      (YulangClosure.NativeDictionaryDenotation.name words subs value current cell instantiate).words
                      (YulangClosure.NativeDictionaryDenotation.name words subs value current cell
                          instantiate).substitutions
                      (YulangClosure.NativeDictionaryDenotation.defaultMeaning
                        (YulangClosure.NativeDictionaryDenotation.name words subs value current cell instantiate).words
                        defaults)
                      fuel
                      { context := raw,
                        substitution :=
                          (YulangClosure.NativeDictionaryDenotation.name words subs value current cell
                              instantiate).result }).bind
                  fun key => dictionary witness key site) =
                (YulangClosure.NativeDictionaryDenotation.resolve
                      (YulangClosure.NativeDictionaryDenotation.defaultMeaning words defaults)
                      (YulangClosure.NativeDictionaryDenotation.nameAction v c caller cell instantiate) fuel
                      (YulangClosure.NativeDictionaryDenotation.action
                        (YulangClosure.NativeDictionaryDenotation.nameAction v c caller cell instantiate) input)).bind
                  fun key => dictionary witness key site
'YulangClosure.NativeDictionaryDenotation.name_raw_dictionary_denotation' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.name_raw_dictionary_denotation
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.defaultMeaning.eq_1
@YulangClosure.NativeDictionaryDenotation.defaultMeaning.eq_1 : ∀ {Step : Type}
  (words : YulangClosure.NativeDictionaryDenotation.WordArena Step)
  (defaults : Nat → Option YulangClosure.NativeDictionaryDenotation.RawContext) (cell : Nat),
  YulangClosure.NativeDictionaryDenotation.defaultMeaning words defaults cell =
    (defaults cell).bind (YulangClosure.NativeDictionaryDenotation.context words)
'YulangClosure.NativeDictionaryDenotation.defaultMeaning.eq_1' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.defaultMeaning.eq_1
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.applyDag.eq_1
@YulangClosure.NativeDictionaryDenotation.applyDag.eq_1 : ∀ {Step : Type}
  (words : YulangClosure.NativeDictionaryDenotation.WordArena Step) (x : Nat)
  (x_1 : YulangClosure.NativeDictionaryDenotation.RawContext),
  YulangClosure.NativeDictionaryDenotation.applyDag words YulangClosure.NativeDictionaryDenotation.SubArena.empty x
      x_1 =
    Option.none
'YulangClosure.NativeDictionaryDenotation.applyDag.eq_1' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.applyDag.eq_1
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.Context.mk.injEq
@YulangClosure.NativeDictionaryDenotation.Context.mk.injEq : ∀ {Step : Type} (base : Option Nat) (word : List Step)
  (base_1 : Option Nat) (word_1 : List Step),
  ({ base := base, word := word } = { base := base_1, word := word_1 }) = (base = base_1 ∧ word = word_1)
'YulangClosure.NativeDictionaryDenotation.Context.mk.injEq' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.Context.mk.injEq
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.subAt_push_old
@YulangClosure.NativeDictionaryDenotation.subAt_push_old : ∀ {Step : Type}
  {words : YulangClosure.NativeDictionaryDenotation.WordArena Step}
  {subs : YulangClosure.NativeDictionaryDenotation.SubArena} {i : Nat}
  {as : List (YulangClosure.NativeDictionaryDenotation.Assignment Step)},
  YulangClosure.NativeDictionaryDenotation.subAt words subs i = Option.some as →
    ∀ (node : YulangClosure.NativeDictionaryDenotation.SubNode),
      YulangClosure.NativeDictionaryDenotation.subAt words (subs.push node) i = Option.some as
'YulangClosure.NativeDictionaryDenotation.subAt_push_old' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.subAt_push_old
YULANG_AUDIT_BEGIN _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.subAt.match_1.eq_1
_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.subAt.match_1.eq_1 : ∀
  (motive : YulangClosure.NativeDictionaryDenotation.SubNode → Sort u_1) (scope : Nat)
  (raw : YulangClosure.NativeDictionaryDenotation.RawContext)
  (h_1 :
    (scope : Nat) →
      (raw : YulangClosure.NativeDictionaryDenotation.RawContext) →
        motive (YulangClosure.NativeDictionaryDenotation.SubNode.assign scope raw))
  (h_2 : (first second : Nat) → motive (YulangClosure.NativeDictionaryDenotation.SubNode.then first second)),
  (match YulangClosure.NativeDictionaryDenotation.SubNode.assign scope raw with
    | YulangClosure.NativeDictionaryDenotation.SubNode.assign scope raw => h_1 scope raw
    | YulangClosure.NativeDictionaryDenotation.SubNode.then first second => h_2 first second) =
    h_1 scope raw
'_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.subAt.match_1.eq_1' does not depend on any axioms
YULANG_AUDIT_END _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.subAt.match_1.eq_1
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.WordArena.push.sizeOf_spec
@YulangClosure.NativeDictionaryDenotation.WordArena.push.sizeOf_spec : ∀ {Step : Type} [inst : SizeOf Step]
  (old : YulangClosure.NativeDictionaryDenotation.WordArena Step)
  (node : YulangClosure.NativeDictionaryDenotation.WordNode Step),
  SizeOf.sizeOf (old.push node) = 1 + SizeOf.sizeOf old + SizeOf.sizeOf node
'YulangClosure.NativeDictionaryDenotation.WordArena.push.sizeOf_spec' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.WordArena.push.sizeOf_spec
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.nameAction.eq_1
@YulangClosure.NativeDictionaryDenotation.nameAction.eq_1 : ∀ {Step : Type}
  (value current : List (YulangClosure.NativeDictionaryDenotation.Assignment Step))
  (caller : YulangClosure.NativeDictionaryDenotation.Context Step) (cell : Nat),
  YulangClosure.NativeDictionaryDenotation.nameAction value current caller cell Option.none = value ++ current
'YulangClosure.NativeDictionaryDenotation.nameAction.eq_1' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.nameAction.eq_1
YULANG_AUDIT_BEGIN _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.join.match_1.eq_3
_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.join.match_1.eq_3 : ∀
  (motive : Option Nat → Option Nat → Sort u_1) (i j : Nat) (h_1 : (h : Option Nat) → motive Option.none h)
  (h_2 : (h : Option Nat) → motive h Option.none) (h_3 : (i j : Nat) → motive (Option.some i) (Option.some j)),
  (match Option.some i, Option.some j with
    | Option.none, h => h_1 h
    | h, Option.none => h_2 h
    | Option.some i, Option.some j => h_3 i j) =
    h_3 i j
'_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.join.match_1.eq_3' does not depend on any axioms
YULANG_AUDIT_END _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.join.match_1.eq_3
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.nameChecked.eq_1
@YulangClosure.NativeDictionaryDenotation.nameChecked.eq_1 : ∀ {Step : Type}
  (defaults : Nat → Option YulangClosure.NativeDictionaryDenotation.RawContext)
  (words : YulangClosure.NativeDictionaryDenotation.WordArena Step)
  (subs : YulangClosure.NativeDictionaryDenotation.SubArena) (value : Option Nat)
  (current : YulangClosure.NativeDictionaryDenotation.State) (cell : Nat),
  YulangClosure.NativeDictionaryDenotation.nameChecked defaults words subs value current cell Option.none =
    Option.some (YulangClosure.NativeDictionaryDenotation.name words subs value current cell Option.none)
'YulangClosure.NativeDictionaryDenotation.nameChecked.eq_1' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.nameChecked.eq_1
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.Assignment.mk.inj
@YulangClosure.NativeDictionaryDenotation.Assignment.mk.inj : ∀ {Step : Type} {scope : Nat}
  {replacement : YulangClosure.NativeDictionaryDenotation.Context Step} {scope_1 : Nat}
  {replacement_1 : YulangClosure.NativeDictionaryDenotation.Context Step},
  { scope := scope, replacement := replacement } = { scope := scope_1, replacement := replacement_1 } →
    scope = scope_1 ∧ replacement = replacement_1
'YulangClosure.NativeDictionaryDenotation.Assignment.mk.inj' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.Assignment.mk.inj
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.Assignment.mk.sizeOf_spec
@YulangClosure.NativeDictionaryDenotation.Assignment.mk.sizeOf_spec : ∀ {Step : Type} [inst : SizeOf Step] (scope : Nat)
  (replacement : YulangClosure.NativeDictionaryDenotation.Context Step),
  SizeOf.sizeOf { scope := scope, replacement := replacement } = 1 + SizeOf.sizeOf scope + SizeOf.sizeOf replacement
'YulangClosure.NativeDictionaryDenotation.Assignment.mk.sizeOf_spec' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.Assignment.mk.sizeOf_spec
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.instDecidableEqRawContext.decEq._proof_2
YulangClosure.NativeDictionaryDenotation.instDecidableEqRawContext.decEq._proof_2 : ∀ (a a_1 b : Option Nat),
  ¬a_1 = b → { base := a, word := a_1 } = { base := a, word := b } → False
'YulangClosure.NativeDictionaryDenotation.instDecidableEqRawContext.decEq._proof_2' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.instDecidableEqRawContext.decEq._proof_2
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.WordNode.join.injEq
@YulangClosure.NativeDictionaryDenotation.WordNode.join.injEq : ∀ {Step : Type} (left right left_1 right_1 : Nat),
  (YulangClosure.NativeDictionaryDenotation.WordNode.join left right =
      YulangClosure.NativeDictionaryDenotation.WordNode.join left_1 right_1) =
    (left = left_1 ∧ right = right_1)
'YulangClosure.NativeDictionaryDenotation.WordNode.join.injEq' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.WordNode.join.injEq
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.WordNode.join.sizeOf_spec
@YulangClosure.NativeDictionaryDenotation.WordNode.join.sizeOf_spec : ∀ {Step : Type} [inst : SizeOf Step]
  (left right : Nat),
  SizeOf.sizeOf (YulangClosure.NativeDictionaryDenotation.WordNode.join left right) =
    1 + SizeOf.sizeOf left + SizeOf.sizeOf right
'YulangClosure.NativeDictionaryDenotation.WordNode.join.sizeOf_spec' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.WordNode.join.sizeOf_spec
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.compose.eq_3
YulangClosure.NativeDictionaryDenotation.compose.eq_3 : ∀ (subs : YulangClosure.NativeDictionaryDenotation.SubArena)
  (i j : Nat),
  YulangClosure.NativeDictionaryDenotation.compose subs (Option.some i) (Option.some j) =
    (subs.push (YulangClosure.NativeDictionaryDenotation.SubNode.then i j), Option.some subs.size)
'YulangClosure.NativeDictionaryDenotation.compose.eq_3' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.compose.eq_3
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.caller_action_not_idempotent
YulangClosure.NativeDictionaryDenotation.caller_action_not_idempotent : YulangClosure.NativeDictionaryDenotation.action
      YulangClosure.NativeDictionaryDenotation.orderedExample { base := Option.some 0, word := [] } =
    { base := Option.some 1, word := [] } ∧
  YulangClosure.NativeDictionaryDenotation.action YulangClosure.NativeDictionaryDenotation.orderedExample
      (YulangClosure.NativeDictionaryDenotation.action YulangClosure.NativeDictionaryDenotation.orderedExample
        { base := Option.some 0, word := [] }) =
    { base := Option.none, word := [] }
'YulangClosure.NativeDictionaryDenotation.caller_action_not_idempotent' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.caller_action_not_idempotent
YULANG_AUDIT_BEGIN _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.applyDag.match_1.eq_2
_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.applyDag.match_1.eq_2 : ∀
  (motive :
    YulangClosure.NativeDictionaryDenotation.SubArena →
      Nat → YulangClosure.NativeDictionaryDenotation.RawContext → Sort u_1)
  (before : YulangClosure.NativeDictionaryDenotation.SubArena) (node : YulangClosure.NativeDictionaryDenotation.SubNode)
  (i : Nat) (input : YulangClosure.NativeDictionaryDenotation.RawContext)
  (h_1 :
    (x : Nat) →
      (x_1 : YulangClosure.NativeDictionaryDenotation.RawContext) →
        motive YulangClosure.NativeDictionaryDenotation.SubArena.empty x x_1)
  (h_2 :
    (before : YulangClosure.NativeDictionaryDenotation.SubArena) →
      (node : YulangClosure.NativeDictionaryDenotation.SubNode) →
        (i : Nat) → (input : YulangClosure.NativeDictionaryDenotation.RawContext) → motive (before.push node) i input),
  (match before.push node, i, input with
    | YulangClosure.NativeDictionaryDenotation.SubArena.empty, x, x_1 => h_1 x x_1
    | before.push node, i, input => h_2 before node i input) =
    h_2 before node i input
'_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.applyDag.match_1.eq_2' does not depend on any axioms
YULANG_AUDIT_END _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.applyDag.match_1.eq_2
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.context.eq_1
@YulangClosure.NativeDictionaryDenotation.context.eq_1 : ∀ {Step : Type}
  (arena : YulangClosure.NativeDictionaryDenotation.WordArena Step)
  (raw : YulangClosure.NativeDictionaryDenotation.RawContext),
  YulangClosure.NativeDictionaryDenotation.context arena raw =
    Option.map (fun w => { base := raw.base, word := w }) (YulangClosure.NativeDictionaryDenotation.word arena raw.word)
'YulangClosure.NativeDictionaryDenotation.context.eq_1' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.context.eq_1
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.subAt_bound
@YulangClosure.NativeDictionaryDenotation.subAt_bound : ∀ {Step : Type}
  {words : YulangClosure.NativeDictionaryDenotation.WordArena Step}
  {subs : YulangClosure.NativeDictionaryDenotation.SubArena} {i : Nat}
  {as : List (YulangClosure.NativeDictionaryDenotation.Assignment Step)},
  YulangClosure.NativeDictionaryDenotation.subAt words subs i = Option.some as → i < subs.size
'YulangClosure.NativeDictionaryDenotation.subAt_bound' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.subAt_bound
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.substitution_push_old
@YulangClosure.NativeDictionaryDenotation.substitution_push_old : ∀ {Step : Type}
  {words : YulangClosure.NativeDictionaryDenotation.WordArena Step}
  {subs : YulangClosure.NativeDictionaryDenotation.SubArena} {i : Option Nat}
  {as : List (YulangClosure.NativeDictionaryDenotation.Assignment Step)},
  YulangClosure.NativeDictionaryDenotation.substitution words subs i = Option.some as →
    ∀ (node : YulangClosure.NativeDictionaryDenotation.SubNode),
      YulangClosure.NativeDictionaryDenotation.substitution words (subs.push node) i = Option.some as
'YulangClosure.NativeDictionaryDenotation.substitution_push_old' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.substitution_push_old
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.initializer.eq_1
YulangClosure.NativeDictionaryDenotation.initializer.eq_1 : ∀
  (defaults : Nat → Option YulangClosure.NativeDictionaryDenotation.RawContext) (cell : Nat)
  (parent : YulangClosure.NativeDictionaryDenotation.State),
  YulangClosure.NativeDictionaryDenotation.initializer defaults cell parent =
    (fun scope => if scope = cell then Option.some parent.context else defaults scope,
      if (defaults cell).isSome = Bool.true then Option.none
      else
        Option.some
          { context := { base := Option.some cell, word := Option.none }, substitution := parent.substitution })
'YulangClosure.NativeDictionaryDenotation.initializer.eq_1' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.initializer.eq_1
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.wordAt.eq_2
@YulangClosure.NativeDictionaryDenotation.wordAt.eq_2 : ∀ {Step : Type} (x : Nat)
  (old : YulangClosure.NativeDictionaryDenotation.WordArena Step) (previous : Option Nat) (item : Step),
  YulangClosure.NativeDictionaryDenotation.wordAt
      (old.push (YulangClosure.NativeDictionaryDenotation.WordNode.step previous item)) x =
    if x = old.size then
      Option.map (fun x => x ++ [item])
        ((Option.map (YulangClosure.NativeDictionaryDenotation.wordAt old) previous).getD (Option.some []))
    else YulangClosure.NativeDictionaryDenotation.wordAt old x
'YulangClosure.NativeDictionaryDenotation.wordAt.eq_2' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.wordAt.eq_2
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.SubArena.empty.sizeOf_spec
YulangClosure.NativeDictionaryDenotation.SubArena.empty.sizeOf_spec : SizeOf.sizeOf
    YulangClosure.NativeDictionaryDenotation.SubArena.empty =
  1
'YulangClosure.NativeDictionaryDenotation.SubArena.empty.sizeOf_spec' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.SubArena.empty.sizeOf_spec
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.name_action_none
@YulangClosure.NativeDictionaryDenotation.name_action_none : ∀ {Step : Type}
  (value current : List (YulangClosure.NativeDictionaryDenotation.Assignment Step))
  (caller input : YulangClosure.NativeDictionaryDenotation.Context Step) (cell : Nat),
  YulangClosure.NativeDictionaryDenotation.action
      (YulangClosure.NativeDictionaryDenotation.nameAction value current caller cell Option.none) input =
    YulangClosure.NativeDictionaryDenotation.action current
      (YulangClosure.NativeDictionaryDenotation.action value input)
'YulangClosure.NativeDictionaryDenotation.name_action_none' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.name_action_none
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.wordAt.eq_1
@YulangClosure.NativeDictionaryDenotation.wordAt.eq_1 : ∀ {Step : Type} (x : Nat),
  YulangClosure.NativeDictionaryDenotation.wordAt YulangClosure.NativeDictionaryDenotation.WordArena.empty x =
    Option.none
'YulangClosure.NativeDictionaryDenotation.wordAt.eq_1' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.wordAt.eq_1
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.SubNode.assign.sizeOf_spec
YulangClosure.NativeDictionaryDenotation.SubNode.assign.sizeOf_spec : ∀ (scope : Nat)
  (replacement : YulangClosure.NativeDictionaryDenotation.RawContext),
  SizeOf.sizeOf (YulangClosure.NativeDictionaryDenotation.SubNode.assign scope replacement) =
    1 + SizeOf.sizeOf scope + SizeOf.sizeOf replacement
'YulangClosure.NativeDictionaryDenotation.SubNode.assign.sizeOf_spec' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.SubNode.assign.sizeOf_spec
YULANG_AUDIT_BEGIN _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.wordAt.match_1.eq_1
@_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.wordAt.match_1.eq_1 : ∀
  {Step : Type} (motive : YulangClosure.NativeDictionaryDenotation.WordNode Step → Sort u_1) (previous : Option Nat)
  (item : Step)
  (h_1 :
    (previous : Option Nat) →
      (item : Step) → motive (YulangClosure.NativeDictionaryDenotation.WordNode.step previous item))
  (h_2 : (left right : Nat) → motive (YulangClosure.NativeDictionaryDenotation.WordNode.join left right)),
  (match YulangClosure.NativeDictionaryDenotation.WordNode.step previous item with
    | YulangClosure.NativeDictionaryDenotation.WordNode.step previous item => h_1 previous item
    | YulangClosure.NativeDictionaryDenotation.WordNode.join left right => h_2 left right) =
    h_1 previous item
'_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.wordAt.match_1.eq_1' does not depend on any axioms
YULANG_AUDIT_END _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.wordAt.match_1.eq_1
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.append.eq_1
@YulangClosure.NativeDictionaryDenotation.append.eq_1 : ∀ {Step : Type}
  (arena : YulangClosure.NativeDictionaryDenotation.WordArena Step)
  (raw : YulangClosure.NativeDictionaryDenotation.RawContext) (item : Step),
  YulangClosure.NativeDictionaryDenotation.append arena raw item =
    (arena.push (YulangClosure.NativeDictionaryDenotation.WordNode.step raw.word item),
      { base := raw.base, word := Option.some arena.size })
'YulangClosure.NativeDictionaryDenotation.append.eq_1' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.append.eq_1
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.cyclic_default_fails
YulangClosure.NativeDictionaryDenotation.cyclic_default_fails : ∀ (fuel : Nat),
  YulangClosure.NativeDictionaryDenotation.resolve (fun x => Option.some { base := Option.some 0, word := [] }) [] fuel
      { base := Option.some 0, word := [] } =
    Option.none
'YulangClosure.NativeDictionaryDenotation.cyclic_default_fails' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.cyclic_default_fails
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.action.eq_1
@YulangClosure.NativeDictionaryDenotation.action.eq_1 : ∀ {Step : Type}
  (as : List (YulangClosure.NativeDictionaryDenotation.Assignment Step))
  (c : YulangClosure.NativeDictionaryDenotation.Context Step),
  YulangClosure.NativeDictionaryDenotation.action as c =
    List.foldl (fun c a => YulangClosure.NativeDictionaryDenotation.assign a c) c as
'YulangClosure.NativeDictionaryDenotation.action.eq_1' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.action.eq_1
YULANG_AUDIT_BEGIN _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.subAt.match_3.eq_2
_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.subAt.match_3.eq_2 : ∀
  (motive : YulangClosure.NativeDictionaryDenotation.SubArena → Nat → Sort u_1)
  (old : YulangClosure.NativeDictionaryDenotation.SubArena) (node : YulangClosure.NativeDictionaryDenotation.SubNode)
  (i : Nat) (h_1 : (x : Nat) → motive YulangClosure.NativeDictionaryDenotation.SubArena.empty x)
  (h_2 :
    (old : YulangClosure.NativeDictionaryDenotation.SubArena) →
      (node : YulangClosure.NativeDictionaryDenotation.SubNode) → (i : Nat) → motive (old.push node) i),
  (match old.push node, i with
    | YulangClosure.NativeDictionaryDenotation.SubArena.empty, x => h_1 x
    | old.push node, i => h_2 old node i) =
    h_2 old node i
'_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.subAt.match_3.eq_2' does not depend on any axioms
YULANG_AUDIT_END _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.subAt.match_3.eq_2
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.join.eq_2
@YulangClosure.NativeDictionaryDenotation.join.eq_2 : ∀ {Step : Type}
  (arena : YulangClosure.NativeDictionaryDenotation.WordArena Step) (a : Option Nat),
  (a = Option.none → False) → YulangClosure.NativeDictionaryDenotation.join arena a Option.none = (arena, a)
'YulangClosure.NativeDictionaryDenotation.join.eq_2' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.join.eq_2
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.subAt.eq_1
@YulangClosure.NativeDictionaryDenotation.subAt.eq_1 : ∀ {Step : Type}
  (words : YulangClosure.NativeDictionaryDenotation.WordArena Step) (x : Nat),
  YulangClosure.NativeDictionaryDenotation.subAt words YulangClosure.NativeDictionaryDenotation.SubArena.empty x =
    Option.none
'YulangClosure.NativeDictionaryDenotation.subAt.eq_1' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.subAt.eq_1
YULANG_AUDIT_BEGIN _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.join.match_1.eq_2
_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.join.match_1.eq_2 : ∀
  (motive : Option Nat → Option Nat → Sort u_1) (h : Option Nat) (h_1 : (h : Option Nat) → motive Option.none h)
  (h_2 : (h : Option Nat) → motive h Option.none) (h_3 : (i j : Nat) → motive (Option.some i) (Option.some j)),
  (h = Option.none → False) →
    (match h, Option.none with
      | Option.none, h => h_1 h
      | h, Option.none => h_2 h
      | Option.some i, Option.some j => h_3 i j) =
      h_2 h
'_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.join.match_1.eq_2' does not depend on any axioms
YULANG_AUDIT_END _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.join.match_1.eq_2
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.context_transport
@YulangClosure.NativeDictionaryDenotation.context_transport : ∀ {Step : Type}
  {old new : YulangClosure.NativeDictionaryDenotation.WordArena Step},
  (∀ (h : Option Nat) (w : List Step),
      YulangClosure.NativeDictionaryDenotation.word old h = Option.some w →
        YulangClosure.NativeDictionaryDenotation.word new h = Option.some w) →
    ∀ {raw : YulangClosure.NativeDictionaryDenotation.RawContext}
      {c : YulangClosure.NativeDictionaryDenotation.Context Step},
      YulangClosure.NativeDictionaryDenotation.context old raw = Option.some c →
        YulangClosure.NativeDictionaryDenotation.context new raw = Option.some c
'YulangClosure.NativeDictionaryDenotation.context_transport' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.context_transport
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.SubArena.push.sizeOf_spec
YulangClosure.NativeDictionaryDenotation.SubArena.push.sizeOf_spec : ∀
  (old : YulangClosure.NativeDictionaryDenotation.SubArena) (node : YulangClosure.NativeDictionaryDenotation.SubNode),
  SizeOf.sizeOf (old.push node) = 1 + SizeOf.sizeOf old + SizeOf.sizeOf node
'YulangClosure.NativeDictionaryDenotation.SubArena.push.sizeOf_spec' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.SubArena.push.sizeOf_spec
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.WordArena.brecOn.eq
@YulangClosure.NativeDictionaryDenotation.WordArena.brecOn.eq : ∀ {Step : Type}
  {motive : YulangClosure.NativeDictionaryDenotation.WordArena Step → Sort u_1}
  (t : YulangClosure.NativeDictionaryDenotation.WordArena Step)
  (F_1 :
    (t : YulangClosure.NativeDictionaryDenotation.WordArena Step) →
      YulangClosure.NativeDictionaryDenotation.WordArena.below t → motive t),
  YulangClosure.NativeDictionaryDenotation.WordArena.brecOn t F_1 =
    F_1 t (YulangClosure.NativeDictionaryDenotation.WordArena.brecOn.go t F_1).2
'YulangClosure.NativeDictionaryDenotation.WordArena.brecOn.eq' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.WordArena.brecOn.eq
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.applyDag_denotes
@YulangClosure.NativeDictionaryDenotation.applyDag_denotes : ∀ {Step : Type}
  {words : YulangClosure.NativeDictionaryDenotation.WordArena Step}
  {subs : YulangClosure.NativeDictionaryDenotation.SubArena} {i : Nat}
  {as : List (YulangClosure.NativeDictionaryDenotation.Assignment Step)}
  {raw : YulangClosure.NativeDictionaryDenotation.RawContext}
  {input : YulangClosure.NativeDictionaryDenotation.Context Step},
  YulangClosure.NativeDictionaryDenotation.subAt words subs i = Option.some as →
    YulangClosure.NativeDictionaryDenotation.context words raw = Option.some input →
      ∃ result,
        YulangClosure.NativeDictionaryDenotation.applyDag words subs i raw = Option.some result ∧
          YulangClosure.NativeDictionaryDenotation.context result.fst result.snd =
              Option.some (YulangClosure.NativeDictionaryDenotation.action as input) ∧
            ∀ (handle : Option Nat) (items : List Step),
              YulangClosure.NativeDictionaryDenotation.word words handle = Option.some items →
                YulangClosure.NativeDictionaryDenotation.word result.fst handle = Option.some items
'YulangClosure.NativeDictionaryDenotation.applyDag_denotes' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.applyDag_denotes
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.join.eq_3
@YulangClosure.NativeDictionaryDenotation.join.eq_3 : ∀ {Step : Type}
  (arena : YulangClosure.NativeDictionaryDenotation.WordArena Step) (i j : Nat),
  YulangClosure.NativeDictionaryDenotation.join arena (Option.some i) (Option.some j) =
    (arena.push (YulangClosure.NativeDictionaryDenotation.WordNode.join i j), Option.some arena.size)
'YulangClosure.NativeDictionaryDenotation.join.eq_3' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.join.eq_3
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.name_keeps_context
@YulangClosure.NativeDictionaryDenotation.name_keeps_context : ∀ {Step : Type}
  {words : YulangClosure.NativeDictionaryDenotation.WordArena Step}
  {raw : YulangClosure.NativeDictionaryDenotation.RawContext}
  {input : YulangClosure.NativeDictionaryDenotation.Context Step},
  YulangClosure.NativeDictionaryDenotation.context words raw = Option.some input →
    ∀ (subs : YulangClosure.NativeDictionaryDenotation.SubArena) (value : Option Nat)
      (current : YulangClosure.NativeDictionaryDenotation.State) (cell : Nat) (instantiate : Option Step),
      YulangClosure.NativeDictionaryDenotation.context
          (YulangClosure.NativeDictionaryDenotation.name words subs value current cell instantiate).words raw =
        Option.some input
'YulangClosure.NativeDictionaryDenotation.name_keeps_context' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.name_keeps_context
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.join_keeps_old
@YulangClosure.NativeDictionaryDenotation.join_keeps_old : ∀ {Step : Type}
  {words : YulangClosure.NativeDictionaryDenotation.WordArena Step} {handle : Option Nat} {items : List Step},
  YulangClosure.NativeDictionaryDenotation.word words handle = Option.some items →
    ∀ (left right : Option Nat),
      YulangClosure.NativeDictionaryDenotation.word (YulangClosure.NativeDictionaryDenotation.join words left right).fst
          handle =
        Option.some items
'YulangClosure.NativeDictionaryDenotation.join_keeps_old' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.join_keeps_old
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.RawContext.mk.sizeOf_spec
YulangClosure.NativeDictionaryDenotation.RawContext.mk.sizeOf_spec : ∀ (base word : Option Nat),
  SizeOf.sizeOf { base := base, word := word } = 1 + SizeOf.sizeOf base + SizeOf.sizeOf word
'YulangClosure.NativeDictionaryDenotation.RawContext.mk.sizeOf_spec' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.RawContext.mk.sizeOf_spec
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.subAt.eq_2
@YulangClosure.NativeDictionaryDenotation.subAt.eq_2 : ∀ {Step : Type}
  (words : YulangClosure.NativeDictionaryDenotation.WordArena Step) (x : Nat)
  (old : YulangClosure.NativeDictionaryDenotation.SubArena) (scope : Nat)
  (raw : YulangClosure.NativeDictionaryDenotation.RawContext),
  YulangClosure.NativeDictionaryDenotation.subAt words
      (old.push (YulangClosure.NativeDictionaryDenotation.SubNode.assign scope raw)) x =
    if x = old.size then
      Option.map (fun c => [{ scope := scope, replacement := c }])
        (YulangClosure.NativeDictionaryDenotation.context words raw)
    else YulangClosure.NativeDictionaryDenotation.subAt words old x
'YulangClosure.NativeDictionaryDenotation.subAt.eq_2' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.subAt.eq_2
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.subAt.eq_def
@YulangClosure.NativeDictionaryDenotation.subAt.eq_def : ∀ {Step : Type}
  (words : YulangClosure.NativeDictionaryDenotation.WordArena Step)
  (x : YulangClosure.NativeDictionaryDenotation.SubArena) (x_1 : Nat),
  YulangClosure.NativeDictionaryDenotation.subAt words x x_1 =
    match x, x_1 with
    | YulangClosure.NativeDictionaryDenotation.SubArena.empty, x => Option.none
    | old.push node, i =>
      if i = old.size then
        match node with
        | YulangClosure.NativeDictionaryDenotation.SubNode.assign scope raw =>
          Option.map (fun c => [{ scope := scope, replacement := c }])
            (YulangClosure.NativeDictionaryDenotation.context words raw)
        | YulangClosure.NativeDictionaryDenotation.SubNode.then first second => do
          let a ← YulangClosure.NativeDictionaryDenotation.subAt words old first
          let b ← YulangClosure.NativeDictionaryDenotation.subAt words old second
          Pure.pure (a ++ b)
      else YulangClosure.NativeDictionaryDenotation.subAt words old i
'YulangClosure.NativeDictionaryDenotation.subAt.eq_def' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.subAt.eq_def
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.name_dispatch_meaning
@YulangClosure.NativeDictionaryDenotation.name_dispatch_meaning : ∀ {Step : Type}
  {words : YulangClosure.NativeDictionaryDenotation.WordArena Step}
  {subs : YulangClosure.NativeDictionaryDenotation.SubArena} {value : Option Nat}
  {current : YulangClosure.NativeDictionaryDenotation.State}
  {v c : List (YulangClosure.NativeDictionaryDenotation.Assignment Step)}
  {caller input : YulangClosure.NativeDictionaryDenotation.Context Step}
  {raw : YulangClosure.NativeDictionaryDenotation.RawContext},
  YulangClosure.NativeDictionaryDenotation.substitution words subs value = Option.some v →
    YulangClosure.NativeDictionaryDenotation.substitution words subs current.substitution = Option.some c →
      YulangClosure.NativeDictionaryDenotation.context words current.context = Option.some caller →
        YulangClosure.NativeDictionaryDenotation.context words raw = Option.some input →
          ∀ (defaults : Nat → Option (YulangClosure.NativeDictionaryDenotation.Context Step)) (fuel cell : Nat)
            (instantiate : Option Step),
            YulangClosure.NativeDictionaryDenotation.dispatchMeaning
                (YulangClosure.NativeDictionaryDenotation.name words subs value current cell instantiate).words
                (YulangClosure.NativeDictionaryDenotation.name words subs value current cell instantiate).substitutions
                defaults fuel
                { context := raw,
                  substitution :=
                    (YulangClosure.NativeDictionaryDenotation.name words subs value current cell instantiate).result } =
              YulangClosure.NativeDictionaryDenotation.resolve defaults
                (YulangClosure.NativeDictionaryDenotation.nameAction v c caller cell instantiate) fuel
                (YulangClosure.NativeDictionaryDenotation.action
                  (YulangClosure.NativeDictionaryDenotation.nameAction v c caller cell instantiate) input)
'YulangClosure.NativeDictionaryDenotation.name_dispatch_meaning' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.name_dispatch_meaning
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.join.eq_1
@YulangClosure.NativeDictionaryDenotation.join.eq_1 : ∀ {Step : Type}
  (arena : YulangClosure.NativeDictionaryDenotation.WordArena Step) (b : Option Nat),
  YulangClosure.NativeDictionaryDenotation.join arena Option.none b = (arena, b)
'YulangClosure.NativeDictionaryDenotation.join.eq_1' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.join.eq_1
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.WordNode.step.injEq
@YulangClosure.NativeDictionaryDenotation.WordNode.step.injEq : ∀ {Step : Type} (previous : Option Nat) (item : Step)
  (previous_1 : Option Nat) (item_1 : Step),
  (YulangClosure.NativeDictionaryDenotation.WordNode.step previous item =
      YulangClosure.NativeDictionaryDenotation.WordNode.step previous_1 item_1) =
    (previous = previous_1 ∧ item = item_1)
'YulangClosure.NativeDictionaryDenotation.WordNode.step.injEq' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.WordNode.step.injEq
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.context_fields
@YulangClosure.NativeDictionaryDenotation.context_fields : ∀ {Step : Type}
  {words : YulangClosure.NativeDictionaryDenotation.WordArena Step}
  {raw : YulangClosure.NativeDictionaryDenotation.RawContext}
  {c : YulangClosure.NativeDictionaryDenotation.Context Step},
  YulangClosure.NativeDictionaryDenotation.context words raw = Option.some c ↔
    raw.base = c.base ∧ YulangClosure.NativeDictionaryDenotation.word words raw.word = Option.some c.word
'YulangClosure.NativeDictionaryDenotation.context_fields' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.context_fields
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.name_applies_caller_once
YulangClosure.NativeDictionaryDenotation.name_applies_caller_once : YulangClosure.NativeDictionaryDenotation.action
    (YulangClosure.NativeDictionaryDenotation.nameAction [] YulangClosure.NativeDictionaryDenotation.orderedExample
      { base := Option.some 0, word := [] } 2 (Option.some 7))
    { base := Option.some 2, word := [] } =
  { base := Option.some 1, word := [7] }
'YulangClosure.NativeDictionaryDenotation.name_applies_caller_once' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.name_applies_caller_once
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.word_push_old
@YulangClosure.NativeDictionaryDenotation.word_push_old : ∀ {Step : Type}
  {arena : YulangClosure.NativeDictionaryDenotation.WordArena Step} {h : Option Nat} {w : List Step},
  YulangClosure.NativeDictionaryDenotation.word arena h = Option.some w →
    ∀ (node : YulangClosure.NativeDictionaryDenotation.WordNode Step),
      YulangClosure.NativeDictionaryDenotation.word (arena.push node) h = Option.some w
'YulangClosure.NativeDictionaryDenotation.word_push_old' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.word_push_old
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.SubNode.assign.inj
@YulangClosure.NativeDictionaryDenotation.SubNode.assign.inj : ∀ {scope : Nat}
  {replacement : YulangClosure.NativeDictionaryDenotation.RawContext} {scope_1 : Nat}
  {replacement_1 : YulangClosure.NativeDictionaryDenotation.RawContext},
  YulangClosure.NativeDictionaryDenotation.SubNode.assign scope replacement =
      YulangClosure.NativeDictionaryDenotation.SubNode.assign scope_1 replacement_1 →
    scope = scope_1 ∧ replacement = replacement_1
'YulangClosure.NativeDictionaryDenotation.SubNode.assign.inj' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.SubNode.assign.inj
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.assignRaw_keeps_old
@YulangClosure.NativeDictionaryDenotation.assignRaw_keeps_old : ∀ {Step : Type}
  {words : YulangClosure.NativeDictionaryDenotation.WordArena Step} {handle : Option Nat} {items : List Step},
  YulangClosure.NativeDictionaryDenotation.word words handle = Option.some items →
    ∀ (scope : Nat) (replacement input : YulangClosure.NativeDictionaryDenotation.RawContext),
      YulangClosure.NativeDictionaryDenotation.word
          (YulangClosure.NativeDictionaryDenotation.assignRaw words scope replacement input).fst handle =
        Option.some items
'YulangClosure.NativeDictionaryDenotation.assignRaw_keeps_old' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.assignRaw_keeps_old
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.instDecidableEqContext.decEq._proof_3
@YulangClosure.NativeDictionaryDenotation.instDecidableEqContext.decEq._proof_3 : ∀ {Step : Type} (a : Option Nat)
  (a_1 : List Step) (b : Option Nat) (b_1 : List Step),
  ¬a = b → { base := a, word := a_1 } = { base := b, word := b_1 } → False
'YulangClosure.NativeDictionaryDenotation.instDecidableEqContext.decEq._proof_3' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.instDecidableEqContext.decEq._proof_3
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.instDecidableEqContext.decEq._proof_2
@YulangClosure.NativeDictionaryDenotation.instDecidableEqContext.decEq._proof_2 : ∀ {Step : Type} (a : Option Nat)
  (a_1 b : List Step), ¬a_1 = b → { base := a, word := a_1 } = { base := a, word := b } → False
'YulangClosure.NativeDictionaryDenotation.instDecidableEqContext.decEq._proof_2' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.instDecidableEqContext.decEq._proof_2
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.WordNode.step.sizeOf_spec
@YulangClosure.NativeDictionaryDenotation.WordNode.step.sizeOf_spec : ∀ {Step : Type} [inst : SizeOf Step]
  (previous : Option Nat) (item : Step),
  SizeOf.sizeOf (YulangClosure.NativeDictionaryDenotation.WordNode.step previous item) =
    1 + SizeOf.sizeOf previous + SizeOf.sizeOf item
'YulangClosure.NativeDictionaryDenotation.WordNode.step.sizeOf_spec' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.WordNode.step.sizeOf_spec
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.append_denotes
@YulangClosure.NativeDictionaryDenotation.append_denotes : ∀ {Step : Type}
  {arena : YulangClosure.NativeDictionaryDenotation.WordArena Step}
  {raw : YulangClosure.NativeDictionaryDenotation.RawContext}
  {c : YulangClosure.NativeDictionaryDenotation.Context Step},
  YulangClosure.NativeDictionaryDenotation.context arena raw = Option.some c →
    ∀ (item : Step),
      YulangClosure.NativeDictionaryDenotation.context
          (YulangClosure.NativeDictionaryDenotation.append arena raw item).fst
          (YulangClosure.NativeDictionaryDenotation.append arena raw item).snd =
        Option.some { base := c.base, word := c.word ++ [item] }
'YulangClosure.NativeDictionaryDenotation.append_denotes' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.append_denotes
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.initialize_fresh
YulangClosure.NativeDictionaryDenotation.initialize_fresh : ∀
  (defaults : Nat → Option YulangClosure.NativeDictionaryDenotation.RawContext) (cell : Nat)
  (parent : YulangClosure.NativeDictionaryDenotation.State),
  defaults cell = Option.none →
    (YulangClosure.NativeDictionaryDenotation.initializer defaults cell parent).fst cell = Option.some parent.context ∧
      (YulangClosure.NativeDictionaryDenotation.initializer defaults cell parent).snd =
        Option.some
          { context := { base := Option.some cell, word := Option.none }, substitution := parent.substitution }
'YulangClosure.NativeDictionaryDenotation.initialize_fresh' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.initialize_fresh
YULANG_AUDIT_BEGIN _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.subAt.match_3.eq_1
_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.subAt.match_3.eq_1 : ∀
  (motive : YulangClosure.NativeDictionaryDenotation.SubArena → Nat → Sort u_1) (x : Nat)
  (h_1 : (x : Nat) → motive YulangClosure.NativeDictionaryDenotation.SubArena.empty x)
  (h_2 :
    (old : YulangClosure.NativeDictionaryDenotation.SubArena) →
      (node : YulangClosure.NativeDictionaryDenotation.SubNode) → (i : Nat) → motive (old.push node) i),
  (match YulangClosure.NativeDictionaryDenotation.SubArena.empty, x with
    | YulangClosure.NativeDictionaryDenotation.SubArena.empty, x => h_1 x
    | old.push node, i => h_2 old node i) =
    h_1 x
'_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.subAt.match_3.eq_1' does not depend on any axioms
YULANG_AUDIT_END _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.subAt.match_3.eq_1
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.word.eq_1
@YulangClosure.NativeDictionaryDenotation.word.eq_1 : ∀ {Step : Type}
  (arena : YulangClosure.NativeDictionaryDenotation.WordArena Step),
  YulangClosure.NativeDictionaryDenotation.word arena Option.none = Option.some []
'YulangClosure.NativeDictionaryDenotation.word.eq_1' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.word.eq_1
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.NameResult.mk.inj
@YulangClosure.NativeDictionaryDenotation.NameResult.mk.inj : ∀ {Step : Type}
  {words : YulangClosure.NativeDictionaryDenotation.WordArena Step}
  {substitutions : YulangClosure.NativeDictionaryDenotation.SubArena} {result : Option Nat}
  {words_1 : YulangClosure.NativeDictionaryDenotation.WordArena Step}
  {substitutions_1 : YulangClosure.NativeDictionaryDenotation.SubArena} {result_1 : Option Nat},
  { words := words, substitutions := substitutions, result := result } =
      { words := words_1, substitutions := substitutions_1, result := result_1 } →
    words = words_1 ∧ substitutions = substitutions_1 ∧ result = result_1
'YulangClosure.NativeDictionaryDenotation.NameResult.mk.inj' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.NameResult.mk.inj
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.dispatchMeaning.eq_1
@YulangClosure.NativeDictionaryDenotation.dispatchMeaning.eq_1 : ∀ {Step : Type}
  (words : YulangClosure.NativeDictionaryDenotation.WordArena Step)
  (subs : YulangClosure.NativeDictionaryDenotation.SubArena)
  (defaults : Nat → Option (YulangClosure.NativeDictionaryDenotation.Context Step)) (fuel : Nat)
  (state : YulangClosure.NativeDictionaryDenotation.State),
  YulangClosure.NativeDictionaryDenotation.dispatchMeaning words subs defaults fuel state = do
    let input ← YulangClosure.NativeDictionaryDenotation.context words state.context
    let sub ← YulangClosure.NativeDictionaryDenotation.substitution words subs state.substitution
    YulangClosure.NativeDictionaryDenotation.resolve defaults sub fuel
        (YulangClosure.NativeDictionaryDenotation.action sub input)
'YulangClosure.NativeDictionaryDenotation.dispatchMeaning.eq_1' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.dispatchMeaning.eq_1
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.assignRaw_denotes
@YulangClosure.NativeDictionaryDenotation.assignRaw_denotes : ∀ {Step : Type}
  {words : YulangClosure.NativeDictionaryDenotation.WordArena Step}
  {replacement input : YulangClosure.NativeDictionaryDenotation.RawContext}
  {r c : YulangClosure.NativeDictionaryDenotation.Context Step},
  YulangClosure.NativeDictionaryDenotation.context words replacement = Option.some r →
    YulangClosure.NativeDictionaryDenotation.context words input = Option.some c →
      ∀ (scope : Nat),
        YulangClosure.NativeDictionaryDenotation.context
            (YulangClosure.NativeDictionaryDenotation.assignRaw words scope replacement input).fst
            (YulangClosure.NativeDictionaryDenotation.assignRaw words scope replacement input).snd =
          Option.some (YulangClosure.NativeDictionaryDenotation.assign { scope := scope, replacement := r } c)
'YulangClosure.NativeDictionaryDenotation.assignRaw_denotes' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.assignRaw_denotes
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.State.mk.sizeOf_spec
YulangClosure.NativeDictionaryDenotation.State.mk.sizeOf_spec : ∀
  (context : YulangClosure.NativeDictionaryDenotation.RawContext) (substitution : Option Nat),
  SizeOf.sizeOf { context := context, substitution := substitution } =
    1 + SizeOf.sizeOf context + SizeOf.sizeOf substitution
'YulangClosure.NativeDictionaryDenotation.State.mk.sizeOf_spec' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.State.mk.sizeOf_spec
YULANG_AUDIT_BEGIN _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.wordAt.match_1.eq_2
@_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.wordAt.match_1.eq_2 : ∀
  {Step : Type} (motive : YulangClosure.NativeDictionaryDenotation.WordNode Step → Sort u_1) (left right : Nat)
  (h_1 :
    (previous : Option Nat) →
      (item : Step) → motive (YulangClosure.NativeDictionaryDenotation.WordNode.step previous item))
  (h_2 : (left right : Nat) → motive (YulangClosure.NativeDictionaryDenotation.WordNode.join left right)),
  (match YulangClosure.NativeDictionaryDenotation.WordNode.join left right with
    | YulangClosure.NativeDictionaryDenotation.WordNode.step previous item => h_1 previous item
    | YulangClosure.NativeDictionaryDenotation.WordNode.join left right => h_2 left right) =
    h_2 left right
'_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.wordAt.match_1.eq_2' does not depend on any axioms
YULANG_AUDIT_END _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.wordAt.match_1.eq_2
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.wordAt.eq_3
@YulangClosure.NativeDictionaryDenotation.wordAt.eq_3 : ∀ {Step : Type} (x : Nat)
  (old : YulangClosure.NativeDictionaryDenotation.WordArena Step) (left right : Nat),
  YulangClosure.NativeDictionaryDenotation.wordAt
      (old.push (YulangClosure.NativeDictionaryDenotation.WordNode.join left right)) x =
    if x = old.size then do
      let a ← YulangClosure.NativeDictionaryDenotation.wordAt old left
      let b ← YulangClosure.NativeDictionaryDenotation.wordAt old right
      Pure.pure (a ++ b)
    else YulangClosure.NativeDictionaryDenotation.wordAt old x
'YulangClosure.NativeDictionaryDenotation.wordAt.eq_3' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.wordAt.eq_3
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.NameResult.mk.sizeOf_spec
@YulangClosure.NativeDictionaryDenotation.NameResult.mk.sizeOf_spec : ∀ {Step : Type} [inst : SizeOf Step]
  (words : YulangClosure.NativeDictionaryDenotation.WordArena Step)
  (substitutions : YulangClosure.NativeDictionaryDenotation.SubArena) (result : Option Nat),
  SizeOf.sizeOf { words := words, substitutions := substitutions, result := result } =
    1 + SizeOf.sizeOf words + SizeOf.sizeOf substitutions + SizeOf.sizeOf result
'YulangClosure.NativeDictionaryDenotation.NameResult.mk.sizeOf_spec' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.NameResult.mk.sizeOf_spec
YULANG_AUDIT_BEGIN _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.word.match_1.eq_1
_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.word.match_1.eq_1 : ∀
  (motive : Option Nat → Sort u_1) (h_1 : Unit → motive Option.none) (h_2 : (i : Nat) → motive (Option.some i)),
  (match Option.none with
    | Option.none => h_1 ()
    | Option.some i => h_2 i) =
    h_1 ()
'_private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.word.match_1.eq_1' does not depend on any axioms
YULANG_AUDIT_END _private.YulangClosure.NativeDictionaryDenotation.0.YulangClosure.NativeDictionaryDenotation.word.match_1.eq_1
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.wordAt.eq_def
@YulangClosure.NativeDictionaryDenotation.wordAt.eq_def : ∀ {Step : Type}
  (x : YulangClosure.NativeDictionaryDenotation.WordArena Step) (x_1 : Nat),
  YulangClosure.NativeDictionaryDenotation.wordAt x x_1 =
    match x, x_1 with
    | YulangClosure.NativeDictionaryDenotation.WordArena.empty, x => Option.none
    | old.push node, i =>
      if i = old.size then
        match node with
        | YulangClosure.NativeDictionaryDenotation.WordNode.step previous item =>
          Option.map (fun x => x ++ [item])
            ((Option.map (YulangClosure.NativeDictionaryDenotation.wordAt old) previous).getD (Option.some []))
        | YulangClosure.NativeDictionaryDenotation.WordNode.join left right => do
          let a ← YulangClosure.NativeDictionaryDenotation.wordAt old left
          let b ← YulangClosure.NativeDictionaryDenotation.wordAt old right
          Pure.pure (a ++ b)
      else YulangClosure.NativeDictionaryDenotation.wordAt old i
'YulangClosure.NativeDictionaryDenotation.wordAt.eq_def' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.wordAt.eq_def
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.applyDag.eq_2
@YulangClosure.NativeDictionaryDenotation.applyDag.eq_2 : ∀ {Step : Type}
  (words : YulangClosure.NativeDictionaryDenotation.WordArena Step) (x : Nat)
  (x_1 : YulangClosure.NativeDictionaryDenotation.RawContext)
  (before : YulangClosure.NativeDictionaryDenotation.SubArena) (scope : Nat)
  (raw : YulangClosure.NativeDictionaryDenotation.RawContext),
  YulangClosure.NativeDictionaryDenotation.applyDag words
      (before.push (YulangClosure.NativeDictionaryDenotation.SubNode.assign scope raw)) x x_1 =
    if x = before.size then Option.some (YulangClosure.NativeDictionaryDenotation.assignRaw words scope raw x_1)
    else YulangClosure.NativeDictionaryDenotation.applyDag words before x x_1
'YulangClosure.NativeDictionaryDenotation.applyDag.eq_2' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.applyDag.eq_2
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.instDecidableEqRawContext.decEq._proof_3
YulangClosure.NativeDictionaryDenotation.instDecidableEqRawContext.decEq._proof_3 : ∀ (a a_1 b b_1 : Option Nat),
  ¬a = b → { base := a, word := a_1 } = { base := b, word := b_1 } → False
'YulangClosure.NativeDictionaryDenotation.instDecidableEqRawContext.decEq._proof_3' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.instDecidableEqRawContext.decEq._proof_3
YULANG_AUDIT_BEGIN YulangClosure.NativeDictionaryDenotation.applyDag.eq_def
@YulangClosure.NativeDictionaryDenotation.applyDag.eq_def : ∀ {Step : Type}
  (words : YulangClosure.NativeDictionaryDenotation.WordArena Step)
  (x : YulangClosure.NativeDictionaryDenotation.SubArena) (x_1 : Nat)
  (x_2 : YulangClosure.NativeDictionaryDenotation.RawContext),
  YulangClosure.NativeDictionaryDenotation.applyDag words x x_1 x_2 =
    match x, x_1, x_2 with
    | YulangClosure.NativeDictionaryDenotation.SubArena.empty, x, x_3 => Option.none
    | before.push node, i, input =>
      if i = before.size then
        match node with
        | YulangClosure.NativeDictionaryDenotation.SubNode.assign scope replacement =>
          Option.some (YulangClosure.NativeDictionaryDenotation.assignRaw words scope replacement input)
        | YulangClosure.NativeDictionaryDenotation.SubNode.then first second => do
          let middle ← YulangClosure.NativeDictionaryDenotation.applyDag words before first input
          YulangClosure.NativeDictionaryDenotation.applyDag middle.fst before second middle.snd
      else YulangClosure.NativeDictionaryDenotation.applyDag words before i input
'YulangClosure.NativeDictionaryDenotation.applyDag.eq_def' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeDictionaryDenotation.applyDag.eq_def
YULANG_AUDIT_COUNT 131
```

## 8. Exact resource/command receipts

### 01-base

```json
{
  "command": [
    "python3",
    "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
    "--project",
    "/workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project",
    "--lake",
    "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
    "--timeout",
    "115",
    "--module",
    "YulangClosure.NativeDictionaryDenotation",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.wordAt_bound",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.wordAt_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.word_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.append_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.join_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.action_append",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.subAt_bound",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.subAt_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.substitution_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.then_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.then_action",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_action_none",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_action_some"
  ],
  "cwd": "/workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project",
  "started_utc": "2026-10-26T11:03:08.153303+00:00",
  "wall_seconds": 1.2834710759998416,
  "exit": 1,
  "peak_aggregate_rss_bytes": 632287232,
  "cpu_affinity": [
    0
  ],
  "termination": null,
  "source_sha256": "c339f20df5b863fe277490096642388e831c36acbdd3b8337a8875ee91af5425",
  "log_sha256": "16e10d17180feb151c96fc6618281a7f52f0875b18df7a0ee9c4eeb0db35dd42",
  "seen_pids": [
    116738,
    116740,
    116744,
    116748,
    116751,
    116757
  ],
  "lean_num_threads": 1,
  "lean_memory_mib": 1024,
  "outer_timeout_seconds": 119,
  "helper_timeout_seconds": 115,
  "receipt_name": "01-base"
}
```

### 02-base-repair

```json
{
  "command": [
    "python3",
    "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
    "--project",
    "/workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project",
    "--lake",
    "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
    "--timeout",
    "115",
    "--module",
    "YulangClosure.NativeDictionaryDenotation",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.wordAt_bound",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.wordAt_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.word_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.append_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.join_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.action_append",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.subAt_bound",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.subAt_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.substitution_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.then_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.then_action",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_action_none",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_action_some"
  ],
  "cwd": "/workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project",
  "started_utc": "2026-10-26T11:03:43.608918+00:00",
  "wall_seconds": 2.815031726997404,
  "exit": 0,
  "peak_aggregate_rss_bytes": 910671872,
  "cpu_affinity": [
    0
  ],
  "termination": null,
  "source_sha256": "bc8c01d2f929561769f191405c0394b14961c70c562342cbbf517c5aec83f190",
  "log_sha256": "b5517cddaa112ebd8c39fa203f93190279b5801401ffa5b8ac8a30991dfd1616",
  "seen_pids": [
    116957,
    116959,
    116963,
    116967,
    116970,
    116976,
    116984,
    116988
  ],
  "lean_num_threads": 1,
  "lean_memory_mib": 1024,
  "outer_timeout_seconds": 119,
  "helper_timeout_seconds": 115,
  "receipt_name": "02-base-repair"
}
```

### 03-name

```json
{
  "command": [
    "python3",
    "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
    "--project",
    "/workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project",
    "--lake",
    "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
    "--timeout",
    "115",
    "--module",
    "YulangClosure.NativeDictionaryDenotation",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.wordAt_bound",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.wordAt_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.word_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.append_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.join_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.action_append",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.subAt_bound",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.subAt_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.substitution_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.then_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.then_action",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_action_none",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_action_some",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.context_transport",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.subAt_word_transport",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.substitution_word_push",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.compose_keeps_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_checked_denotes"
  ],
  "cwd": "/workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project",
  "started_utc": "2026-10-26T11:04:22.695777+00:00",
  "wall_seconds": 3.3378715130020282,
  "exit": 1,
  "peak_aggregate_rss_bytes": 636399616,
  "cpu_affinity": [
    0
  ],
  "termination": null,
  "source_sha256": "01270f46b719762c578662ae9a744af437b32ec0c215445307e0591cf4bf431a",
  "log_sha256": "a588c442deecc5f08a894d271b44d3cf4ab2e5580984ff9417b5b10a3378bbbd",
  "seen_pids": [
    117157,
    117159,
    117163,
    117167,
    117170,
    117176
  ],
  "lean_num_threads": 1,
  "lean_memory_mib": 1024,
  "outer_timeout_seconds": 119,
  "helper_timeout_seconds": 115,
  "receipt_name": "03-name"
}
```

### 04-name-repair

```json
{
  "command": [
    "python3",
    "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
    "--project",
    "/workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project",
    "--lake",
    "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
    "--timeout",
    "115",
    "--module",
    "YulangClosure.NativeDictionaryDenotation",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.wordAt_bound",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.wordAt_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.word_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.append_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.join_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.action_append",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.subAt_bound",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.subAt_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.substitution_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.then_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.then_action",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_action_none",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_action_some",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.context_transport",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.subAt_word_transport",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.substitution_word_push",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.compose_keeps_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_checked_denotes"
  ],
  "cwd": "/workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project",
  "started_utc": "2026-10-26T11:05:02.084551+00:00",
  "wall_seconds": 11.064584063002258,
  "exit": 0,
  "peak_aggregate_rss_bytes": 914685952,
  "cpu_affinity": [
    0
  ],
  "termination": null,
  "source_sha256": "44c1906a72c244537b2375a7a9e508df13e2cd0844b13ac0e8a956af653fe60f",
  "log_sha256": "72df2fd5335392074f37241c2525edc887ad7184d27456eb0365fc4124c5f58d",
  "seen_pids": [
    117506,
    117507,
    117512,
    117516,
    117528,
    117534,
    117578,
    117589
  ],
  "lean_num_threads": 1,
  "lean_memory_mib": 1024,
  "outer_timeout_seconds": 119,
  "helper_timeout_seconds": 115,
  "receipt_name": "04-name-repair"
}
```

### 05-dictionary

```json
{
  "command": [
    "python3",
    "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
    "--project",
    "/workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project",
    "--lake",
    "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
    "--timeout",
    "115",
    "--module",
    "YulangClosure.NativeDictionaryDenotation",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.wordAt_bound",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.wordAt_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.word_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.append_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.join_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.action_append",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.subAt_bound",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.subAt_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.substitution_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.then_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.then_action",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_action_none",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_action_some",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.context_transport",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.subAt_word_transport",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.substitution_word_push",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.compose_keeps_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_checked_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.context_fields",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.join_keeps_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.assignRaw_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.assignRaw_keeps_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.initialize_fresh",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.resolve_default",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_keeps_context",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_dispatch_meaning",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_dictionary_denotation",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.caller_action_not_idempotent",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_applies_caller_once",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.cyclic_default_fails"
  ],
  "cwd": "/workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project",
  "started_utc": "2026-10-26T11:06:56.632025+00:00",
  "wall_seconds": 2.112962740997318,
  "exit": 1,
  "peak_aggregate_rss_bytes": 645742592,
  "cpu_affinity": [
    0
  ],
  "termination": null,
  "source_sha256": "0dfa9baaae59b864eb9e9ef1aacb979b66ef132134fd3061d39471e7c5833c92",
  "log_sha256": "53038c8a3fe180e802707e4ab679e43d26a7c033b987e18ef359049196423e63",
  "seen_pids": [
    117972,
    117974,
    117978,
    117982,
    117985,
    117991
  ],
  "lean_num_threads": 1,
  "lean_memory_mib": 1024,
  "outer_timeout_seconds": 119,
  "helper_timeout_seconds": 115,
  "receipt_name": "05-dictionary"
}
```

### 06-raw-defaults

```json
{
  "command": [
    "python3",
    "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
    "--project",
    "/workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project",
    "--lake",
    "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
    "--timeout",
    "115",
    "--module",
    "YulangClosure.NativeDictionaryDenotation",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.wordAt_bound",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.wordAt_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.word_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.append_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.join_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.action_append",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.subAt_bound",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.subAt_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.substitution_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.then_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.then_action",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_action_none",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_action_some",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.context_transport",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.subAt_word_transport",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.substitution_word_push",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.compose_keeps_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_checked_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.context_fields",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.join_keeps_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.assignRaw_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.assignRaw_keeps_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.initialize_fresh",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.resolve_default",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_keeps_context",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_dispatch_meaning",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_dictionary_denotation",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.caller_action_not_idempotent",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_applies_caller_once",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.cyclic_default_fails",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.empty_defaults_valid",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.initializer_defaults_valid",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_defaults_unchanged",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_raw_dictionary_denotation"
  ],
  "cwd": "/workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project",
  "started_utc": "2026-10-26T11:08:02.956756+00:00",
  "wall_seconds": 5.93079381899588,
  "exit": 0,
  "peak_aggregate_rss_bytes": 924295168,
  "cpu_affinity": [
    0
  ],
  "termination": null,
  "source_sha256": "5b7c98e7a34550670c0ba30608db65b3dd0638f76a195ee503ad72c2ea8ed28c",
  "log_sha256": "20d3f62fd329d5528f1780a4ab6d0e3641aba58112b50036c3ffc634f611c360",
  "seen_pids": [
    118190,
    118192,
    118196,
    118200,
    118203,
    118209,
    118233,
    118237
  ],
  "lean_num_threads": 1,
  "lean_memory_mib": 1024,
  "outer_timeout_seconds": 119,
  "helper_timeout_seconds": 115,
  "receipt_name": "06-raw-defaults"
}
```

### 07-raw-dag

```json
{
  "command": [
    "python3",
    "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
    "--project",
    "/workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project",
    "--lake",
    "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
    "--timeout",
    "115",
    "--module",
    "YulangClosure.NativeDictionaryDenotation",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.wordAt_bound",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.wordAt_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.word_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.append_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.join_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.action_append",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.subAt_bound",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.subAt_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.substitution_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.then_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.then_action",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_action_none",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_action_some",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.context_transport",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.subAt_word_transport",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.substitution_word_push",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.compose_keeps_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_checked_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.context_fields",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.join_keeps_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.assignRaw_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.assignRaw_keeps_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.applyDag_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.initialize_fresh",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.resolve_default",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_keeps_context",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_dispatch_meaning",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_dictionary_denotation",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.caller_action_not_idempotent",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_applies_caller_once",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.cyclic_default_fails",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.empty_defaults_valid",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.initializer_defaults_valid",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_defaults_unchanged",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_raw_dictionary_denotation"
  ],
  "cwd": "/workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project",
  "started_utc": "2026-10-26T11:10:58.207487+00:00",
  "wall_seconds": 2.230736881996563,
  "exit": 1,
  "peak_aggregate_rss_bytes": 651001856,
  "cpu_affinity": [
    0
  ],
  "termination": null,
  "source_sha256": "49dde3388ec5052834c1e9a29f078aef56402807955c0022bcaf3ccbc52bb3be",
  "log_sha256": "9a8b8e0489be8aa137dbaca32db5f3d18f0e4eaa8880a26e00e2b251776560c7",
  "seen_pids": [
    118793,
    118795,
    118799,
    118803,
    118806,
    118812
  ],
  "lean_num_threads": 1,
  "lean_memory_mib": 1024,
  "outer_timeout_seconds": 119,
  "helper_timeout_seconds": 115,
  "receipt_name": "07-raw-dag"
}
```

### 08-raw-dag-repair

```json
{
  "command": [
    "python3",
    "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
    "--project",
    "/workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project",
    "--lake",
    "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
    "--timeout",
    "115",
    "--module",
    "YulangClosure.NativeDictionaryDenotation",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.wordAt_bound",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.wordAt_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.word_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.append_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.join_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.action_append",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.subAt_bound",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.subAt_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.substitution_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.then_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.then_action",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_action_none",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_action_some",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.context_transport",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.subAt_word_transport",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.substitution_word_push",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.compose_keeps_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_checked_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.context_fields",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.join_keeps_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.assignRaw_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.assignRaw_keeps_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.applyDag_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.initialize_fresh",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.resolve_default",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_keeps_context",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_dispatch_meaning",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_dictionary_denotation",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.caller_action_not_idempotent",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_applies_caller_once",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.cyclic_default_fails",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.empty_defaults_valid",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.initializer_defaults_valid",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_defaults_unchanged",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_raw_dictionary_denotation"
  ],
  "cwd": "/workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project",
  "started_utc": "2026-10-26T11:11:57.078285+00:00",
  "wall_seconds": 5.438976200995967,
  "exit": 0,
  "peak_aggregate_rss_bytes": 926040064,
  "cpu_affinity": [
    0
  ],
  "termination": null,
  "source_sha256": "b2205581ead7393df9dcc652c279be790c5d8366c1a20198a48e43edd46b0382",
  "log_sha256": "3141e0b22b074a3ac50dcc9df14adeef2787e8da8d108a4ef20e51839369212b",
  "seen_pids": [
    118948,
    118950,
    118954,
    118958,
    118961,
    118967,
    118980,
    118984
  ],
  "lean_num_threads": 1,
  "lean_memory_mib": 1024,
  "outer_timeout_seconds": 119,
  "helper_timeout_seconds": 115,
  "receipt_name": "08-raw-dag-repair"
}
```

### 09-originating-census

```json
{
  "command": [
    "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
    "--no-cache",
    "env",
    "lean",
    "-j1",
    "-M1024",
    "AuditNativeDictionaryDenotation.lean"
  ],
  "cwd": "/workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project",
  "started_utc": "2026-10-26T11:12:45.975865+00:00",
  "wall_seconds": 1.0544369030030794,
  "exit": 0,
  "peak_aggregate_rss_bytes": 899969024,
  "cpu_affinity": [
    0
  ],
  "termination": null,
  "source_sha256": "b2205581ead7393df9dcc652c279be790c5d8366c1a20198a48e43edd46b0382",
  "log_sha256": "bea0250703c0b47ec04f9725e0d6867d7e85348e9b8428a77bcaffc52cbedb8e",
  "seen_pids": [
    119050,
    119055
  ],
  "lean_num_threads": 1,
  "lean_memory_mib": 1024,
  "outer_timeout_seconds": 119,
  "helper_timeout_seconds": 115,
  "receipt_name": "09-originating-census"
}
```

### 10-checked-dictionary

```json
{
  "command": [
    "python3",
    "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
    "--project",
    "/workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project",
    "--lake",
    "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
    "--timeout",
    "115",
    "--module",
    "YulangClosure.NativeDictionaryDenotation",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.wordAt_bound",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.wordAt_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.word_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.append_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.join_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.action_append",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.subAt_bound",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.subAt_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.substitution_push_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.then_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.then_action",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_action_none",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_action_some",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.context_transport",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.subAt_word_transport",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.substitution_word_push",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.compose_keeps_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_checked_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.context_fields",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.join_keeps_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.assignRaw_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.assignRaw_keeps_old",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.applyDag_denotes",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.initialize_fresh",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.resolve_default",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_keeps_context",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_dispatch_meaning",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_dictionary_denotation",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.caller_action_not_idempotent",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_applies_caller_once",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.cyclic_default_fails",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.empty_defaults_valid",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.initializer_defaults_valid",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_defaults_unchanged",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_raw_dictionary_denotation",
    "--theorem",
    "YulangClosure.NativeDictionaryDenotation.name_checked_dictionary_denotation"
  ],
  "cwd": "/workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project",
  "started_utc": "2026-10-26T11:13:28.280061+00:00",
  "wall_seconds": 4.991688136004086,
  "exit": 0,
  "peak_aggregate_rss_bytes": 927268864,
  "cpu_affinity": [
    0
  ],
  "termination": null,
  "source_sha256": "d44a78f08970a09ca4c3e99a1d8dea846286a299d1a2bc91ec3b5e0eabea9070",
  "log_sha256": "ada1294cfe817292c2173072308974cddde57ceaad2421e291bdf9d958d664ff",
  "seen_pids": [
    119150,
    119152,
    119156,
    119160,
    119163,
    119169,
    119181,
    119185
  ],
  "lean_num_threads": 1,
  "lean_memory_mib": 1024,
  "outer_timeout_seconds": 119,
  "helper_timeout_seconds": 115,
  "receipt_name": "10-checked-dictionary"
}
```

### 11-final-originating-census

```json
{
  "command": [
    "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
    "--no-cache",
    "env",
    "lean",
    "-j1",
    "-M1024",
    "AuditNativeDictionaryDenotation.lean"
  ],
  "cwd": "/workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project",
  "started_utc": "2026-10-26T11:15:01.510091+00:00",
  "wall_seconds": 1.0245386460010195,
  "exit": 0,
  "peak_aggregate_rss_bytes": 901685248,
  "cpu_affinity": [
    0
  ],
  "termination": null,
  "source_sha256": "d44a78f08970a09ca4c3e99a1d8dea846286a299d1a2bc91ec3b5e0eabea9070",
  "log_sha256": "e301ada26982a93f8e6bd2ea877cf31c2a3648135522268ba03390a9ba845fb3",
  "seen_pids": [
    119294,
    119299
  ],
  "lean_num_threads": 1,
  "lean_memory_mib": 1024,
  "outer_timeout_seconds": 119,
  "helper_timeout_seconds": 115,
  "receipt_name": "11-final-originating-census"
}
```

## 9. Preserved failed-check diagnostics

### 01-base

```text
cwd: /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project
$ /workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake --version
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
[exit 0]
cwd: /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project
$ /workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake --no-cache env lean --version
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
[exit 0]
cwd: /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project
$ /workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake --no-cache build +YulangClosure.NativeDictionaryDenotation
✖ [2/2] Building YulangClosure.NativeDictionaryDenotation (969ms)
trace: .> LEAN_PATH=/workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project/.lake/build/lib/lean /workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lean -j1 -M1024 /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project/YulangClosure/NativeDictionaryDenotation.lean -o /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project/.lake/build/lib/lean/YulangClosure/NativeDictionaryDenotation.olean -i /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project/.lake/build/lib/lean/YulangClosure/NativeDictionaryDenotation.ilean -c /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project/.lake/build/ir/YulangClosure/NativeDictionaryDenotation.c --setup /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project/.lake/build/ir/YulangClosure/NativeDictionaryDenotation.setup.json --json
warning: YulangClosure/NativeDictionaryDenotation.lean:69:21: `if_neg` has been deprecated: Use `ite_eq_right` instead

Hint: Replace the deprecated name:
  i̵f̵_̵n̵e̵g̵i̲t̲e̲_̲e̲q̲_̲r̲i̲g̲h̲t̲
error: YulangClosure/NativeDictionaryDenotation.lean:91:10: Tactic `rfl` failed: The left-hand side
  context (append arena { base := base, word := none } item).fst (append arena { base := base, word := none } item).snd
is not definitionally equal to the right-hand side
  some
    { base := ((fun w => { base := { base := base, word := none }.base, word := w }) []).base,
      word := ((fun w => { base := { base := base, word := none }.base, word := w }) []).word ++ [item] }

case mk.none.refl
Step : Type
arena : WordArena Step
item : Step
base : Option Nat
⊢ context (append arena { base := base, word := none } item).fst
      (append arena { base := base, word := none } item).snd =
    some
      { base := ((fun w => { base := { base := base, word := none }.base, word := w }) []).base,
        word := ((fun w => { base := { base := base, word := none }.base, word := w }) []).word ++ [item] }
error: YulangClosure/NativeDictionaryDenotation.lean:113:26: Type mismatch: After simplification, term
  ha
 has type
  @Eq (Option (List Step)) (word arena (some i)) (some x)
but is expected to have type
  @Eq (Option (List Step)) (word (join arena (some i) none).fst (join arena (some i) none).snd) (some x)
warning: YulangClosure/NativeDictionaryDenotation.lean:177:20: `if_neg` has been deprecated: Use `ite_eq_right` instead

Hint: Replace the deprecated name:
  i̵f̵_̵n̵e̵g̵i̲t̲e̲_̲e̲q̲_̲r̲i̲g̲h̲t̲
error: YulangClosure/NativeDictionaryDenotation.lean:186:3: unexpected token 'then'; expected identifier
error: YulangClosure/NativeDictionaryDenotation.lean:195:24: unexpected token 'then'; expected ')' or term
error: YulangClosure/NativeDictionaryDenotation.lean:208:25: unexpected token 'then'; expected ')' or term
error: YulangClosure/NativeDictionaryDenotation.lean:230:86: unsolved goals
Step : Type
value current : List (Assignment Step)
caller input : Context Step
cell : Nat
item : Step
⊢ List.foldl (fun c a => assign a c) input
      (value ++ [{ scope := cell, replacement := { base := caller.base, word := caller.word ++ [item] } }] ++ current) =
    List.foldl (fun c a => assign a c)
      (assign { scope := cell, replacement := { base := caller.base, word := caller.word ++ [item] } }
        (List.foldl (fun c a => assign a c) input value))
      current
warning: YulangClosure/NativeDictionaryDenotation.lean:231:25: This simp argument is unused:
  action_append

Hint: Omit it from the simp argument list.
  [apply] simp only [nameAction, action, List.foldl_cons, List.foldl_nil]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/NativeDictionaryDenotation.lean:231:48: This simp argument is unused:
  List.foldl_cons

Hint: Omit it from the simp argument list.
  [apply] simp only [nameAction, action_append, action, List.foldl_nil]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/NativeDictionaryDenotation.lean:231:65: This simp argument is unused:
  List.foldl_nil

Hint: Omit it from the simp argument list.
  [apply] simp only [nameAction, action_append, action, List.foldl_cons]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Some required targets logged failures:
- YulangClosure.NativeDictionaryDenotation
error: build failed
[exit 1]
FAIL: command failed with exit 1
```

### 03-name

```text
cwd: /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project
$ /workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake --version
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
[exit 0]
cwd: /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project
$ /workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake --no-cache env lean --version
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
[exit 0]
cwd: /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project
$ /workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake --no-cache build +YulangClosure.NativeDictionaryDenotation
✖ [2/2] Building YulangClosure.NativeDictionaryDenotation (2.9s)
trace: .> LEAN_PATH=/workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project/.lake/build/lib/lean /workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lean -j1 -M1024 /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project/YulangClosure/NativeDictionaryDenotation.lean -o /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project/.lake/build/lib/lean/YulangClosure/NativeDictionaryDenotation.olean -i /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project/.lake/build/lib/lean/YulangClosure/NativeDictionaryDenotation.ilean -c /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project/.lake/build/ir/YulangClosure/NativeDictionaryDenotation.c --setup /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project/.lake/build/ir/YulangClosure/NativeDictionaryDenotation.setup.json --json
error: YulangClosure/NativeDictionaryDenotation.lean:265:9: unexpected token 'then'; expected '_' or identifier
error: YulangClosure/NativeDictionaryDenotation.lean:265:8: Missing alternative name: Expected `then`
error: YulangClosure/NativeDictionaryDenotation.lean:257:8: Alternative `then` has not been provided
error: YulangClosure/NativeDictionaryDenotation.lean:254:24: unsolved goals
case neg
Step : Type
old new : WordArena Step
keep : ∀ (h : Option Nat) (w : List Step), word old h = some w → word new h = some w
before : SubArena
node : SubNode
ih : ∀ {i : Nat} {as : List (Assignment Step)}, subAt old before i = some as → subAt new before i = some as
i : Nat
as : List (Assignment Step)
h : subAt old (before.push node) i = some as
eq : ¬i = before.size
⊢ subAt new (before.push node) i = some as
error: YulangClosure/NativeDictionaryDenotation.lean:362:61: Invalid `⟨...⟩` notation: The expected type of this term could not be determined
error: YulangClosure/NativeDictionaryDenotation.lean:362:8: 'change' tactic failed, pattern
  Option.map (fun x => [?m.145]) (context newWords replacement) = ?m.150
is not definitionally equal to target
  substitution newWords assigned (some subs.size) =
    some [{ scope := cell, replacement := { base := caller.base, word := caller.word ++ [item] } }]
Some required targets logged failures:
- YulangClosure.NativeDictionaryDenotation
error: build failed
[exit 1]
FAIL: command failed with exit 1
```

### 05-dictionary

```text
cwd: /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project
$ /workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake --version
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
[exit 0]
cwd: /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project
$ /workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake --no-cache env lean --version
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
[exit 0]
cwd: /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project
$ /workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake --no-cache build +YulangClosure.NativeDictionaryDenotation
✖ [2/2] Building YulangClosure.NativeDictionaryDenotation (1.8s)
trace: .> LEAN_PATH=/workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project/.lake/build/lib/lean /workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lean -j1 -M1024 /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project/YulangClosure/NativeDictionaryDenotation.lean -o /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project/.lake/build/lib/lean/YulangClosure/NativeDictionaryDenotation.olean -i /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project/.lake/build/lib/lean/YulangClosure/NativeDictionaryDenotation.ilean -c /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project/.lake/build/ir/YulangClosure/NativeDictionaryDenotation.c --setup /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project/.lake/build/ir/YulangClosure/NativeDictionaryDenotation.setup.json --json
error: YulangClosure/NativeDictionaryDenotation.lean:442:11: Type mismatch
  this
has type
  word words handle = some items
but is expected to have type
  word (assignRaw words scope replacement input).fst handle = some items
error: YulangClosure/NativeDictionaryDenotation.lean:446:3: unexpected token 'initialize'; expected identifier
error: YulangClosure/NativeDictionaryDenotation.lean:454:5: unexpected token 'initialize'; expected ')', '_', identifier or term
error: YulangClosure/NativeDictionaryDenotation.lean:454:16: Unknown identifier `defaults`
error: YulangClosure/NativeDictionaryDenotation.lean:454:36: unexpected token ')'; expected command
error: YulangClosure/NativeDictionaryDenotation.lean:455:16: Unknown identifier `defaults`
error: YulangClosure/NativeDictionaryDenotation.lean:455:36: unexpected token ')'; expected command
error: YulangClosure/NativeDictionaryDenotation.lean:457:18: unexpected token ','; expected '{', identifier or term
warning: YulangClosure/NativeDictionaryDenotation.lean:487:13: Possibly looping simp theorem: `resolve.eq_1`

Note: Possibly caused by: `resolve`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
error: YulangClosure/NativeDictionaryDenotation.lean:487:2: Tactic `simp` failed with a nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
error: YulangClosure/NativeDictionaryDenotation.lean:555:17: Tactic `simp` failed with a nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
Some required targets logged failures:
- YulangClosure.NativeDictionaryDenotation
error: build failed
[exit 1]
FAIL: command failed with exit 1
```

### 07-raw-dag

```text
cwd: /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project
$ /workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake --version
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
[exit 0]
cwd: /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project
$ /workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake --no-cache env lean --version
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
[exit 0]
cwd: /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project
$ /workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake --no-cache build +YulangClosure.NativeDictionaryDenotation
✖ [2/2] Building YulangClosure.NativeDictionaryDenotation (1.9s)
trace: .> LEAN_PATH=/workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project/.lake/build/lib/lean /workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lean -j1 -M1024 /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project/YulangClosure/NativeDictionaryDenotation.lean -o /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project/.lake/build/lib/lean/YulangClosure/NativeDictionaryDenotation.olean -i /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project/.lake/build/lib/lean/YulangClosure/NativeDictionaryDenotation.ilean -c /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project/.lake/build/ir/YulangClosure/NativeDictionaryDenotation.c --setup /workspace/scratch/f98087c7ac1a/dictionary-denotation-r4/project/.lake/build/ir/YulangClosure/NativeDictionaryDenotation.setup.json --json
error: YulangClosure/NativeDictionaryDenotation.lean:500:20: unsolved goals
case pos.then.some.some.refl.refine_1
Step : Type
before : SubArena
ih :
  ∀ {words : WordArena Step} {i : Nat} {as : List (Assignment Step)} {raw : RawContext} {input : Context Step},
    subAt words before i = some as →
      context words raw = some input →
        ∃ result,
          applyDag words before i raw = some result ∧
            context result.fst result.snd = some (action as input) ∧
              ∀ (handle : Option Nat) (items : List Step),
                word words handle = some items → word result.fst handle = some items
words : WordArena Step
raw : RawContext
input : Context Step
hi : context words raw = some input
first second : Nat
a : List (Assignment Step)
ha : subAt words before first = some a
b : List (Assignment Step)
hb : subAt words before second = some b
middle : WordArena Step × RawContext
hfirst : applyDag words before first raw = some middle
hm : context middle.fst middle.snd = some (action a input)
keepFirst :
  ∀ (handle : Option Nat) (items : List Step), word words handle = some items → word middle.fst handle = some items
hb' : subAt middle.fst before second = some b
result : WordArena Step × RawContext
hsecond : applyDag middle.fst before second middle.snd = some result
hout : context result.fst result.snd = some (action b (action a input))
keepSecond :
  ∀ (handle : Option Nat) (items : List Step), word middle.fst handle = some items → word result.fst handle = some items
⊢ (do
      let middle ← some middle
      applyDag middle.fst before second middle.snd) =
    some result
warning: YulangClosure/NativeDictionaryDenotation.lean:494:39: This simp argument is unused:
  Option.bind_some

Hint: Omit it from the simp argument list.
  [apply] simp only [ha, hb, pure] at hs

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/NativeDictionaryDenotation.lean:500:61: This simp argument is unused:
  Option.bind_some

Hint: Omit it from the simp argument list.
  [apply] simp only [applyDag, ite_true, hfirst, hsecond]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/NativeDictionaryDenotation.lean:500:79: This simp argument is unused:
  hsecond

Hint: Omit it from the simp argument list.
  [apply] simp only [applyDag, ite_true, hfirst, Option.bind_some]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Some required targets logged failures:
- YulangClosure.NativeDictionaryDenotation
error: build failed
[exit 1]
FAIL: command failed with exit 1
```

## 10. Stop and next owner

Producer writes stop with the external `STOPPED` receipt and frozen output hashes. The primary owns fresh independent review, integration and any subsequent continuation. Review should check the exact Name order/default guard, single resulting arena in raw application, full-payload preservation, the distinction between default-chain fuel and the native combined counter, and the precise typed-dictionary residual in §1. The original source gate remains open; no smaller language or context domain is selected.
