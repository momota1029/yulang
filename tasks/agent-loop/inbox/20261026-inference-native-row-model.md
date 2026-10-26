# Canonical finite structural row model: construction handoff

Date: 2026-10-26. Packet: `20261026-inference-native-row-model`.
Producer: generic leaf `/root/native_model_construction`; no children.
Requested role instructions: `.codex/agents/lean-prover.toml`; no effective
custom-role/model/effort identity was independently observed (UNKNOWN).
Status: **kernel-checked construction; frozen, writes stopped; independent
review and integration remain primary-owned**.

## Original parent and exact leases

The unchanged parent is `SourceProblem.InferenceSoundness` in
`YulangClosure/Contracts.lean` and `docs/yulang-whole-proof-closure-ja.md`:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

Its full original source domain, original scopes, joint witness, complete Call,
contextual effects, publication, extrusion, intrusion and natural inference are
unchanged. This packet closes a model-existence component; **the original
whole-source parent remains OPEN**. It does not promote production,
principality, ordinary progress or termination.

Assigned branch/baseline: `yulang3`,
`bf81a1bd444b3bcbecca6b754ea6fb603262f368`. No Git command or mutation was used.
The exact copied Lean dependency cone was pinned by hashes and rechecked
against the repository before freeze; see the complete table below.

Exact repository writes, all new:

- `notes/theory/lean/YulangClosure/NativeRowModel.lean`.
- `notes/theory/2026-10-26-native-row-model-construction.md`.
- `tasks/agent-loop/inbox/20261026-inference-native-row-model.md` (this handoff).

All other writes are under
`/workspace/scratch/f98087c7ac1a/inference-native-row-model/`, including an
isolated project and its own build cache. Existing repository files, native
sources, root imports, project configuration, lockfile, dependency sources,
shared status, audit/index files, questions and Git state were not modified.
No Cargo invocation or native probe was run by this leaf. The inventory and
saturation leaves have distinct source/evidence ownership.

Read root AGENTS/pre-sprint, design-authority, compiler-engineering
proof-obligation economy, goal-driven sprints, the original top-level inference
principles and birth-level correction, `yulang-lean-proofs` plus its source and
execution guides, the lean-prover role, the original source-preservation
claim, the continuation record and actual original Store/history/decision
modules. Native extrusion/intrusion/scheme/Term/bound owners and the pinned
reference paper §§5.1–5.3/Figs.10–12 were inspected. Consulted-source hashes are
retained in `consulted-sources.json`; frozen proof imports are listed below.

## Before and after

Previously the accepted completed/growing publication theorem needed a supplied
terminal graph/reference interpretation and actual terminal decision success.
Now `System.graph` and `System.names` are executable functions of finite source
syntax, and `canonical_decided` derives that decision from a finite syntactic
saturation invariant. The new theorem neither assumes a satisfying model nor
moves `RegularSub` into the invariant.

The finite input is `System`:

```lean
rows : Kind → Nat
heads : (k : Kind) → List (Regular.Node k)
clauses : List Regular.Comparison
```

Rows occupy source indices below `rows k`; head `h` has source index
`rows k + h`. All structural ports use these source references. `Saturated`
requires bounded clauses, lawful head metadata/children, lower-root transport
along row edges, direct lower-root/upper-head replay, and the original exact
structural `NodeRel` test with clause membership for child comparisons. Its
full field types appear in the source and the full-origin audit. None mentions
a graph, valuation, semantic subtyping, certificate or successful checker.

The deterministic output graph contains the exact renamed structural heads,
finite union suffixes for row lower-root lists and finite intersection suffixes
for upper-root lists. A row's one meaning is its lower join. The upper meet is
separate, and `canonical_interval` proves the ordering between them. Alias-only
components with no structural lower root map to bottom. Function cycles may
return through the same rows, but all lattice paths terminate in structural
heads or bottom/top. Both negative Function ports and both positive ports use
the identical row map.

The core proof `postfixed` has four syntactic endpoint cases. Head→row uses
finite union injection. Row→row uses lower-root inclusion and finite union
elimination. Row→head uses explicit lower-head/upper-head replay and structural
expansion. Head→head uses the existing constructor comparison after the one
reference renaming. Recursive hypotheses occur only below structural
expansion. Coinduction yields every all-depth comparison; graph validity and
the actual guard Boolean are proved separately. Existing exact finite lattice
decision then supplies computed acceptance.

## Main checked declarations and original application

All names below have prefix `YulangClosure.SimpleSub.NativeRowModel.`.
Every complete type, including implicit arguments, is preserved in the audit.

| Declaration | Exact substantive conclusion |
| --- | --- |
| `canonical_bounds` | `Saturated s → ∀ p ∈ s.clauses, Lattice.RegularSub s.graph (Regular.renamePair s.names p)`. |
| `canonical_valid` | `Saturated s → s.graph.Valid`. |
| `canonical_guard_checked` | `∀ s, Lattice.checkGuarded s.graph = true`; no saturation premise is needed for finite lattice suffixes. |
| `canonical_guarded` | `∀ s, s.graph.Guarded`. |
| `canonical_decided` | `Saturated s → LatticeDecision.decideDemands s.graph (s.clauses.map (Regular.renamePair s.names)) = true`. |
| `canonical_interval` | For each in-range row, its one lower-join meaning is below its separately allocated upper meet. |
| `canonical_original_history` | Applies the computed decision to the existing graph-indexed `ConstraintHistory` and derives the original initial obligations. |
| `canonical_completed_publication` | Directly applies existing `completed_decided_growing_publication_with_clients`, with the computed terminal graph/table and no terminal-success premise. |
| `canonical_decoded_store` | Uses the original exact decoder equation and derives original `StoreSatisfied` in the computed graph/reference map. |
| `empty_lower_bottom` | Any in-range row with an empty structural lower-root list has an actual structural-bottom lookup. |
| `recursive_store_constructed` | A concrete original Store with one shared recursive Function and both effect ports has computed graph validity, guarding and satisfaction. |
| `recursive_decision_constructed` | The concrete recursive Store's mapped finite demands are accepted using the construction theorem. |
| `alias_cycle_constructed` | A two-row alias cycle with no structural lower roots maps both rows to bottom and is accepted. |
| `lower_join_upper_meet_need_not_equal` | An unconstrained row has lower bottom and upper top, and the actual reverse decision is false. This refutes the proposed identification, not original-source soundness. |

The publication application keeps every existing lawful inventory,
boundedness/image/stopping/use/coverage premise and the actual locally indexed
`GrowingHistory`. The history must genuinely finish in the computed graph with
its computed names. No prefix compatibility or native history is inferred from
an arbitrary final reconstruction. This is the first remaining syntactic
alignment obligation at that application, not an unmentioned model premise.

The concrete recursive Store uses actual `Term.function`, `Term.var` and
`Term.atom`, not a new source predicate. Its decoder equation is `rfl`.
The original complete source/Call theorem is not identified with this example.

## Exact source/native scope and first missing owners

Represented: both kinds; shared row references; both bound directions in a
normalized clause table; all four Function ports with variance `(-,-,+,+)`;
atoms/bottom/top; finite record metadata including optional bits; whole tuple
and variant payload lists; real finite union/intersection nodes; guarded
structural recursion; alias-only cycles normalized to bottom.

Not established here: a native extractor for every endpoint; arbitrary native
width/presence/cast/method semantics; contextual effect operands and authentic
scope/occurrence guards; ordinary versus unifying coalescing correspondence;
equivalence for all original unguarded recursive syntax; all-history inventory,
level/extrusion/fresh-use/merge transport; source publication metadata; full
original Call and one source-scoped witness. These cases remain in the parent.

The inventory lane's exact all-eight-lane adapter preserves raw owner/lane/slot,
current representative and normalized endpoint pairs separately. Lower slots
mean item≤owner; upper slots mean owner≤item. A canonical-lower-vector-only
interpretation is insufficient because level-directed row/row insertion can
store the same flow only on another row's upper side. This packet never uses
raw row IDs as graph nodes.

The saturation lane's completed-block temporal proof is useful source evidence
for restricted local replay. Its producer explicitly reports that global
`rowRow`, `rowHead`, `headHead`, extrusion/merge/fresh-use closure and original
comparison-table correspondence remain OPEN. The model theorem does not assume
that a native successful return supplies them.

There is a separate original semantic seam, not a reason to rename this
fragment “all Yulang”: exact `recordPairs` is not the original boundary plan
relation. The original manuscript's `{foo?:string} → {} → {foo?:int}` example
has two successful adaptations but a failed direct comparison. Variable flow
must issue its direct producer/consumer query at the actual boundary identity;
an intermediate semantic record cannot bypass it. The paper gives a concrete
continuation using unchanged-view routes, producer anchors, consumer boundary
IDs, typed record/cast/method/Call plans, separate adaptation output ports,
absence/non-resurrection and authentic effect context. No new semantics or
opaque `LocalLaws` assumption is adopted.

## Actual execution and retained failures

Pinned executable:
`/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`.
Observed Lake: `Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)`.
Observed Lean:
`Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)`.

Assigned limits: 1,800 seconds, at most 18 focused Lean calls, 120 seconds per
call, one thread and 1 GiB per Lean process, isolated cache. Used **nine focused
checker calls**, plus the two read-only version commands. Every run used
`LEAN_NUM_THREADS=1`; the project and direct audits pass `-j1 -M1024`. The
runner kills the entire process group on a 120-second timeout. No run timed out.
No full/default integration build was claimed; the primary owns integration.

All check logs remain under
`/workspace/scratch/f98087c7ac1a/inference-native-row-model/`:

| Log | Result and repair |
| --- | --- |
| `check01.log` | Exit 1: sandboxed Lake could not detect its installed configuration. The authorized exact executable was retried with `require_escalated`; no installation or config edit. |
| `check02.log` | Exit 1: explicit `System` parameters were missing in several field-notation theorem binders; one arithmetic simplification also needed a concrete inequality. |
| `check03.log` | Exit 1: a derived Slot `BEq` differed definitionally from the generic `DecidableEq`-derived instance used by the index lemma. Removed only the redundant new derived `BEq`. |
| `check04.log` | Exit 1: constructor-projection composition needed `Function.comp_def`; a shadowed membership name in graph validity referred to the wrong hypothesis. |
| `check05.log` | Exit 0: generic construction, actual guard/decision and direct original publication application accepted; 14 focused dependency jobs. |
| `check06.log` | Exit 1: a two-element example's membership simplification left `p ∈ []`; added the exact nil simplification. |
| `check07.log` | Exit 0: final frozen 600-line source and concrete examples accepted without warnings; 14 focused dependency jobs. |
| `check08-audit.log` | Exit 0: every originating theorem, including generated/private declarations, complete types and axioms; all 18 required roots present. |
| `check09-all-origin.log` | Exit 0: every originating declaration, including definitions/constructors/recursors and generated/private names, complete types and axioms. |

The failures are preserved, not overwritten by the success log. The full
printed outputs are in those files; JSON extracts retain the same exact
printed type-and-axiom blocks. `source-scan.log` records `rg` exit 1 with no
matches for holes, project axioms, `native_decide`, `ofReduceBool`, or the kernel
bypass in the entire changed dependency cone. This source scan supplements,
and does not replace, the indirect axiom audit.

## Complete origin audit

The final audit selects constants by their actual originating module index,
not namespace spelling or a manually selected public theorem list. It rejects
project axiom declarations, duplicate inventory entries and absent required
roots, prints `#check @name` and `#print axioms name` for each entry, and rejects
all dependencies except the allowed standard axioms. It includes lazily
generated equations with older namespaces and actual private constants.

There are **209 distinct declarations**, with matching unique begin/end
records: 137 theorem constants, 61 definitions, five constructors, three
inductive types and three recursors. Seventeen names are private. The 137
theorem-name set exactly matches the separate theorem-only audit; the file has
51 authored theorem declarations, so public-only counting would be incomplete.

| Actual axiom set | Theorems | All declarations |
| --- | ---: | ---: |
| empty | 41 | 97 |
| `propext` | 35 | 51 |
| `propext, Quot.sound` | 55 | 55 |
| `propext, Classical.choice, Quot.sound` | 6 | 6 |

No project axiom, `sorryAx`, native-evaluation assumption or bypass occurs.
`Classical.choice` occurs only in `recursive_member`, `recursive_saturated`,
their two generated proof helpers, and the two recursive example result roots.
Every generic canonical construction/application root uses only `propext`
and `Quot.sound`. The executable graph/reference construction itself has no
choice-based search or noncomputable definition.

Audit code: `project/AuditNativeRowModel.lean` and
`project/AuditNativeRowModelAll.lean`. Full theorem audit:
`check08-audit.log` / `audit-records.json`. Full all-origin audit:
`check09-all-origin.log` / `all-origin-records.json`. Complete artifact digests:
`evidence-hashes.json`. No checker rerun is required merely to inspect these
complete outputs; independent proof review remains necessary.

## Frozen source and dependency hashes

Frozen new Lean source SHA256: `16835744153d05150992175ddb866ccc202e0f31781ed1a5a26c3e55c54a26bb`.
Frozen mathematical/source-correspondence paper SHA256: `7921ede9a0579696de3db4ce1625e55d493ccd0b3d237196876039d763173cd0`.
The isolated and repository Lean source are byte-identical. No Lean source
was edited after `check07`, and both audits import that frozen artifact.

The following imports were copied into the isolated project and verified
byte-identical to their repository sources before freezing:

| Source under `notes/theory/lean/` | SHA256 |
| --- | --- |
| `YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `YulangClosure/SimpleSubConstraintSoundness.lean` | `33709d3978e8071708c10bba23d85b1b025c11dfd988220501acb7c6e3220293` |
| `YulangClosure/SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `YulangClosure/SimpleSubGeneralizationSoundness.lean` | `3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246` |
| `YulangClosure/SimpleSubLatticeCertificates.lean` | `55533eee35ed7058abd125ac0e01d8f29b8c0534800018d254c1bd9f9c0bb79b` |
| `YulangClosure/SimpleSubLatticeDecision.lean` | `a9c184512bf6e23d15cc8a3a2ed230652fb168f707155e779be18c562d8e57c9` |
| `YulangClosure/SimpleSubLatticeGrowingInference.lean` | `1270e3407ddeef881020610b094709ebba07b62a97e54712bcc4b139ef8e78d0` |
| `YulangClosure/SimpleSubLatticeInference.lean` | `c534c060dfde84f2817fbaa53222f430b59d9b6377cfacedabeca7b9b4b8ffa3` |
| `YulangClosure/SimpleSubRegularConstraintSoundness.lean` | `1d2266867115fc27afe39dbb80a3ca0e8f75247a2e16b739145137e83999de33` |
| `YulangClosure/SimpleSubRegularPublication.lean` | `18fc6f138204e1529dcd0bb9c01a20de7444a26e4dadc87677460ccd8ac9fc99` |
| `YulangClosure/SimpleSubRegularSolutions.lean` | `755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29` |
| `YulangClosure/SimpleSubScopedPublication.lean` | `d64e9bffca5d513985237a9ff78dcf3d9e43baae1594edbc93dff4b5410d428f` |

Key execution artifacts (paths relative to the owned scratch directory):

| Artifact | SHA256 |
| --- | --- |
| `check01.log` | `236786620621f84d25485adb540c569870d11538778ae65170964d8a81444e6c` |
| `check02.log` | `5a57b6417d54dac3be252a63422254de41ed91904ebdc75a96253cb3e88d80d4` |
| `check03.log` | `0b7c54bc1f081f2338f316b1483bd3d1793c13cd60702bb11ad414909d7faf4e` |
| `check04.log` | `a72802ef01ebe254b3da61a8fa6c81a52a109ccb784a481be2ee20a7497688fb` |
| `check05.log` | `cd9177a4d2e7f2245c7964966814a2389596b81dbdfa7e262c7711a9ca915e6e` |
| `check06.log` | `8800e92addfbb129887aa9d707dc3b2758d3289ab18847fcb9a3dd5c2d3cf287` |
| `check07.log` | `4830768147f516e0556696c849478d0628a6088dc22711c16ecb5e157cd227c1` |
| `check08-audit.log` | `8420357b184801c3311d14fb056c11451b7376eb7c45513f77b549eb952c4a84` |
| `check09-all-origin.log` | `96c008de494caa3f9b129017ddfe5acad160fa748e6a90c3ca9ff669042da1c0` |
| `audit-records.json` | `069b05f9e7de2772acd438aa69af35702a11569621adbf7e2ce45bcd693bdf15` |
| `all-origin-records.json` | `c7173620104c8a2ac7280485b2e55fbe58b74b04d7db25fb254be6f0c80852a8` |
| `project/AuditNativeRowModelAll.lean` | `8d2389c685203dc459fc0fe00ab067edf3b2bf194884f8eb121eb7fb68f26969` |
| `frozen-lean-manifest.json` | `f8c89026b5787a7dfa20c343cb9a2b5338d04def12964baa4f90e778084b5a1a` |
| `consulted-sources.json` | `7e5104e8aa643c5b37c1e17422860e666ac64819896f1b9473bcae677c577e30` |
| `source-scan.log` | `228e1342ec1f92b1a721a9a2c39fd658133ed52ea3df8a27e5d5ee366e998426` |

## Freeze and remaining ownership

**All producer writes stopped after this handoff was written.** No checker or
producer subprocess is running. The source, paper and receipt are ready for a
fresh nonauthor review. This receipt does not certify itself or promote the
original parent.

Primary owns review, the preserved original parent status, exact integration
imports/audit, any authorized native implementation changes, small coherent
commits and publication. Native inventory/history and syntactic saturation
owners must supply the explicit source conditions above. Original optional
boundary/effect/Call owners retain their original semantic obligations.
