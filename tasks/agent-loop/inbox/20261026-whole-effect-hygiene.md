# Original Effect hygiene constructor/consumer proof handoff

Assignment-ID: WHOLE-EFFECT-HYGIENE-20261026. Handoff revision: 1.
Producer: `/root/effect_hygiene`, bounded `lean_prover` leaf; no descendants.
Primary packet: the current explicit whole soundness / Effect hygiene /
principality / inference termination assignment, baseline
`a9c746f31cc0eabeba9ebf5b673b6f121ed0ca82`, branch `yulang3`.
No separate on-disk contract was supplied by the primary. Requested role:
bounded generic worker following `.codex/agents/lean-prover.toml`; no model
override requested; actual runtime model/effort metadata is not independently
reported here.

Outcome: **kernel-accepted constructor/consumer subtheorems; independent review
pending; whole original Effect hygiene OPEN**. This is neither a replacement
effect semantics nor a claim that the original independent guards are proved.

## 1. Original obligation and source map

The parent is the original all-source, all-finite-prefix value/effect/hygiene
claim of `docs/yulang-whole-proof-closure-ja.md` §§1, 3–4. It includes the
original shared tuple, actual operation instance, receiver/receipt/route and
protection scope; capture, generalization and use must preserve their
dependencies. Independent continuations and repeated resume remain quantified.
No source form, optional record, selection, effect port or source obligation
has been removed from that parent.

The precise applicable sources are:

| Source | Relevant content |
| --- | --- |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` §1.1 | Reuse established hygiene results and work on missing constructor/consumer correspondence. |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–4 | Composed polarity; concrete permission is distinct from inflow; symbolic dependencies remain; typed transport/lifetime results retain their exact source premises. |
| `notes/design/2026-10-08-source-generalize-definition.md` and selected `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` §§3–6 | Original source scopes, fixed established resources, single actual initializer event, publication, whole instance, and source/client interpretation. Reading another certificate of the initializer is not executing the initializer again. |
| `docs/yulang-source-type-safety-ja.tex`, opening correction and `sec:owners` | Saved boundary receivers stay fixed; resumed control uses current lifetime information; a later read or raw resume does not revive an expired original receiver. This manuscript is a research integration/correction source, not blanket semantic approval. |
| `notes/design/2026-10-24-cooccurrence-release-clarification.md` | Static equal-incidence grouping must preserve distinct dynamic evidence; no new all-input/selected-input semantic vote is needed. |
| `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` | Existing concrete publicationCandidate, publish, atPublication, executionValue, extend and original source/client judgments. |
| `SourceFunctionMembership.lean` / `SourceIdentityWorld.lean` | Existing complete receipt record, current-world owned return and Name read. The represented native projection explicitly excludes full dictionary/world/Call semantics. |
| `PaperTypeSubstitution.lean` | Existing complete OperationInstance static substitution; this module does not represent original effect/protection semantics. |

The current `OriginalSourceInterpretation.Inputs` still takes independent
`functionGuards`, `observationGuards`, `checkedObservation`, `actualTypedPath`,
`receiptPrecondition`, and related original relations. Its greatest fixed point
and positive operator do not construct those interpretations. The paper
execution type representation cannot replace the missing effect clauses.

## 2. Delivered file and exact theorem boundaries

File: `notes/theory/lean/YulangClosure/OriginalEffectHygiene.lean`.
SHA-256: `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f`.
It imports existing modules only and introduces no new semantic data type,
project axiom, replacement typing relation, or compiler behavior.

All names below have prefix `YulangClosure.OriginalEffectHygiene.`.
The source file contains the complete checked types; the final audit log prints
each type including all explicit/implicit quantifiers.

| Theorem | Exact input boundary and proved conclusion |
| --- | --- |
| `publication_candidate_provenance` | From successful existing publicationCandidate: record identity, complete captures, exact filtered fixed-frame prefix, every fixed frame, and the original initializer entry path/names/frames are recovered. It distinguishes completed captures from pre-initializer replay entry. |
| `publication_lookup_provenance` | From successful existing atPublication: original name identity and stored record, identity check, fixed-history check, and equality with the existing restore operation. |
| `execution_lookup_provenance` | From successful executionValue: a frame in the actual replay history with exactly the same Binder, entry path and entire ScopedValue. |
| `source_publication_constructs_replay` | From the existing publicationValid condition for one `(name, site)` binding, construct successful publish and atPublication results, with captures, saved entry, replay, anchors and publication map. The replay fixedness check is derived from publicationCandidate, not assumed separately. |
| `replay_rejects_foreign_path` | If all saved frames at the requested Binder have a different entry path, executionValue returns none. No static-type comparison is used as event identity. |
| `description_extension_keeps_replay` | For every non-event Binder and arbitrary candidate/target, the existing extension leaves executionValue unchanged. |
| `future_scope_has_no_replay_value` | Invocation, rigidOperation and response extensions all make executionValue return none; future events cannot be consumed from an old initializer replay. |
| `published_replay_provenance` | Compose actual atPublication and executionValue successes: recover the same original record/frame, unchanged root/anchors/publications, fixedness and full payload; an event extension continues exactly the saved frame's exit path. |
| `published_execution_judgment` | Given an original executionE judgment after actual publication restoration, the open-history constructor is impossible; recover the actual stored value, its independent admission and body judgment, and the original fixed-frame provenance. |
| `generated_new_use_keeps_original_publication` | From Satisfies of the actual BuildJoint newUse formula, reconstruct the original source judgment and client judgment and recover the registered publication, entry names/path and fixed replay, unchanged root/maps, and alias identity. No source derivation is supplied as a premise. |
| `Native.owned_return_expires` | Successful existing Control.leave alone implies the returned invocation owner is inactive. No ControlValid or supplied lifetime theorem is assumed. |
| `Native.name_preserves_historical_evidence` | Successful actual observeName preserves control, complete view storage and every recorded old receipt; any previously inactive owner stays inactive. K, V, D, ViewData, Rest and Site are arbitrary types; only K/V require DecidableEq. |
| `Native.return_then_name_cannot_revive` | Compose actual returnOwned and actual observeName successes. The returned owner remains inactive while every original complete receipt remains recorded. |
| `operation_substitution_keeps_declaration` | Any existing Paper OperationInstance substitution keeps the original operation identity. |
| `substitution_cannot_identify_distinct_operations` | Two distinct declaration identities remain distinct under independently arbitrary type substitutions. This asserts no injectivity for substituted type arguments. |

The original source rules are not changed. The strongest new-use result
quantifies arbitrary raw `Definition.source` and arbitrary client suffix under
the existing Kernel. Thus it includes every source constructor represented by
the original generator without claiming that the independent Kernel.atom
clauses have all been realized. The singleton publication construction is
expressly singleton; it is not a recursive-group publication theorem.

## 3. Application to the original parent, and the first remaining premises

For an original source publication, use
`publication_candidate_provenance` and
`source_publication_constructs_replay` to supply the saved-entry/fixed-history
facts. At a generated newUse, the new-use theorem constructs the same registered
publication restoration and original source derivation. At any immediately
represented fixed execution consumer, `published_execution_judgment` and
`published_replay_provenance` recover the same stored event, instead of assuming
that replay preserves it. Description extension and foreign-path rejection
show the two relevant ways a replay identity could otherwise be changed are
excluded by the actual existing functions.

For the native post-Force owned-return/Name seam, the original typed-boundary
lifetime package can use the now-proved inactive-old-owner fact together with
complete receipt retention. Neither receipt existence nor a newly added Name
receipt is used to infer old-owner activity. This is the exact concrete field
fact missing from a proof based only on history retention.

The whole parent cannot yet follow. The stable followups are:

1. **EFFECT-ORIGINAL-INTERPRETATION-1**, owner original source/interpretation
   lane under primary. Construct the original Kernel.atom interpretations for
   receiptFormation, captureWholeEnvironment, completeBodyConsumer,
   shallowResidualCoverage, shallowLatentPreservation, operationRigidInstance
   and rawContinuationContract. Connect them to the independently fixed
   FunctionGuards.profile, ObservationGuards request/response/guarantee/
   currentAuthority/incidence and actual typed-path clauses. Required input:
   the approved original local contracts and same source/assignment tuple.
   Falsifier: any bridge obtains a local permission solely from equal rows,
   equal families, a historical receipt, or a supplied already-safe body.
2. **EFFECT-CURRENT-WORLD-RESUME-1**, owner original source-owner/current-world
   interpretation. Extend the represented return/Name seam to the actual
   resumed continuation, current world and complete saved frame word; preserve
   old receivers/receipts while resolving fresh executable control. Falsifier:
   an old inactive receiver becomes active just because its saved code resumes.
   This proof is not supplied by source description replay.
3. **EFFECT-SOURCE-RECIPE-AND-COMPACTION-1**, owner existing cooccurrence and
   source-recipe lanes. Retain the existing reviewed transport theorem and
   discharge its constructor/correspondence premises for arbitrary substitution,
   compaction, all merge routes, generalization and use. Actual per-receipt/
   per-route tuples must survive grouped static labels. Falsifier: one route's
   crossing clears another independent scope or receipt.
4. **EFFECT-ORIGINAL-PUBLICATION-REACHABILITY-1**, owner source construction.
   Apply the constructor/consumer facts to whole original reachable source
   environments, including multi-binding recursive publication and all nested
   derivation paths. The raw Environment type permits arbitrary initial maps;
   these lemmas do not turn arbitrary input records into independently valid
   original semantic data. In particular `ScopedValue.event.parents` coherence
   with the stored entry path remains an original admission/formation fact;
   the theorem preserves the whole value, and Environment.extend computes its
   path from the actual entry path, occurrence and payload.

The primary's separate `NativeScopeTransformer.lean` lane addresses exact
native transformer composition/protection algebra. It is complementary and
does not by itself supply the original input/profile interpretation above.

## 4. Checks, actual axiom results, and preserved failures

Owned checker/cache copy:
`/workspace/scratch/e3678bef96db/lean-effect-work`.
Native executable:
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`.
Observed versions: Lake `5.0.0-src+eb6cafb`; Lean `4.35.0`, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Linux x86_64 release.

The isolated dependencies were first built with:

```text
lake build +YulangClosure.OriginalSourceGeneration +YulangClosure.SourceFunctionMembership +YulangClosure.PaperTypeSubstitution
```

The final named audit used the repository skill helper with `--project` pointing
at that copy, `--lake` pointing at the native executable, module
`YulangClosure.OriginalEffectHygiene`, `--timeout 120`, and all 20 names from
`EffectAuditNames.txt`. It performed a focused no-cache module build and a
separate Lean audit file. All commands exited 0. The final focused build had
9 jobs and compiled the new module in 3.7 seconds. Lean invocations were
`-j1 -M1024`; no dependencies or toolchain were changed. Each escalated check
was automatically approved for the pinned native executable and isolated copy.

Final complete printed output:
`/workspace/scratch/e3678bef96db/lean-effect-work/EffectAudit.log`, SHA-256
`c1e74494319c75af11b2f334aa46af80e278dfb3a1019cb8020b0cf081c7a26d`.
Name manifest SHA-256:
`5f6c78023c064e55e53a56ae76a93cbf1000a90db98ab841f4f3b23845d2131a`.

| Audited declarations | Actual complete axiom set |
| --- | --- |
| Ten new original-source publication/replay theorems | `propext`, `Classical.choice`, `Quot.sound` |
| Three new `Native` theorems | `propext`, `Quot.sound` |
| Two new operation identity theorems | Empty |
| OriginalSource.new_use_checks_source_and_client_in_one_frame; alias_keeps_publication_identity; reconstruction; reconstruction_forest | `propext`, `Classical.choice`, `Quot.sound` |
| SourceFunctionMembership.recorded_after_read | `propext` |

These are **named-root audits only**. The helper checks declaration kind and
collects each named theorem's transitive axioms. It is not a complete census of
all private/generated theorem constants. The primary will perform that census
at integration; the leaf did not claim or repeat it.

Supplementary source search found no `sorry`, `admit`, project `axiom`,
`sorryAx`, `debug.skipKernelTC` or `native_decide` in the eight-module project
dependency cone. No trailing whitespace was found. Every dependency and the
final source file matched the isolated copy byte for byte.

Material repair history: five initial focused new-module builds failed on
ordinary proof elaboration/simplification (Option's generic bind normalization,
case-rewritten equality goals, Boolean/all simplification, one reserved local
name and a congrArg inference ambiguity). Those were repaired in proof terms
without changing any existing definition or weakening a statement. A first
successful named audit revealed that the open OriginalSource.Site alias had
accidentally specialized two native signatures to Nat; the final source adds
an explicit arbitrary Site type and reruns the named audit. The earlier
successful audit is retained as `EffectAudit-before-general-Site.log`, SHA-256
`30d36b94c3c1b6c6b674e1712f7310e72d1b9a2c1c2a24ed4a04741971df8b86`.
Earlier failure output remains in the tool transcript; no failed proof is
described as a mathematical counterexample.

No default/full build, Rust execution, benchmark, changed compiler semantics,
native whole-machine correspondence, independent review or original whole
hygiene proof is claimed. Root import integration is intentionally left to the
primary; the exact root-import file was not leased to this worker.

## 5. Frozen inputs and handoff state

All paths in the first table are under `notes/theory/lean/`.

| Direct/transitive input | SHA-256 |
| --- | --- |
| YulangClosure/Contracts.lean | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| YulangClosure/NativeClosureEnvironment.lean | `39aa5cefa078dd423e54f0d9790f9a48e136326742e01f65149f317c907be957` |
| YulangClosure/OriginalSourceGeneration.lean | `ab37f3739d89dff9e7918fb745f5a308a3e597ab4aaa9e5a172fcacaeddabf0b` |
| YulangClosure/OriginalSourceSyntax.lean | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| YulangClosure/PaperTypeSubstitution.lean | `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861` |
| YulangClosure/SourceFunctionMembership.lean | `8d370ee57e486ae48607d1bab493ae5135f28bf8a5a7ff1b0ef240fc0247e424` |
| YulangClosure/SourceIdentityWorld.lean | `6019fd9d57cde50183e016bd0c72de2c6eee72009065d85119fb0348dbcf0168` |
| YulangClosure/OriginalSourceInterpretation.lean (inspected, not imported) | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |

| Governing/correction input | SHA-256 |
| --- | --- |
| notes/design/2026-10-08-source-generalize-definition.md | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| notes/theory/2026-10-08-source-generalize-definition-and-proof.md | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| notes/design/2026-10-10-annotation-effect-hygiene-integration.md | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| notes/design/2026-10-24-cooccurrence-release-clarification.md | `c9eb9b8d274172f02bc82088896c30dd92e219a02adf6ba22418b2cc34207d12` |
| docs/yulang-source-type-safety-ja.tex | `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166` |

Exact repository writes: the new Lean module and this handoff only. All build,
audit and scratch writes stayed in the isolated copy or the checker-owned
temporary audit directory. The checker removed its own temporary audit files.
No Git mutation, dependency installation, central scheduling write, question,
compiler edit or child assignment occurred. The primary owns review,
integration, source-closure status, commits and pushes.

Freeze receipt: source and handoff writes stopped after this revision; no live
checker process or descendant remains. The bounded production packet is
finished with the listed whole-parent obstructions. The worker is available
for a new primary packet or a bounded review-request repair, but makes no
background continuation claim. This file and the module are pending fresh
independent review, not self-certified.
