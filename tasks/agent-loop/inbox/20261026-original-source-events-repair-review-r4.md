# OriginalSourceEvents repair: independent review r4

Verdict: **ACCEPT for the exact repaired source-metadata, dependent-data and
local-consumer scope below.** Both earlier findings F1 and F2 are resolved.
No blocking or major finding remains within that scope. Full original
source/native inference soundness and the remaining semantic bridges stay OPEN.

Reviewer: `/root/function_future_review_r4`, independent nonauthor generic
proof-role fallback. The reviewer authored neither the original module nor its
repair. Applicable AGENTS/base/proof rules, the `yulang-lean-proofs` skill and
its source/execution references, and `.codex/agents/lean-prover.toml` were read.
No descendants or model override; effective model/effort settings are UNKNOWN.
The primary retains adjudication, shared-status changes, Git and publication.

This is a distinct review from the exhausted rejected packet. It began at
2026-10-26 15:53:17 UTC with 1200 seconds and at most three focused 120-second
checker bundles. One bundle was used. Only this new repository receipt and
`/workspace/scratch/f98087c7ac1a/source-events-repair-review-r4/` were written.
The old review, old scratch, rejected snapshots, core, configuration, imports,
author files, Git and shared status were not changed by this reviewer.

## Exact accepted freeze and preserved rejection

| Artifact | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalSourceEvents.lean` | `df3469e907867c6f884b17b589d078b58a3dd674a589e1d16baa05b0f004e61b` |
| `notes/theory/2026-10-26-original-source-events.md` | `96108ef0429329c85e876b42f315ee3e6c8356c3b47a6e086ab40c7e59bd7de1` |
| `tasks/agent-loop/inbox/20261026-original-source-events-r4.md` | `8d57fcf06062209e452f849f8c2e5be8243ae2bf6e0a85c84d29fd3492b46b6b` |
| `source-events-r4/repair/freeze.json` | `b6fca2f3d79531a30b006495f9192a676e626bab840656a55b2dea2ff26261e0` |

The author reports final writes/checkers stopped at 15:57:21 UTC. All 163
repair artifacts, three final outputs and ten unchanged dependency sources
were independently hashed. The reviewer read the complete repaired module
through the original full source and exact complete delta, the final note and
producer handoff, and the complete audit/runner/parser implementations.

The independent recursive input closure is 11 Lean sources plus three unchanged
configuration files. All 13 dependency/configuration hashes equal those in the
previous independent review; only `OriginalSourceEvents.lean` changed. In
particular Environment remains `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132`,
Generation remains `0f25e53350edf9c452fd3c0f461602437ca2adf979859fda5e2492bcc403ae55`,
Interpretation remains `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`,
and Signature remains `ed07890e29b4dcb38cabd18ec0e196efde9e95c64902942a9906a470b38c3311`.
No WorldReadout or disjoint termination successor was imported.

All 274 original author artifact hashes, all 278 before-repair snapshot
payloads and all 183 private artifacts from the rejected review were rechecked
unchanged. The original rejection receipt remains SHA-256
`5efbe584a8f39949a87bf0d3cd5767fcc463a5213a3577014be2a9707010a80f`;
its additional author-side copy matches. The old REPAIR REQUIRED decision is
not relabeled as acceptance. The new note and producer correctly preserve the
old collision and the old incomplete 49/17 census with its 52/19 correction.

## F1 closed: generic route identity, not a fixture-only correction

The entire old module prefix was independently compared. Its only executable
changes are the two choice-right edges in `owners` and `entries`, from tag 1
to tag 3. Its route comment is corrected; every other preexisting source byte
is preserved. All 40 prior named public roots retain byte-identical complete
printed type/axiom blocks. Thirty-two named roots are added.

The repaired construction uses 0 for descent/choice-left, 1 for advancing the
forest tail, 2 for retained-evidence extension, and 3 for choice-right. The
complete `treeRoutes`/`forestRoutes` definitions cover every existing tree and
forest constructor. They enumerate tree-node positions; an empty forest
contains no such position.

The actual proof dependencies and quantified types were inspected:

- `tree_routes_routed` and `forest_routes_routed` prove that every enumerated
  path extends the supplied prefix and has no reserved tag 2 in its relative
  suffix. The prefix itself is arbitrary; the original source traversal starts
  with the empty prefix.
- `route_edges_separate` separates all descendants under distinct next tags.
  `tree_route_shape` and `tree_sibling_separation` show that a tree's root,
  descent subtree and choice-right subtree cannot collide with any descendant
  of its next forest sibling.
- `tree_routes_nodup` and `forest_routes_nodup` are mutual structural proofs
  for arbitrary RuleTree/RuleForest inputs. They assume no Site uniqueness,
  already-unique inventory, source-image restriction or absence of choice.
- The four owner/entry route-sublist theorems are **ordered** inclusions in
  the complete inventories. Their local binder/entry lemmas prove at most one
  emitted route per node. The four corresponding `*_routes_nodup` theorems
  therefore apply to the actual traversals, rather than an unrelated list.
- Tree and forest `reserved_tag_separation` exclude tag 2 at every relative
  depth. `retained_owner_separate_from_tree` applies this to an actual collected
  entry, and `distinct_retained_routes` uses injectivity of appending `[2]`.
- `different_routes_different_keys` and
  `different_record_routes_different_keys` preserve the resulting distinction
  in both key constructors with the remaining raw coordinates held fixed.

The final author probes retain the rejected old walk definitions and prove
the original collision, then check corrected owner/entry outputs, both key
distinctions, nested choices, repeated equal sites/binders/context and a
retained slot below a non-root entry. They include arbitrary-input generic
Nodup applications. The old counterexample remains a generic rule-tree
discriminator, not an original independently admitted source-program example.

The independent reviewer additionally proved the corrected collision outputs
and both key distinctions at **arbitrary prefixes and complete enclosing
scopes**, with the original telescope retained in both owners. It applied
reserved-tag separation to an actual entry collected from an arbitrary forest,
and applied both inventory uniqueness results directly to `sourceOwners` and
`sourceEntries` for arbitrary original source categories. These checks add no
premise that the original program uses distinct Site numbers.

## F2 closed: complete current-module origin inventory

The repaired audit selects imported declarations by their actual module index
and scratch declarations by `env.getModuleIdxFor? name == none`. It has no
namespace filter for completeness. It prints each declaration's actual
ConstantInfo kind, complete type and transitive axiom result, rejects project
axioms, and checks every required originating root and named scratch root is
an actual theorem in the corresponding inventory.

The previously omitted private `sourceRules.match_4.eq_1`, `.eq_2` and
`.splitter` are present under the current audit module's private prefix, with
complete types and no axiom dependencies. All current-module private/generated
declarations are included. This closes the original audit-completeness defect;
the new 97/34 figures include the old probes, rejected encoding and repair
regressions, so they are not merely a renamed version of 52/19.

| Independently reproduced inventory | Constants | Theorems | Required named roots |
| --- | ---: | ---: | ---: |
| OriginalSourceEvents origin | 785 | 268 | 72 |
| Complete author audit module | 97 | 34 | 24 |
| Separate reviewer probe module | 17 | 11 | 9 authored checks, plus generated declarations audited by origin |

The 785 originating constants comprise 434 definitions, 22 recursors, 268
theorems, 22 inductives and 39 constructors. The author audit module comprises
63 definitions and 34 theorems. Required roots exactly equal the source's 72
authored theorem declarations: prior 40 plus 32 new. No generated theorem is
misrepresented as an additional authored mathematical result.

An independent balanced-record parser reconstructed every type/axiom block,
checked names, kinds, uniqueness, full type headers including wrapped universe
arguments, original rendered summaries, canonical dependencies and type hashes.
Its records match both author JSON inventories field for field. The fresh raw
audit log is byte-identical to the author's final log, not just equal in count.
No elision, truncated record, unexpected diagnostic or unapproved axiom occurs.

| Actual transitive axiom set | Origin constants | Origin theorems | Audit constants | Audit theorems |
| --- | ---: | ---: | ---: | ---: |
| None | 632 | 157 | 61 | 17 |
| `propext` | 129 | 92 | 29 | 11 |
| `propext`, `Quot.sound` | 14 | 12 | 3 | 3 |
| `propext`, `Quot.sound`, `Classical.choice` | 10 | 7 | 4 | 3 |

The independent probe's 17 constants have dependency counts 9 none, 4
`propext`, 1 `propext`/`Quot.sound`, and 3 all-standard. Its three generated
private declarations are also included. No axiom-free claim is inferred from
the surface spelling of a proof.

These are isolated-origin counts. The previously noted generated
`OriginalSourceEnvironment.put.eq_1` must remain in any integrated census even
if its origin is an earlier imported module. This receipt does not certify an
aggregate theorem total by adding 268 to another environment's count.

## Original-source application and precise semantic limits

The governing SG §3.3/§5.2, Call-input realization §§2–4 and selected contextual
Function-membership authority were read against the actual original source
generation, Environment, Contracts and Signature declarations. The repair
changes neither the parent language nor its semantic admission predicates.
The accepted application is the following concrete construction chain.

`sourceOwners` and `sourceEntries` traverse actual `sourceRules context source`,
not an assumed successful rule package. The Lambda equations derive invocation,
receipt and parameter-entry metadata with arbitrary original pattern and body,
including the formal binding context, annotation, entry role and receipt
operands. Those explicit equations use an unannotated outer Lambda mark;
the general traversal retains annotation wrappers and the full existing syntax.
This does not assert completed semantic cases for every source constructor.

The retained formal owner is new metadata demanded by SG's original Shared
obligation. For Value entry its ordered telescope contains the original
description/view/invocation/receipt prefix followed by actual Return/rebind;
for computation entry it remains below receipt without an invented Force.
The original generated Lambda's lack of a rebind `sharedE` is a representation
gap, not semantic permission to omit retained evidence.

`ScopeValues`, `lambdaPrefix`, `returnedPrefix` and `carrierPrefix` preserve the
complete provided payloads at their structural binder kinds. Value and carrier
installed tuples remain distinct. Given the Return-shaped `Returned` input,
`returnedEvidence` uses its same value/root; `lambda_actual_return_install`
applies that source-derived formal registration to the actual existing
`Decoded.shared` consumer, installing the same descriptor/value/root and
binding the actual formal name. This is a real local consumer application,
not an assumed source judgment or desired membership fact. It does not prove
that an arbitrary computation returns, or that this supplied Return record
arises from evaluation of a particular source body.

Other installed addresses and every old fixed frame are preserved by the
stated local lemmas. The complete new Shared data, including its witness,
remains in the appended frame. No invariant of the entire future witness map
is assumed. The legacy Frame still lacks the new route coordinate, and the
packet's typed prior telescope is not yet linked to every live decoder state.
Actual Outcome emission, Decoded.runtime installation, route-preserving Frame
correspondence and the emitted formal constraint telescope remain OPEN.

The Signature `Catalogue.Packet` is reused as data on one common Joint:
each output is exactly the corresponding projection from that tuple. The
actual `Introduction.License`, `Occurrence`, `PortProv` and licensed-field
interfaces were inspected. No independent operator license is manufactured,
replaced with `True`, or inferred from static support. Opaque field meanings
and semantic compatibility remain independently supplied obligations.

Runtime-owned fields and per-description EventProof remain separate.
`Description.interpret` may change the permitted decorated witness without
changing the actual packet/key. The local `ownedReadout` computes the six
dynamic fields from one assignment at one captured owner/origin/parent path/
occurrence. Its event equation needs no readback-law premise, retains the old
fiber/eta0 and takes history/current from actual Runtime.after. The key and
Owner metadata do not by themselves authenticate a global source-owner
relation or encode every scoped payload. Route uniqueness is proved within
the fixed traversed tree/forest; a global all-event readout is not supplied.

Initial, Response, raw Resume and FutureUse records retain their full supplied
raw operands, including original context, request/operation, handles,
continuation, pending suffix, returned provider/root/port and current data.
Raw/decorated round trips prove coverage of this **data grammar**. They do not
establish all independently admitted semantic challenges. `sourceRecord`
checks structural binder kind only; the independent generic Lambda probe
confirms that a Response record is rejected as an invocation. This is not an
admission, anchor, successful-execution or safety filter.

The Response erasure collision remains a formal-interface discriminator.
Neither original admission of both alternatives nor impossibility of every
faithful host interpretation is proved; an actual owner/Receipt relation may
provide additional information. The richer RecordKey retains operands that
the legacy Runtime.response projection omits, but that projection has not been
made into a complete global readout.

Empty semantic sorts are not silently inhabited. The reviewer instantiated an
empty Value sort and proved that a `Returned` record then implies False.
The metadata traversal and its generic uniqueness theorem impose no runtime
Value inhabitant or complete typing certificate.

Consequently full original Event/EventField owner correspondence, domain/value
reading at every independently admitted Initial/Response/Resume/FutureUse,
view/incidence/guards/captures, full PhiW, Function closure, KernelSound,
source cases, hole replacement, general L4 and successful native correspondence
with the same scoped witness remain OPEN. The actual
`YulangClosure.SourceProblem.InferenceSoundness` parent is not instantiated by
this packet. These limits are stated in the accepted final note and handoff.

## Execution, failures and stopped handoff

The independent run used the pinned absolute native Lake, Lean 4.35.0 commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, and Lake
`5.0.0-src+eb6cafb`, with one CPU/thread, `-j1 -M1024`, a 120-second total
bundle deadline and 1280 MiB process-group RSS ceiling. The project and cache
were newly created. All imports and the module were freshly built; no author
olean or old-review cache was reused. Configuration and dependencies were
copied unchanged. The explicit module target does not modify default imports.

The same bounded wrapper used permitted execution escalation because the
ordinary-sandbox Lake installation failure was already observed and retained
in the preceding review. No installation/path/toolchain workaround was used,
and the known failed startup was not repeated merely to consume another bundle.

| Independent command stage | Result |
| --- | --- |
| Native Lake and Lean versions | Both exit 0 and match the pin |
| Fresh explicit module build | Exit 0; 66.531388 seconds; peak 1052676096 bytes |
| Independent repair/scope/empty-sort probes | Exit 0; 1.333548 seconds; peak 1160372224 bytes |
| Complete author audit rerun | Exit 0; 4.341160 seconds; peak 1183502336 bytes |
| Entire bounded bundle | Exit 0; 72.473194 seconds; no termination or resource breach |

| Independent log | SHA-256 |
| --- | --- |
| Fresh build | `e450cbfef559a89232c72e0df1bccbbcd97687dd15428fd9c17432ff2a562972` |
| Reviewer probes | `1ecfac468399682d13bc707a42bc4aeb308a773458c603491c3d035828f582a0` |
| Complete census | `b7beda0ce830ad960849b397836f45ef92e57e09e452cbd1cc04fb938d66b870` |

All six author repair receipts, their source snapshots and full logs were
verified. Checks 1–3 remain failures, including the provisional elaboration
warnings; check 4 builds final module bytes, and checks 5–6 pass the audits.
The failed workdir start and initial universe-suffix parser rejection are
retained. All original rejected-packet and reviewer failures remain immutable.
No failure occurred in this new review's checker bundle or evidence parser.
The dependency-cone source scan found only an explanatory comment mentioning
the word axiom; it supplements, rather than replaces, the complete axiom audit.

The final private `artifact-manifest.json` records this receipt, final output
hashes, all 14 inputs, author and predecessor manifests, full independent
records, the exact reviewer attempt and source correspondence evidence.
`stopped.json` follows the manifest to avoid a self-reference. No reviewer
checker, child or background writer remains; all owned writes stop after those
files. Only the primary may integrate and publish this exact accepted packet.
