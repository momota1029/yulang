# Dots cycle155: selected-payload evidence from request provenance

2026-11-13 UTC; start02:27:19, main proof verification around03:00; final report publication after03:17. Hard cutoff03:22:19.
I-25 Evidence lane; ACTIVE/STOP checked on fresh integration/m1-final
`8b65432f1fd903d07c77e855acfebc1c9f683421`. Previous154 publication
`d51d0e182e56d36138a3510809927fafb20cc3f7` recovered; no previous writer running.
Read standing orders, inbox, AGENTS/workflow/testing/docs, prior154 report and imports.
Publish target is work/dots-main ONLY. No Step/Stable/inspection definitions changed.

## 今回の到達点

- 要求ごとの実履歴/記録packetを根拠に、選択された再帰辞書の現在Evidenceを証明。一般形では現在head Shapeと要求coverageが前提。
- 具体的なnamed-output再帰2node例ではcoverage自体も証明し、新しい一般定理を適用。
- reserved出力について初期状態→install→等式反映→実nominal refreshまで構成。最後の3slot状態でKnown出力・正モデル・現在Instance/Evidenceを証明。
- install後も等式反映後も非Stable。最終refresh後のStableと一般evidenceNodeは未完了。

## Main result: soundness, not general completion

21 new modules, 110 public theorems. Public theorem types are in
`dots-cycle-155-types.md`; definition/private/generated dependencies were also gated.
The count includes assembly/transport helpers and concrete regression theorems,
not110 independent language-level completeness results. There are11 general
pipeline modules and10 application/continuation modules (some also contain generic
helpers); the module guide identifies each role.

1. A finite request batch can take each request from a DIFFERENT current recorded
packet. Reachability, actual request membership and singleton variable freedom
imply the batch Models and readiness; no initial Observed target is assumed.
2. A request may instead come from an observation at a REACHABLE earlier state,
with an actual Value trace to the current state. This mixed provenance transports
through actual Value steps. A variable-free actual install adds emitted requests.
Singleton variable freedom is essential to assembly; arbitrary shared variables
and generic nonempty-journal Joint are NOT proved.
3. Current scalar or finite nominal head shapes plus that operational provenance
produce current Instance/evidence. Finite nominal Tree has arbitrary-arity nominal
leaves and the existing wrap/fork constructors. Both head certificates use one
point argument(slot,slot); nominal captures retain injective names and exact
inputNames, while scalar requires inputNames=[]. This is not arbitrary head syntax,
repeated capture or general multiargument coverage.
4. Coverage is needed only along actual selected source descendants. Mutual
induction over the existing Value Classify payload proves recursive Evidence for
EVERY current journal model. Existing Resolves+Completed gives a diagnostic-tree
corollary. No substitute classifier, assumed semantic conclusion or exact executor
was introduced. Deriving shape/provenance for every reachable state remains open.
5. The real reserved-output install proves this selected-path coverage, since its
selected tree is a leaf, its scalar head is explicit and its request is recorded.
The pipeline yields its actual Classify evidence; an explicit positive model
prevents a vacuous all-model result. A mixed old source0/new reserved source2 batch
also satisfies Models before and after actual equality feedback.

## Important negative result: selected does not mean stable

The installed reserved-output journal entails output2 = source0, both the nominal
triple of int. The raw context admits a countermodel where output2=int; hence the
actual Value equate(2,0) rule is enabled and the installed state is NOT Stable.
We construct that step, its reachability, exact preservation of the journal model
set and current Evidence after the step. The later certified-refresh result below proves this equality successor is also NOT Stable.
Stability of the final refreshed state is NOT claimed.
Cycle154 did not prove this reserved fixture stable; this refines its unfinished
continuation, not a reversal of a previous stability theorem.

## Module map

- RequestBatchAssembly: variable-free singleton assembly.
- RecordedBatchModels, RecordedTreeBranch: distributed recorded requests to models/head evidence.
- RequestProvenance, RequestProvenanceTrace, InstalledRequestProvenance: mixed
  reachable historical/current-recorded sources, trace transport, actual install.
- ProvenanceTreeBranch, ProvenanceScalarBranch, ProvenanceHeadBranch: current
  structural head certificates to Instance and node evidence.
- ProvenanceClassification: stronger global coverage intermediate theorem.
- SelectedProvenanceCoverage: selected-descendant coverage and full payload soundness.
- ReservedInstalledEvidence, ReservedOutputEquality, ReservedEqualityStep,
  ReservedInstalledClassification: actual fixture semantics, feedback, classification.
- ReservedMixedProvenance, ReservedClassifierSoundness: inhabited application tests.
- ReservedSuccessorBoundary: historical intermediate proof boundary and no-reobserve.
- NonterminalProvenanceApplication: actual recursive named-output coverage/evidence.
- ReservedNominalRefresh: actual carrier extension, model equality and nonstability.
- ReservedRefreshedEvidence: current Instance/Evidence in the new3-slot context.
All names above have prefix `GeneralDictionary`. All21 are exported by Yulang.lean.
Audit.lean, README, lake settings, spec and plan were not edited.

## Verification

Lean4.35.0. Focused build of the21 changed modules (--wfail): PASS,791 jobs.
11 Audit/Cycle155*.lean shards, each `lake env lean --trust=0`: PASS.
Complete dependency gate for all constants owned by these21 modules, including
private/generated definitions: PASS,278 declarations; only propext, Classical.choice,
Quot.sound. All110 public theorem `#check @...` outputs: PASS.
`verify-lean.sh . 8b65432f1 --no-build`: PASS, diff-only; no full build/audit claim.
Logs and exact commands appear in dots-cycle-155-validation.md.
No sorry/new axiom/native_decide. Focused checks do not prove language completeness.
Full repository build/audit is left to the supervisor per standing orders.
After code freeze, all21 new source files were additionally re-elaborated directly
with `lake env lean --trust=0 <file>`: PASS. This is independent of merely requesting
a cached focused build; it still does not constitute a full repository build.

## Review, failures, limits

Independent review and an actual application checked the scope of current-model
transport, selected-path coverage and the nonstability distinction. Development
errors (constructor/type details, audit import ordering and temporary gate syntax)
were corrected and the final tests rerun. An initial GitHub commit request used an
incorrect parent SHA and failed validation without changing a ref; retried with the
verified full SHA. All successful publications use nonforce expected-head leases.
No Git blob approval was requested in this cycle; inline tree content was used.

Existing Yulang2 x-oracle cases were consulted; no new Yulang2 runtime/parser
comparison, complete language equivalence, CI success or general termination claim.
The freshly fetched Astra fresh-pump note explicitly remains a draft mathematical
counterexample with a kernel-checked algebraic core, NOT a full infinite Step trace.
Its unresolved general termination issue is inherited, not settled by these results.

## Boundary inventory

Checked, Models, RootPending, RootK2, CandidateK2, InspectionPending, Survivor,
Reorders, DictionaryEquivalent, Step, Stable, Generated, Evidence all have existing
general definitions. Definitions alone are not full-language correctness.
General V5 remains8/14 obligations unfinished: progress, execution, halted,
whereAccessible, treeExecution, canonicalLocalOrder, evidenceNode, generatedChildren.
Our conditional soundness does not close general evidenceNode. Completeness and
principality are not claimed. General alias/head coverage, arbitrary query/capture,
nonempty-journal Joint and fresh-request coverage remain open.

## Publication and continuation

- 3442f6c19c94cd163a698ca9e2d64aa1c2359650: start heartbeat.
- a7cc9b0b8b0fddb48c56beff816d032c7e312db3: first source checkpoint.
- 5bb19b3666c036fe7b1ac4ca53e1269fba82aa4e:13 modules and20-minute heartbeat.
- acf14e46b33a59063a4dfc983717503d6d77514a:17 modules and30-minute heartbeat.
- 519aa15fb94e4fa2d989ea94799fa51bc805125f:19 modules and approximately40-minute heartbeat.
- e6cba10990cb28e0972cc356dbd86996373e55dd:all21 source modules, all audits and design notes. Immutable fetch and byte-identical Lean/design readback PASS.
Each source checkpoint fetched by immutable SHA and compared with local Lean files;
final source checkpoint has zero Lean-tree diff. No concurrent branch overwrite.
Final report publication is the commit containing this file; see branch history.

Next proof targets (names proposed, not existing completed declarations):
1. `refreshed_stable`: check every actual Value constructor for the final3-slot
   reserved fixture, including all installable packets, refreshed observations,
   enqueue and alias merge. Do not infer this from Classify or Known alone.
2. `reachable_request_supported`: derive request provenance from general actual
   fresh-allocation histories rather than supplying a final-batch certificate.
3. `reachable_selected_structural`: derive current structural head coverage on
   selected descendants, extending syntax only when source semantics justify it.
   This is still not a general alias/Joint or termination proof.

## 日本語索引・受入条件・資源

全110定理名と前提を含む日本語の主張は `dots-cycle-155-claims-ja.md`、正確な量化は型付録に収録。I-25のcurrent-context Evidenceに関して、履歴/recorded要求の混在、実Value feedback、selected descendantのみの条件付きsoundnessと具体的非空例を達成した。一般evidenceNodeは未完了。今回新しい言語意味論の判断は不要で、質問ノートは追加していない。使用量枠は不明。

source checkpoints acf14e46 / e6cba109 のCI combined statusesは空、workflow APIはPRイベント限定で空だった。CI PASSとは報告しない。

## Successor stability boundary (additional verified work)

ReservedSuccessorBoundary adds6 theorems: feedback has RawEqual(2,0), but output2
still has no carrier slot and is not Known. All descriptors are PointClosed,
therefore ANY Revision cannot Improve: reobserve is excluded. At this intermediate proof stage Stable was not proved. The later actual refresh
below disproves it. Its necessary-condition theorem excludes an output2-known certified
refresh only UNDER an explicit Stable premise, never as an unconditional fact.
Refines permits carrier extension, so current finite slots do not eliminate
that case. At that intermediate stage remaining cases were enqueue/generated closure, arbitrary installable
packets committed, other journal equalities, certified refresh, and alias merge.

## Recursive application (additional verified work)

NonterminalProvenanceApplication constructs the current ternary nominal parent
and scalar child Shapes of the existing actual-install fixture. Its parent request
is supported by the actual initial observation and actual install trace; child
requests are empty. Local functionality bounds SelectedPath to root/child, so
Covered is DERIVED. The new general theorem proves Evidence of the actual recursive
Value Classify payload for every current model. An explicit inhabited example has
one child and nonempty named outputs. Old Evidence/BranchModels was not used as
a premise in the coverage proof.

For reproduction, the complete module dependency gate is committed at
`lean/Audit/Cycle155DependencyGate.lean`; run it with `lake env lean --trust=0`.

## Actual nominal refresh: the equality successor is also NOT Stable

ReservedNominalRefresh constructs a genuine2→3 slot carrier extension. Slot2 has
the same ternary nominal descriptor as source0. Original rows are retained and
new slot2 uses rowSource0, avoiding an unproved new row constraint. The Refines
and all-current-model snapshot certificate are proved; sources are preserved.
This is a real Value refresh, not an assumed extension. It makes reserved source2
Known, preserves the journal model set exactly, and yields a reachable state with
an explicit positive model. Hence the equality successor is NOT Stable too.
Only stability of the FINAL REFRESHED state remains open. This supersedes the
earlier intermediate uncertainty about the equality successor's refresh case.

## Current evidence after carrier-changing refresh

ReservedRefreshedEvidence constructs current scalar Shape at slot1 of the3-slot
context, Metadata, recorded-request Covered and Supported. The new general
scalar-head theorem yields current Instance and Evidence for EVERY refreshed
journal model. No Local, Stable or executor premise and no stale-context Evidence
are used. The combined result includes actual initial reachability, positive
model, Known output2 and current dictionary. Final Stable/refresh-stage Classify
remain unproved, and the general V5 obligations remain unchanged.

## Publication checks

The final source snapshot has both the fresh integration base and the prior cycle
publication as ancestors. Its complete tree differs from the tested local tree
only in the expected unpublished report files and heartbeat; Lean and design
files match byte-for-byte. Final delivery contains40 content paths plus the
heartbeat (41 changed paths relative to the fresh integration base).
Documentation/import/audit cross-check found no omissions among all110 public
theorems: each has an export module, audit entry, exact type and Japanese claim.

## Finalization

Report finalized 2026-11-13T03:17:38Z, elapsed 50.3 minutes. All source verification passed and immutable source readback passed before final report publication. Publication/readback must finish by03:22:19UTC. No running writer remains.
