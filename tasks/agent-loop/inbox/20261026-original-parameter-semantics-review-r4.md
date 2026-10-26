# Original parameter semantics — independent review r4

## Decision and exact closure

**ACCEPT the frozen local missing-native presentation and computed parameter-bind
world constructor. No blocking or major finding was found in that scope.**

This acceptance is for `OriginalParameterSemantics.lean` and its final paired
note/producer receipt. It does not certify original whole-source inference
soundness, a full original/native dependent-scope correspondence, actual
Force/result-port membership, or legacy formal Shared delivery. The final note
and producer receipt state those limits explicitly and accurately. Root owns
integration, status changes, commits and pushes.

The accepted three outputs are:

| Output | Bytes | SHA-256 |
| --- | ---: | --- |
| `notes/theory/lean/YulangClosure/OriginalParameterSemantics.lean` | 45,481 | `733c5b05e0db226f95d14ff2161c46e9a389b43d86b365b000a9656ec4fd0bd2` |
| `notes/theory/2026-10-26-original-parameter-semantics.md` | 21,826 | `805a7320f66ba4d118a2866e539d70eab634e35abe40db86f78da510cb3bc88c` |
| `tasks/agent-loop/inbox/20261026-original-parameter-semantics-r4.md` | 13,825 | `bee3774c10702243d74730b7c3cd36b6109bf1ce07bb5432ade45a30af47f273` |

Source freeze: 2026-10-26T16:45:04.468840+00:00, after author clean check 14.
All author writes/checkers stopped at 16:51:26.183746 UTC. The exact final
author freeze was independently verified, including all 356 manifest entries:

- Author artifact manifest: `cb6c6a776b70fe4749bfea427a303b7f946cbd5871445410d0c708cac4b92476`.
- Author freeze: `379e71ce1027b0b364050b38dc3bbf4fb97f91f1158652779fe7417f4db09eff`.
- Author stopped metadata: `16482041a79abd18ba6b56fa52b7e3b6b7238ebaabc09937e9ed4e8fa94dbc1c`.

## Identity, authority and lease

Assignment `parameter_semantics_review_r4`, handoff revision 1. Actual worker:
`/root/parameter_semantics_review_r4`, a fresh nonauthor reviewer. Activation:
2026-10-26 16:47:56 UTC; deadline: 17:07:56 UTC. No configured specialist launch
is claimed; the available worker read and applied the Lean-prover fallback.
Requested model/effort override: none. Independently observed runtime
model/effort metadata: UNKNOWN. No descendants were launched. No contribution
was made to the submitted source or its proof repairs.

Exact writes: this one new inbox receipt and
`/workspace/scratch/f98087c7ac1a/parameter-semantics-review-r4/` only. No source,
configuration, native/Rust, Git, old review, shared status or other agent output
was edited. Three independent scratch probe theorems are review evidence only.

Read authority included root AGENTS and its preserved base, active sprint and
orchestration rules, design authority, inference top-level principles, the
complete `.agents/skills/yulang-lean-proofs` skill and its execution/source
references, and `.codex/agents/lean-prover.toml`. Actual mathematical source
checks included SG §3.3; call-input construction §§3.2–3.3; original-interface
embedding §§6.1–6.2; and the actual Interpretation, Environment, Pair and
WorldReadout definitions reached by this module. Historical proof progress is
not used as a substitute for those definitions.

The accepted stage1 source dependency remains
`73af381dcf6796a06d9508b8c7725ce6b3dfc0c84c3193246a3db5d8bbc1dc64`,
published at checkpoint23 `1e6d1cfcca1a653d3bfd16193adc2e7e70aaa648`.
Its prior independent review is carried forward for its own source claims;
this review independently rebuilt the complete imported cone. Neither the
separate scratch Shared migration nor subsequent retained-Computation work
was used as an input.

## Independent verification and resources

The reviewer recursively collected the exact 17-module source import cone and
three configuration files into a fresh isolated project. All 20 source/config
hashes were checked against the live repository before each bundle and again
after checking. No author or sibling `.lake` cache was imported into this
checker project. Toolchain: Lean 4.35.0, commit `eb6cafb`, matching native Lake
5.0.0-src. The previously established native-tool sandbox fallback was used
with explicit bounded escalation; no configuration/toolchain workaround was
introduced.

Two of the maximum three immutable-input bundles were used. Each was limited
to 120 seconds aggregate, one pinned CPU/thread, Lean `-j1 -M1024`, and
1280 MiB aggregate process-group RSS. Both passed; no timeout/RSS termination
or failed Lean invocation occurred. The unused third bundle is not needed to
resolve a remaining concrete risk.

| Bundle | Checks | Aggregate elapsed | Peak process-group RSS | Result |
| --- | --- | ---: | ---: | --- |
| 1 | Versions; fresh explicit `lake --no-cache build +YulangClosure.OriginalParameterSemantics`, all 18 jobs | 76.200 s | 1,049,858,048 bytes | PASS |
| 2 | Versions; unchanged-input explicit build; three independent probes; full origin/current audit compiled to an actual `.olean`; import and census of that compiled audit | 4.789 s | 1,171,759,104 bytes | PASS |

Full commands, logs, source/config snapshots, exit statuses, resource samples
and hashes are in `attempt01/` and `attempt02/`. The fresh build itself took
75.923 seconds. Relevant full-log hashes:

- Fresh build `attempt01/03.log`: `019f728c31eda552935a844143a533494258b99c925ed31946bf3a19607f7d7c`.
- Independent probes `attempt02/04.log`: `7e07a21dc175f8a3d426e53e3c015566704b9e35e9eba713ccffd9cf01b16627`.
- Complete origin/current audit `attempt02/05.log`: `cd97c58961ba98ccf6facbb41726400a95b5568de19773269ed97fe819a56dbc`.
- Actual compiled/current audit `attempt02/06.log`: `fa3851d695692ff1069b827d6e62af6f7aa5d963b2785d8d4842b9180e32ddfd`.

The census code selects declarations by Lean module origin, not namespace.
It checks every originating and current constant's kind, full type and
transitive axioms. The reviewer inspected that mechanism and independently
reran it against the fresh build. The compiled closure command imports the
actual generated census `.olean`; it is not a census of an uncompiled script.

All 267 independently generated full type/axiom records exactly match the
author's full inventory and check15 output. Every one of the 38 names also
matches an authored source theorem and an originating theorem constant. The
inventory includes nine private constants, including generated `sourceRules`
match auxiliaries, and the additional foreign-namespace originating constant
`YulangClosure.OriginalWorldReadout.captureAddress.congr_simp`. None was lost
to a namespace-prefix filter.

| Origin/current inventory | Count |
| --- | ---: |
| Target originating constants | 267 |
| Definitions | 153 |
| Theorems, including generated auxiliaries | 86 |
| Recursors | 9 |
| Inductive types | 9 |
| Constructors | 10 |
| Authored theorem roots, all inventoried | 38 |
| Current census-module constants | 0 |
| Originating constants in the actual compiled census module | 0 |
| Current closure-audit constants | 0 |
| Project or unapproved transitive axioms | 0 |

The complete, disjoint axiom-set distribution is:

| Transitive axiom set | All 267 constants | 38 authored roots |
| --- | ---: | ---: |
| None | 224 | 18 |
| `propext` | 33 | 11 |
| `Quot.sound` | 1 | 0 |
| `propext`, `Quot.sound` | 8 | 8 |
| `propext`, `Quot.sound`, `Classical.choice` | 1 | 1 |

This confirms absence of `sorryAx` and project axioms in the accepted compiled
target. Ordinary theorem parameters and the explicitly retained semantic
premises remain parameters; an axiom-clean theorem does not discharge them.

Author checks11–16, all exact snapshot inventories and all failures were
verified and retained. Check11 is a genuine failed elaboration, with its
ActualEvent constructor mismatch, transparent-sort rewrites, untyped installed
object and generated sorry diagnostics; it is not accepted proof evidence.
Checks12–16 passed. Source14/15/16 is the frozen accepted source. The review's
non-Lean metadata helper had two schema/pretty-printer assertions and one slow
unbounded regex, all recorded in `inspection01.log` through `inspection04.log`
and `read-diagnostics.json`. The exact owned slow helper was terminated; the
bounded parser passed. Truncated read-only tool displays were reread in bounded
calls. No failed checker or source snapshot was discarded.

## Semantic findings: what the proof actually constructs

1. **The local formal is selected before invocation.** The typed Telescope
   preserves complete Frame payloads, binder/kind evidence and supplied event
   metadata. Its values and its original `decodeFrame` replay use the same
   frames. `declareValueFormal`, `selected_at_original_formal` and
   `source_formal_phiW` select the descriptor from the complete explicit prior
   tuple and use this Parameter's actual formal name. The real root-Lambda
   Description binder is computed, and `decode_formal_description` is an
   equality using the original decoder. No post-Return selection of A is used.
2. **The native representation is data, not a safety subtype.** Snapshot
   preserves the represented native World, providers, raw aliases and original
   residual field. Arbitrary stores, saved references and guard-failing records
   remain inhabitants. The pack/unpack inverses concern the newly defined
   native Event and Presentation only. `initialRoot` computes a new native
   root's readout; it does not reset an existing original Environment.
3. **The operator is fixed before the bind.** `inputs base references` reads
   every raw `Some`, uses actual saved-environment lookups for aliases/captures,
   and uses the same cell interpretation for capture values. Nonworld fields,
   checking domains, event coherence/guards, raw Force, traceForm and complete
   observation fields remain the supplied old fields. No desired final-world
   equation, return-descriptor oracle or semantic membership filter was added.
4. **The bind constructs the full world clause.** `bind_installed` derives the
   actual append/readout equation from native `bindValue`, physical vector
   support and the fresh-address contract update. `bind_phiW` preserves all old
   value/carrier certificates through the candidate restriction action and
   uses the actual new-value certificate at the fresh cell. It also constructs
   alias, capture and Shared agreement. Prior PhiW, real saved-environment
   bounds, actual parent lookup, candidate restriction, independent current
   coherence/guards and that returned-field certificate are explicit premises.
   Post-PhiW and a post-registry equation are not premises.
5. **Capture preservation handles the changed assignment.**
   `bind_capture_value` uses actual old CapturesAgree, the vector bound and
   complete readout preservation. It is valid for old nonlatest saved
   environments and shadowing; it does not apply an unchanged-assignment lemma
   to a changed contract map. The fresh contract cannot overwrite a populated
   old cell under the stated vector premise.
6. **Alias identity is actual cell identity.** The native alias operation
   preserves both handles at the same actual address and reads its complete
   contract. Equal raw payloads or equal view tags are not substituted for
   address identity. The helper does not authenticate arbitrary publication
   identifiers or missing source registration.
7. **Meaning and Background use their own hereditary clauses.**
   `meaning_installed_restrict` derives value/carrier restriction from Meaning.
   `bind_meaning_world` unfolds and folds that same world meaning.
   `bind_background_world` uses the actual Background restriction and hole
   future action, with no world holes. Completed Checking is not repurposed as
   an arbitrary `B_H(B) -> B_H(A)` theorem. Both consumers retain the correct
   event-future/guard and returned-field assumptions.

Three additional reviewer-authored probe theorems were checked, with all
three full current types/axioms printed:

- `dangling_capture_prevents_world`: a visible captured address with no raw
  cell contradicts PhiW. A dangling capture has not been erased to obtain a
  world certificate. No axioms.
- `all_some_not_filtered_by_count`: every present raw cell is semantically
  required by PhiW even if its index lies beyond an arbitrary store's nominal
  count. This checks the unbounded quantifier; it makes no reachability claim
  for that invalid raw store. Axioms: `propext` only.
- `new_value_certificate_required`: a post-bind PhiW certificate implies the
  actual new-value membership at the selected descriptor, interpreted raw value
  and root. Thus the new semantic obligation is not bypassed by constructing
  data. Axioms: `propext`, `Quot.sound` only.

## Discriminators and retained parent obligations

Repeated Sites, erased-operation collisions and original description/key
identity retain stage1's accepted exact-coordinate scope. This module neither
repairs every legacy lookup nor adds injectivity of erased runtime events.
Same-view/different-cell contracts remain address indexed. Distinct proof-use
routes can share one retained complete target, while typed predecessor data
are not erased merely because the raw key agrees. Changed current EventFields
can coexist with unchanged old scoped Shared values, and equal native cells
do not determine the logical scoped witness. These are local data/strategy
theorems, not a universal original-scope equivalence.

The following are **unclosed parent obligations**, not hidden acceptance of
stronger claims:

1. `NativeWitness b View.shared` has domain `SharedPosition b View`, with
   `ScopeValues b View`. Native sorts replace Configuration, Assignment and
   JointWitness, so this is not automatically the full preceding dependent
   domain `ScopeValues (NS b ...)`. No total typed-scope/strategy/overlap
   correspondence is proved. Event product roundtrips do not supply it.
2. Binder/kind agreement does not authenticate actual source occurrence,
   enclosing telescope, route or event-parent incidence. The supplied complete
   metadata and original decoder equality are preserved local constructions,
   not an actual legacy successful generation/history derivation.
3. Actual Force execution, designated Entry/result-port membership at the
   preselected A, and any required B-to-A comparison remain unconstructed.
   The genuine returned-field certificate remains an explicit premise. The
   existing source generator has the stated role/receipt/return-rebind atoms,
   not a newly proved source-owned semantic result-port equation or CheckGoal.
4. Full legacy formal Shared generation, actual retained-anchor consumption
   and post-bind source-environment/world correspondence remain open. The
   separate scratch migration is outside this review. No actual generated
   source step was silently replaced by the new local frame.
5. `pending_has_no_returned_constructor` is the data-level inequality between
   an Outcome without a result and the Returned constructor. It does not prove
   that arbitrary pending executions never deliver later, nor construct an
   execution-to-anchor interpretation.
6. Plain value bind does not establish the entire Rust ValueEntry callback,
   receipt, pattern/body behavior, retained-Computation entry, arbitrary old
   semantic worlds, general recursive L4, future Function registration or
   mutable State. The reference map and raw registration still require their
   original source correspondence.

The final source, note and producer receipt consistently maintain these
boundaries. The local world constructor is a usable checked result while the
parent original inference soundness goal remains open.

## Frozen handoff

All review evidence is under
`/workspace/scratch/f98087c7ac1a/parameter-semantics-review-r4/`: exact inputs,
authority copies, checker attempts, full independent origin/root inventories,
probe source/results, metadata diagnostics and a verified copy of the complete
author freeze. `evidence-summary.json` records exact reconciliation and census.

This receipt's own hash, the complete non-self-referential artifact manifest,
final dependency revalidation and the explicit zero-checker/zero-writer stop
are recorded separately in `final-freeze/`. After that stop, this revision is
immutable. No publish/integration permission is exercised by this reviewer.
