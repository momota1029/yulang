# Value-entry formal provenance through selected local use

Date: 2026-10-17  
Status: **Revision 2; source-correction delta pending review; experimental playground only**  
Author: `/root` (Luna primary)  
Sprint: `receive-role-indexed-inlet-introduction-20261017`, contract revision 1  
Contract SHA-256: `c2422818a92a6666ab9672b45d4d8bf1abf069116c82d4a91228374fc07e10cc`  
Revision 2 corrects the selected named-formal producer after independent
compiler review. Revision 1 remains preserved in commit `3b16bb603`.
Scope: selected `my apply f = { my step x = f x; step }` source path. This trace neither adopts a semantic rule nor closes an original theorem gate.

## Result

The selected source retains the true HIR identity of `step`'s formal `x`, and
the candidate inference path retains the formal registration, authentic
parameter-name call incidence, native call ports, and local-use structural
freshening data. The local fresh-use maps do not carry a `HirParameterId` or a
formal-origin/entry relation. More decisively for this experimental runtime,
`execute` throws away the returned candidate inference result and builds the
runtime program from HIR plus default name-consumption evidence. `from_hir`
then derives each Lambda's `ParameterRole` directly from the source formal's
effect annotation. No candidate-to-runtime transport of an inferred
formal/entry relation is present on this path.

This is a missing correspondence path in `tools/inference-playground`, not a
claim that the production compiler is unsound or that the runtime fails on the
example. The source Lambda for `step` has an ordinary unannotated formal, so
the runtime's native classification is `Value`; this does not establish that
the callable stored in `f` has semantic role `Pure`, or transfer an arbitrary
provider-indexed role proof for original c2.

## Field trace

| Stage | Retained fields / operation | Correspondence limit |
|---|---|---|
| Source identity and HIR | For selected named `my step x = ...`, `local_source.rs:1285-1312` allocates the parameter ID, calls `record_parameter` with the `IdentifierPattern` source identity, and records `local_parameter_owners[id] = step`'s `HirLocalId`. `:651-690` wraps that formal in the retained local Lambda and resolves its body names to `Parameter(id)`. `source_identity.rs:120-124` distinguishes source-pattern origin from the separate inline-Lambda identity plus binder-range origin. | Establishes the real named source formal identity and owner; the inline-Lambda branch is not the producer for this selected source. Neither origin classifies the value passed through it as Pure/Handler. |
| Candidate formal registration | `candidate_source.rs:594-609` emits a registration with owner, Lambda index, parameter ID, scope and a candidate entry role. Here `Value`/`Computation` follows the outer formal's computation annotation. `:617-625` maps a parameter Name to its registration endpoint. | The entry role belongs to this Lambda formal. It is not a semantic role for the callable `f`. |
| Apply and formal-name observation | `candidate_source.rs:646-657` emits `FormalNameInput` only when a Name resolves to `Parameter(id)`; local binding names follow Local/Link handling at `:961-974`. Apply stores the authentic source callee, argument, effect/result incidences and formal-name index at `:1023-1048`. `candidate_call::observe` (:437 onward) rechecks owner, occurrence, scope, Name(Parameter(id)), owning Lambda and native ports. | The original `f x` has an authentic formal-name route. The returned local `step` and its name are not promoted to a new formal. `candidate_call::observe` yields no formal when `formal_name` is absent. |
| Local capture and fresh use | `candidate_scheme.rs:1537-1575` captures the local scheme graph with its source-region frontier and prepares a `FreshUse`; `:1111-1135` begins fresh use and remaps owned scopes/regions. `RetainedFreshUseMaps` (:132-149) and `LocalFreshRoute` retain scope/relation/row/term/effect/bundle/context/evidence maps, local ID, slot, occurrence and graph. `commit_local_use` (:298-320) publishes those retained maps after ordinary constraints are admitted. | These are structural solver provenance and route records. No `HirParameterId`, owning Lambda identity, or relation to runtime `ParameterRole` occurs in the retained local route maps. A solver graph endpoint is not a source-formal proof by itself. |
| Runtime plan creation | `lib.rs:143-153` calls `prepare`, binds `(hir, _candidate)`, discards candidate inference and invokes `RuntimeProgram::from_hir(hir, RuntimeEvidence::default())`. `program.rs:176-180` takes HIR and runtime evidence. In `:382-395`, each source Lambda instruction keeps `parameter.id`; its `ParameterRole` is recomputed from whether the formal annotation has an effect row. Parameter-name consumption uses the runtime role registry and defaults non-parameter names to Observe (`:345-367`). | There is no import of candidate fresh-use/formal evidence into the plan. Runtime classification is source-annotation based. |
| Closure entry | `machine.rs:693-735` dispatches a Value closure through `Frame::ValueEntry`; a Computation closure follows the receiving/reification/receipt route. | Runtime Value/Computation entry is an execution protocol distinction, not the semantic Pure/Handler role required by the theorem. |

The source local binding also retains its own `HirLocalId`; candidate local
actions are addressed by local slot/id and use occurrence. A Local callee does
not become a formal-name route merely because it aliases a returned function.
The scoped candidate Apply experiment rejects Local callees (`candidate_source.rs:1000`),
which is a path limitation, not authority to exclude this source form from the
original theorem.

## First missing producer/correspondence

The first identity-bearing producer is present through HIR and candidate Call
observation for the original inner call `f x`. The selected local-return route
does not export a typed object relating the retained local-use graph and its
fresh-use remaps to the original HIR formal and its entry classification. The
runtime importer then receives neither that candidate object nor its relation:
`execute` discards it before plan construction.

Thus the missing seam is an explicit, validated candidate-to-runtime plan
transport (or a separate source theorem showing why no such transport is
needed), with source-root/Lambda/formal identity and role ownership preserved
through local capture, alias/use and runtime closure construction. Adding a
field alone would not prove authenticity, scope, alias correspondence,
completeness, or a Pure/Handler interpretation.

## Discriminating falsifier

For this exact source, a claimed bridge is falsified if it cannot identify the
same `HirParameterId` and owning Lambda at source registration and runtime
instruction, if a local alias is treated as a formal without a resolved
parameter identity, or if the Value/Computation entry bit is used as the
callable's Pure/Handler role. A future positive bridge must exhibit the actual
producer, serialized/imported fields, identity checks, and the runtime consumer
on this path. No such end-to-end evidence was found in the pinned bytes.

## Limits and next owners

- This is one selected playground source path, not arbitrary c2, source
  acceptance, runtime execution evidence, or a source counterexample.
- No tests, builds, probes, compiler execution, or expected-output changes were
  performed.
- `F2-SAT-INTRO-20261017`, `F2-RG-INTRO-20261017`, original A/B, F1/FK1,
  source T, anchored native MODEL, production/principality and cutover remain
  open. Candidate inlet/role formulas remain unselected.
- `NO_SAFE_CODE_SLICE`: at least three inspected owners agree on the boundary:
  `candidate_source` and `candidate_call` retain/check source incidence but do
  not construct the missing complete inlet; `candidate_scheme` retains
  structural fresh-use maps without formal identity transport; runtime
  `execute` discards CandidateInference and `from_hir` independently derives
  entry from annotation. A code-only patch would choose or assert missing
  semantics without a reviewed bridge.
- Next evidence owners: candidate local-route producer for any formal-origin
  export; playground plan exporter/importer and runtime Lambda consumer; the
  original source typing/action derivation owner for an independently valid
  T/Entry-Exec-Return plan. Any proposal changing runtime behavior returns for
  explicit semantic adoption.

## Frozen source pins

| File | SHA-256 |
|---|---|
| `crates/yu-solver/src/candidate_call.rs` | `cbad9cf51a05343eb7a29ab77aac520891467a8aa4edc3201ea3d91f978984a1` |
| `crates/yu-solver/src/candidate_source.rs` | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| `crates/yu-solver/src/candidate_scheme.rs` | `52b7281946de755003ee8f3b3d18cbc2df6cc6db5566b4e5ecf391b74a92640a` |
| `crates/yu-hir/src/source_identity.rs` | `aa97bc34be51644cf944b2813af47ad9243a8eb270850eeb6df34b9cddb3b3a2` |
| `crates/yu-hir/src/shadow.rs` | `2dffd7fd6542eed9fd3346e0672e76197c248be9c84334f341c4d612234b7ee9` |
| `crates/yu-hir/src/module/local_source.rs` | `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5` |
| `tools/inference-playground/src/lib.rs` | `b65cfd7200e459c9448438ec979ffeb9eddb35c282600349cebe7ddf3b759bbb` |
| `tools/inference-playground/src/runtime/program.rs` | `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748` |
| `tools/inference-playground/src/runtime/machine.rs` | `b8f15e4617a9d66940183c7327499ff8a2beb1e9cae2abb997137fc1ca464b82` |
| Candidate rule artifact (unselected) | `7716a71d6bf6f5212bd455e1a3959569748e558238d0a164649ec1c57d92b72c` |

This trace is frozen for independent review. No reviewer has run yet; parent
gates remain open.
