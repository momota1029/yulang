# R243: original literal source readout, structural trace

Status: frozen research-only source evidence, revision 1; independent review pending.
Author: `/root/sol_r243_source_readout`, requested Sol/high; observed model/effort UNKNOWN.
Baseline: `cddf5d23fe73f78c49f579b30ecc6e6a8287f8f2`, supplied by Luna's read-only HEAD receipt.
Contract: `tasks/agent-loop/sprints/original-literal-source-readout-r243.md`, SHA-256 `58995da0b2880560bf63be81b8d59c07c516e6dd162d6624b7f0d1a74d98674e`.

## Objective, authority and claim class

Trace the concrete source occurrence and literal data through the two pinned owners, their directly called functions and existing result consumers. This is a bounded static source audit. It makes no execution, Rust correctness, Lean verification, independent-review or original-parent closure claim. The unchanged parent is `SourceProblem.InferenceSoundness`, `notes/theory/lean/YulangClosure/Contracts.lean:128–130`; parent delta is zero. The accepted L1/canonical-generation meaning and all eight literal forms remain fixed.

Governing contract sections: R243 “Fixed outcome and method”, “Sol assignment and exact leases”, and “Review and resources”. The trace follows the evidence distinctions in `rules/research-lab.pre-sprint.md` (“One semantic baseline” and “Evidence quality”), the no-new-meaning approval boundary in `rules/design-authority.md`, and the freeze/disjoint-lease rules in `rules/git-concurrency.md`. The authoritative inference principles, sections 1 and 1.1, do not make literal evaluation a prerequisite of constraint generation. No source restriction or semantic interpretation is proposed here.

**Result:** the inspected literal constraint branch forgets the payload in its emitted terms, while retaining the authentic source occurrence. Original HIR is also retained in the frozen result, so global payload destruction does not follow. However, the inspected result consumers do not join that retained payload/occurrence to an original semantic assignment row. Four of the eight payload kinds already have a representation gap at `LocalSourceForm`. These are distinct obstructions.

## Frozen dependencies

SHA-256 hashes were read before relying on either pinned owner and rechecked before freeze. The two R241/R242 artifact hashes also match the contract.

| Dependency | SHA-256 |
|---|---|
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `crates/yu-solver/src/candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `notes/theory/lean/YulangClosure/OriginalLiteralCarrierRealizationR241.lean` | `49bbe56ee5525f1a7a5b3db2d5c2b04737468cdaa864c761fd6465e1af914d8a` |
| `notes/theory/lean/YulangClosure/OriginalLiteralInputDependenceR242.lean` | `b5a5ac8580d71ee15dd595fd2712316451df28a68398a524d558f72a12cee649` |
| Direct calls/result consumer: `crates/yu-solver/src/lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| Direct calls/result consumer: `crates/yu-solver/src/shadow_apply.rs` | `99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5` |
| Direct source-carrier lookup: `crates/yu-hir/src/module.rs` | `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646` |

The three supplementary files were inspected only for the direct calls and consumers named below. No dependency was modified. No quarantined runtime path was read or written.

## Occurrence-to-fact-to-consumer map

In the following table, `o` is an authentic `HirOccurrenceId`, `r` its `SourceRootId`, `i` its owner-local expression index, and `p=(v,e)` the component positions. These implementation coordinates are not identified with original semantic `Site`, `Root`, `Event`, `Scope` or `JointWitness`.

| Stage and exact locator | Coordinate/index and carried data | Next consumer |
|---|---|---|
| HIR `Builder::set_at_range`, `local_source.rs:1520–1549`; `LocalSourceExpr`, `:313–323` | Stores `o`, parse-owned `source`, `range`, lexical `scope`, and `form` together at `expressions[index.ordinal]`; index includes owner (`:49–61`). | HIR `LocalSource::order_occurrences`, `:131–162`, publishes occurrence IDs in source-node order and records `o -> source`. A source key may own multiple generated occurrences; equality of source keys alone is insufficient. |
| `LocalSource::expression`, `:174–178`, and `expressions`, `:180–182` | Owner-checked index lookup, or borrowed expression slice with payload/spelling and `o`. | `ConstraintBatch::emit_candidate_source`, `candidate_source.rs:1043–1073`. |
| `emit_candidate_source`, `:1052–1069` | Checks that `source` is pointer-identical to `hir.local_source_for(r)`, checks parent/root match and occurrence ownership; inserts `o -> hir_index` and `o -> r`. | `candidate_component(o)` for each expression, `:1098–1099`. |
| `ConstraintBatch::candidate_component`, `shadow_apply.rs:3873–3888`; source endpoint planning, `candidate_source.rs:1131–1142` | Records `occurrence_component_positions[o]=p`; literal endpoint is `CandidateEndpoint::Component(v)`. No payload is added to this endpoint. | `Work::Visit`/`Work::Finish`, `candidate_source.rs:1208–1212`, `:1586–1606`. |
| Literal `Work::Finish`, `:1587–1606` | Uses `o`, `p`; forms type/effect terms described below. With `k=self.occurrences.len()` at `:1590`, the four explicit literal emits occupy `k..k+4`, local slots `0,1,2,3`. Payload fields are matched with `_`. | `ConstraintBatch::emit`, `lib.rs:2185–2201`, appends `ConstraintOccurrence {id=(o,slot), lower, upper, cause}`. |
| `append_source_facts`, `candidate_source.rs:2143`, `:2262–2264` | Appends `Action::Fact(j)` for newly emitted occurrence-vector positions `j`. This `j` is not a `FactId`, HIR ordinal or payload index. | Root/expression/member action schedules (`:2148–2256`); `execute_candidate_action`, `:2468–2481`. |
| `InferenceSession::admit_collected_fact`, `lib.rs:11546–11590` | Reads `batch.occurrences[j]`; transaction admits its terms and cause, records provenance; sends value pairs to `constrain_live_value` or effect endpoints to `constrain_live_effect`. | `ConstraintTransaction::admit`, `lib.rs:4007–4056`, and `ConstraintStore::record_provenance`, `:3797–3809`. |
| Store admission/provenance, `lib.rs:3338–3404`, `:4007–4056` | Canonical key is the term pair. `SemanticFact` has `FactId`, `lower`, `upper`; provenance has `CauseId` and `FactId`; cause still contains `(o,slot)`. Duplicate admission can reuse a fact, so a fact index alone is not an occurrence or payload witness. | Frozen result's store and source-occurrence observation. |
| `InferenceSession::finish_observations`, `lib.rs:20075–20146`, `:20326–20349` | For occurrences in `batch.projection_order`, `SolvedProjection` contains `SolvedValue` classification plus `SolvedEffect`; original `hirs`, occurrence-to-HIR positions and store are moved into `FrozenInferenceData`. `SolvedValue` is `Int/Unit/Bool/Str/Unknown/Never`, `:4159–4183`. | `finish_candidate`, `:10746–10756`, wraps this frozen data in `CandidateSolvedResult`; `CandidateInference` owns it (`shadow_apply.rs:508–510`). |
| `CandidateInference::source_occurrence_observation`, `shadow_apply.rs:2251–2294` | Requires an owned occurrence and no recorded errors; joins provenance causes to matching facts, retains `o`, cause, fact and optional origin records; each collection is capped at `min(max_rows,256)` with completeness flags. | Returns an observation, not an original assignment row or a payload readout. |

The four explicit branch constraints are `K+ <: v`, `v <: K-`, `EffectBottom+ <: e`, and `e <: EmptyEffect-`, where `K` is Unit, Bool, Int or Str. This describes source code construction, not a verified solver outcome. `candidate_component` can also emit earlier pure-effect facts when graph effects are disabled (`shadow_apply.rs:3885–3900`); the table's `k..k+4` labels only the four literal-branch emits, not every fact associated with `o`.

## Eight-payload coverage

Each covered form uses the same `o/i/r/p -> (o,slot) -> Action::Fact(j) -> provenance -> occurrence observation` chain above. The “constraint/readout” column records only what the inspected branches construct or classify.

| Original payload kind | HIR construction and retained data | Constraint/readout, and first coverage boundary |
|---|---|---|
| unit | Empty `ParenthesizedExpression` children select `LocalSourceForm::Unit`, `local_source.rs:2182–2211`; occurrence/source/range/scope remain in `LocalSourceExpr`. | Unit leaves; projection class Unit under its bounds test. No original semantic row constructor in the inspected consumer. |
| bool | Unshadowed identifier spelling `true`/`false` selects `Boolean(bool)`, `:2124–2134`; the lexical guard is part of this branch, not a new source-domain restriction. | Bool leaves; `_` ignores the bit. HIR retains it; projection class Bool cannot distinguish it. |
| int | `Integer(integer_spelling(node))`, `:2164–2170`; `integer_spelling`, `:676–682`, retains the single integer token's text. | Int leaves; `_` ignores spelling. A source lookup can recover that spelling. The inspected chain does not decode it to the original integer payload or construct its original semantic row. |
| floatBits | No float/bits payload variant in the complete `LocalSourceForm` enum, `:348–440`, and no corresponding literal arm in `Builder::expression` (`:1881–2278`). | First representation gap: HIR `LocalSourceForm` / `Builder::expression`; no eight-form native path can be read from this owner. This leaves the original floatBits case open. |
| string | Noninterpolated literal selects `String(string_spelling(node))`, `:2171–2176`; `string_literal_source`, `:699–715`, retains text between and including delimiter coordinates. `DecodedString` is a distinct generated-text variant (`:357–358`). | Str leaves; `_` ignores text. Retained delimited source spelling is not by itself a proved decoded original string. Interpolation retains its separate plan/lowered occurrences; it is not silently reclassified as a raw string leaf. |
| bytes | No byte-array payload variant or literal arm in the same complete enum/expression owner. | First representation gap: `LocalSourceForm` / `Builder::expression`; original bytes case remains in the theorem. No coercion from String is justified. |
| path | No path-literal payload variant or literal arm in that owner. Its `PathTail` handling is not an original path-payload constructor. | First representation gap: `LocalSourceForm` / `Builder::expression`; original path case remains open. |
| character | No character payload variant or literal arm in that owner. | First representation gap: `LocalSourceForm` / `Builder::expression`; original character case remains open. No coercion from int/string is justified. |

The default unsupported branch is `local_source.rs:2278`; formation records `SourceCarrierOutcome::Unsupported` (`:1073–1076`). This is a representation-coverage observation at the assigned owner, not evidence that any of these original source forms is inadmissible Yulang. The parser, another lowering path or a runtime implementation is outside this audit.

## Recoverable provenance versus the missing original edge

There is a concrete source-side lookup composition for an already retained source and known owner/index: `hir.local_source_for(r)?.expression(i)`, or a search of `source.expressions()` for equality with the exact branded `o`. `HirModule::local_source_for`, `module.rs:2022–2029`, reads the original source carrier; `source_carrier_for`, `:1974–1979`, validates its root. `occurrence_source_key`, `:2063–2067`, reads the stored occurrence/source-node map. These recover HIR data without attempting to invert a type constraint.

That information survives finishing: `FrozenInferenceData::hir_for_occurrence`, `lib.rs:7836–7842`, selects a retained HIR and checks its occurrence brand. An existing Call-specific consumer even reopens a retained source with its known owner (`CandidateInference::source_operation_apply_effect_joins`, `shadow_apply.rs:2103–2113`). Thus it would be incorrect to conclude that `Integer(_)` or `Boolean(_)` destroys all source payload information.

The inspected literal result path, however, performs **no join from `(retained HIR, owner, occurrence, payload/spelling, solved facts)` into `SourceAssignment.row site`**. The exact boundary is `finish_observations`' `SolvedProjection {value,effect}` at `lib.rs:20146`, and the source-aware consumer's `CandidateSourceFactRecord {occurrence,cause,fact}` at `shadow_apply.rs:2273` / return at `:2294`. Neither constructs the original row's descriptor, value, root and event or supplies the relation from implementation occurrence to original `site`. The source-owner map used during planning is not itself such a row. This is a bounded absence in the inspected constructor/consumer chain, not a repository-wide nonexistence theorem or permission to add an API.

R241's actual folded consumer (`OriginalLiteralCarrierRealizationR241.lean:57`) still requires a decoded state under the complete stored prefix and all three facts:

```text
declarations literal (state.assignment.row site)
inputs.valueForm (state.assignment.descriptor <site, finalRoot>) = ground
inputs.ground (state.assignment.row site)
```

Recovered spelling, a type leaf, or empty effect bounds establishes none of those original relations. R242's input-dependence diagnostic (`OriginalLiteralInputDependenceR242.lean:84`, `:128`, `:138`) is not repaired by retaining HIR: the generator/decoder independence and separate ground premise remain explicit. Its Return consumer at `:160` additionally exposes original event/world/guard/value/field premises. No event, current-world, fiber, eta0, scope or joint witness is reconstructed here.

Written annotation handling remains a separate action (`candidate_source.rs:2151–2203`); definition-root linking is a separate `Action::Link` (`:2205–2208`), while expression and member schedules retain their own components (`:2216–2256`). None of these implementation ports is identified with original synthesis, written-target or final-root ports. Literal `EmptyEffect-` bounds are not substituted for the original contextual effect judgment, frame prefix or readout event.

## Discriminating derivation and evidence limits

Let `E(o,p,b)` denote only the four literal-branch records constructed from `LocalSourceForm::Boolean(b)`, with occurrence, component positions and term arena fixed. Inspection of `candidate_source.rs:1592–1606` gives `E(o,p,true)=E(o,p,false)`: the branch reads no `b` and selects the same leaves/slots/terms. Any decoder whose *only* input is this projection must return the same answer for both branch inputs; it cannot recover both distinct boolean payloads. The HIR side lookup is an additional input and is outside that erasure argument.

This is a minimal symbolic branch comparison, not two authenticated executions, a source-qualified Yulang counterexample or a Lean theorem. Holding branded coordinates fixed across hypothetical payload substitution is an explicit analysis hypothesis; it is not a claim that two different parsed files share HIR identity. No mutation was executed. The same syntactic argument applies to differing integer/string spellings; unit has no two-payload witness. It does not establish anything about the four unrepresented payload kinds.

Oracle independence: the evidence is the actual pinned source fields and calls, independently of any toy checker transition assumptions. It shares the repository's unverified construction code and the exact R241/R242 proposition statements; no semantic oracle, solver run or theorem checker was invoked. Searches were bounded to the two owners and named direct-call/result-consumer files. Large initial reads were output-truncated; all locators used above were subsequently inspected in focused ranges. No repository-wide negative claim relies on a truncated read.

Checks: `sha256sum` on the seven dependencies and contract; `rg -n` symbol searches and `nl -ba`/`sed` focused reads. No builds/tests, Cargo, cache/scratch outputs, compiler edits, Git calls, network calls or descendants. No seeds, enumerated input ranges or experimental mutations apply. One lightweight read command ran at a time. CPU/RAM peaks and exact active wall time were not instrumented; the assignment envelope is 1,200 active seconds, zero heavy processes. Exact wall-time consumption needs the primary's runtime receipt; no numerical resource benchmark is claimed. Projection coverage outside the explicitly iterated `projection_order` was not established.

Failure conditions: dependency mismatch; a missed direct literal consumer with an actual original-row constructor; an alternative payload-carrying field in this exact owner; or an unexamined decoding rule establishing the required original relations would invalidate the corresponding absence claim. Merely showing another type/effect constraint or source key does not falsify the identified missing original-row join.

Recommended next action: Luna should obtain the planned fresh `compiler_referee` review of these frozen bytes, then allocate an exact original carrier/readout bridge packet from the unchanged parent and the identified construction boundary. The four representation gaps remain coverage obligations; no Rust correction or semantic choice is authorized by this note.

STOPPED-writing receipt: revision 1 is final for this assignment; after writing the paired handoff and computing freeze hashes, this worker performs no further writes. No descendants, generated outputs or unresolved child leases exist. Review and all shared-record/Git changes remain Luna-owned.
