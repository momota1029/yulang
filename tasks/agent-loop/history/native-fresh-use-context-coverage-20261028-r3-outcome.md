# Outcome — NATIVE-FRESH-USE-CONTEXT-COVERAGE/r3

Status: **CLOSED_INCOMPLETE**. Luna adjudication after fresh independent review and sprint-end dispatcher consultation.

## Scope and decision

r3 investigated whether existing `State.retained_input` / `CircuitEvidence` borrowed readback can establish Context map-domain and target/child/weight coverage at completed FreshUse consumers. It did not establish the full gate and did not refute feasibility. Rust acceptance is **REJECTED**. The Lean artifact is retained as **unchecked partial research**, with zero kernel checks and zero axiom audits.

The original `SourceProblem.InferenceSoundness` quantifiers and shared witness are unchanged. Context coverage, full FreshUse validation, returned-root, source/native correspondence, effect hygiene, principality, termination, parent theorem and production remain **OPEN**. `H_u` remains **AUTHORITY_BLOCKED**. No approved semantic or API change occurred.

## Admitted contracts and source pins

- Base contract `tasks/agent-loop/sprints/native-fresh-use-context-coverage-20261028-r3.md`, SHA-256 `d6fc97fde87e8c8a0c0eb0cb8afb140029a0428aedcde6f82b1f162c4bc21725`.
- Amendment 01 `tasks/agent-loop/sprints/native-fresh-use-context-coverage-20261028-r3-amendment-01.md`, SHA-256 `dc7389b53d773c4c742af556f4b6d5123821df84bdddb7df97afd7a0ac549fc4`; it admitted only read-only `crates/yu-solver/src/candidate_extrusion.rs` at SHA-256 `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`.
- The clean r3 archive used baseline `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d` with only the three admitted Rust overlays. All 18 contract dependency pins matched before admission.

## Frozen outputs

| Artifact | SHA-256 | Disposition |
|---|---|---|
| Rust `candidate_scheme.rs` | `9279fcb9bd1580655b7db4541c27338cc3a48ac711f06197cd3ee250b5315923` | REJECTED for acceptance |
| Rust handoff | `23c3b76c95562b838c45f76470483c364cf6e77ba36d8e9de02de1411973ffd5` | Frozen |
| `NativeFreshUseContextCoverageR3.lean` | `735c0711151c4605d40b338792327f30af80e9740cce346b65517df722543d46` | 16 unchecked declarations; partial research only |
| Proof handoff | `71d47a6b05871cf4cb676da08eae388b562c33bd7075a97cbf81ad11427625ef` | Frozen |
| Independent review | `2bdb5816a94d62fe8cda53fcb84a0e98688c4ea21f53940dfa48a04e56d3b3b6` | Captured by Luna from read-only reviewer report |

## Independent review findings

The fresh reviewer rejected Rust acceptance for four instrument defects or missing behaviors:

1. Logical identity `ContextId(0)` is inserted into the required stored observation set even though authentic `CircuitEvidence.contexts()` emits only IDs starting at 1. A mapped DAG reaching identity therefore fails; the synthetic fixture hides this by fabricating observed zero.
2. The empty-domain positive test starts with `completed_bound_readback = false` but asserts the coverage predicate is true. This is a deterministic static contradiction; no test was run.
3. The predicate never reads `source_roots`, and the purported source-root mutation changes `source_contexts` too. Mutation evidence uses copied synthetic sets, not unchanged authentic construction/readback evidence, and contains no restored/discharged-parent specimen.
4. Pre-bound suspension returns ordinary `Ok(())`; there is no explicit `Partial/Unavailable` coverage result.

The reviewer found that `completed_exact_domain` is a valid abstract transition theorem whose hypothesis does not restate domain equality, and `attached_target_observed` establishes observation for an attached child. Neither connects successful native execution to every prepared map image or proves weight completeness. The local discharge witness is not a reachable successful restoration trace. The added restoration driver reads establish neither stability nor a successful counterexample. No impossibility result follows.

Review identity `/root/native_fresh_use_context_coverage_review_r3`, requested Sol/high, observed runtime model/effort UNKNOWN. It completed within the original 600s grant, with no writes, Git, descendants, Cargo/tests/build, Lean/Lake or checker execution. Luna recorded the report because the reviewer role prohibited writing. Full report is the frozen review artifact linked above.

## Resource and execution receipt

- Rust allocation: finite 500s cap charged; source and handoff frozen without escalation.
- Proof: `<900s` of the original 1,000s cap reported used, with at least 100s unspent. No carryover.
- Reviewer: within the original 600s grant. No renewal.
- Primary: used only for admission, pins, review capture and compact state/outcome closeout.
- Zero Cargo, Rust tests/build, Lean/Lake, axiom audits or compiler checks. No executable artifacts or scratch directories were created. `python3 tools/agent_sprint.py check` passed for admitted/closed compact state; this is static protocol evidence only.
- No Git staging, commit or push occurred. No unrelated dirty or quarantined path was changed.

## Next bounded direction

Dispatcher recommends r4, subject to a fresh Luna-authored contract and admission: repair the identity/readback, completed-empty, independent source-root mutation and explicit pre-bound unavailable defects, then connect successful native rename execution to the exact-domain/closure projection and prove sufficient target/weight observation across actual restoration—or produce the exact reachable successful counterexample. Reuse r3's valid conditional arguments. Do not repeat a disconnected abstract projection. Candidate owners are the already admitted scheme, Context and read-only restoration source; no new API authority is implied. Proposed resources are a fresh 2,600s envelope (implementation 800s, proof 800s, review 600s, primary 300s, contingency 100s), zero Astra, unchanged check caps. This is a proposal only; Luna must write/admit r4 and reconcile live capacity before starting it.
