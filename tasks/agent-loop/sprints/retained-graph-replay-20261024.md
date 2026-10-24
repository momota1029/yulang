# Retained source graph, SCC extraction and replay attribution

RETAINED-GRAPH-REPLAY-20261024/r1. Baseline `14860b9ba4792c74bfb4d8610cc3ff10b5d0578f`. Worktree `/home/momota1029/rust/yulang-semantics-proof-20261024`, branch `research/semantics-proof-20261024`.

## User steering and original objective

> そこはグラフを持ってきてSCCとりだすしかないですよ

Use the retained actual graph and extract SCCs. This is a proof-method correction within the selected immutable birth-level induced Value-SCC rule. It neither changes the graph domain to type bounds nor authorizes an invented association rule. Preserve original source/Call/effect/type/event scopes, actual extrusion pairs, generalization/use independence and original Simple-sub A/B. Implementation and tests excluded; Astra-only children.

The exact source is the previous replay example:

```text
let top = lambda h.
  let rec f = lambda x. (lambda z.{a=x})(h(f x))
  in {a=succ((f 0).a), b=(f true).a}
in top
```

Previous frozen evidence supplies the complete scalar history, actual positive (T1,B2) copy and publication maps. This method brings the full semantic Value graph and pair/comparison/output provenance records to that same history; it does not restate support-union as ownership or stop at a generic BR-ATTR label.

## Exact outcomes and leases

- `/root/astra_corrected_machine`: sole write path `notes/theory/2026-10-24-retained-value-graph-replay-attribution.md`. Three stages: enumerate actual semantic vertices/edges/birth and separate helpers; compute induced SCCs with complete adjacency/component and qualification tables; join actual pair/comparison/output/reuse provenance to components, deriving a verdict or a concrete representation insufficiency witness. Inspect whether a late copy's low target carries the original boundary association through its graph path, rather than assigning all ancestor support to the copy. Derive that from retained constructors; no new boundary-ownership convention. Do not infer semantic birth from arbitrary current row level.
- `/root`: `notes/theory/2026-10-24-retained-graph-publication-consequence.md`, `docs/yulang-whole-proof-closure-ja.md`, `docs/yulang-proof-index-ja.md`, this contract, `tasks/agent-loop/sprints/retained-graph-replay-20261024-outcome.md`, `tasks/agent-loop/current.json`. Consume graph result into prior PR1–PR3 and original parent. Independently characterize exactly what source graph/provenance information determines, with an explicit mathematical relation if needed, without selecting new semantics.
- `/root/astra_semantics_direction`: read-only30s decision completed, STOP/no descendants. Explicit graph/provenance method selected.
- `/root/astra_semantics_review`: read-only80s independent frozen review of the two new notes and guide delta; recompute components, check real retained records and original authority; supply end-boundary direction.

You are not alone. All old frozen paths remain immutable. Original checkout/unknown external writers remain quarantined. No other writes/reverts, tests/build/probes/compiler execution, implementation/manifests, scratch, worker Git/network or descendants. Protected question bundle excluded. One primary Git integrator.

## Success and falsifiers

A result must apply graph extraction to the disputed concrete pair. A missing/invented Value edge, wrong birth, helper-created cross-level path, wrapper/result alias to F, invented pair association or promotion of reference acceptance to full source acceptance falsifies the relevant claim. Carry the graph and original association handles; the provenance DAG is not an additional Value-reference graph. If the implementation lacks a decisive relation, exhibit the actual retained fields and exact missing query, not merely an unproved general preservation slogan. Do not treat that as authority to choose ownership or silently narrow the source domain. Whole proof closure requires original scope and independently established premises.

## Resources, review and stop

Prior4590s + current300s (direction30+producer190+review80) =4890s charged. This renewed envelope follows explicit user correction and the changed full-graph method; no per-lemma reset, automatic renewal or unobserved refund. Maximum one Astra child concurrently; requested Astra/medium, observed model/effort/duration UNKNOWN. Three producer stages, one frozen handoff, independent review then bounded primary repair. Stop all writers with actual receipts before final Git/report. No background work.

## Frozen inputs

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-24-birth-level-scc-intrusion.md` | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |
| `notes/theory/2026-10-24-birth-level-scc-intrusion.md` | `67c2a44b7a4009a96424dc329ed4385fffdbc6d6661bf4155408cfbd62de3bfa` |
| `notes/design/2026-10-12-intrusion-value-type-association.md` | `531a9efae0ab7e03bfbd2f41cd7da86078e2fc8e67675d2c5c941972409f4e89` |
| `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/progress/2026-10-14-value-occurrence-intrusion-implementation.md` | `35dca7a9033a52d46367229c0119887b944bc6c0f37a560de74f33da4653c0e5` |
| `crates/yu-solver/src/candidate_context.rs` | `33af2efb6ed782e4f143cccff03c62087e6ba8d0fbe90415846537fc2a08cec5` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_source.rs` | `57b119592a6a8d4afd42aca10c5e2bb749cfdf0fb0fdea967dd437d552a1a04e` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/candidate_value_graph.rs` | `5893555fe89c594feabca200d1d8f26631877200da61e6ae39c80d375f748bb1` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `/home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala` | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| `/home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/syntax.scala` | `f26f19f6905d42c247198c45da9b1675b22619dd59749047023efe5f7ee3c60f` |
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b` |
| `notes/design/2026-10-12-value-reference-copied-row-ownership.md` | `7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd` |
| `notes/theory/2026-10-24-birth-level-replay-intrusion.md` | `7bc8ccee1ee9c0a2ce168e5f1687ae76e7794b097cb3d35dc85ccb5d4f717c5b` |
| `notes/theory/2026-10-24-birth-level-publication-replay.md` | `0e84e618a077b6f3d138707349fbfe51d09e8ccdd54628ad772640f6c12ea244` |
