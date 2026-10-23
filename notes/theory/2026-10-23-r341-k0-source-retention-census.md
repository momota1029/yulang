# R341 K0 source-constraint retention census

Status: frozen primary source census; not an independent proof or a compiler
defect finding. This note supports the S0 bridge in the user audit and leaves
the parent theorem open.

## Authority and exact inputs

- Branch: `research/simple-sub-intrusion`
- Inspected baseline: `d6610bb03cd1f9037df834982722e0022fc79209` (matches upstream)
- User audit: `docs/Yulang Simple-sub 拡張：全体証明への移行監査・証明設計.md`,
  SHA-256 `b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`
- R336 reviewed source-typing construction: `notes/theory/2026-10-23-r336-k0-d0-d1-rev4.md`,
  SHA-256 `4bcbe71ec9f2372baca884e3db737c16fc19ad2a51103965ade5ca4c2ecf4973`
- R337 context preservation: `notes/theory/2026-10-23-r337-k0-context-preservation.md`,
  SHA-256 `e14b8125a505c3001021396b8c6e949e3b0a58f61ecf2785f915dbdde65dfc62`
- R337 source census: `notes/theory/2026-10-23-r337-k0-context-source-census.md`,
  SHA-256 `771c3c8ab2a69336579c78a7583097b8d1839bf0d6fe97f2e69da27e77500e6a`
- R338 source census rev1 snapshot: `tasks/agent-loop/review-inputs/r339-r338-census-rev1.md`,
  SHA-256 `1361b0223e8950c3e6546f1cbcb9cd25bd7a0ca038511f7c55cad29d3659fa6d`
- R338 current census rev2: `notes/theory/2026-10-23-r338-k0-state-source-census.md`,
  SHA-256 `56174af37c13d2e6ac846b84c3fd71075bceefb8b05474c1f8b3d6d5b2c50ac9`
- R338 D1/D2 proof: `notes/theory/2026-10-23-r338-k0-d1-d2-state-bridge.md`,
  SHA-256 `f438939f99c212324a397f527d46d4a4ab565733e4b2e9e2ae55254e96ca9bf0`
- R339 replay-retirement candidate: `notes/theory/2026-10-23-r339-k0-obligation-retirement.md`,
  SHA-256 `8797013ab5ea77655629fce45031fb28e1c5557979c1f213b9268abd31080c87`
- R340 continuation proof: `notes/theory/2026-10-23-r340-k0-apply-continuation.md`,
  SHA-256 `7ae75ef26d6bfa441989e9655dda89fbed2927d0061f5d8445246d587a0d7737`
- R340 census full file: SHA-256 `de3902d834a68f0d4f5b269f4bddac7d900d44bfe8dc118b05b451372cf24078`;
  its immutable rev1 prefix is 16,711 bytes, SHA-256
  `5b9fd45dc51a902c96a23586b4965a674b8429554340d8c3d01d4410746ecf5f`.

Production source pins at the inspected baseline:

| Owner | SHA-256 | R341 responsibility |
| --- | --- | --- |
| `crates/yu-solver/src/candidate_source.rs` | `0dc798e48e70505093e52b31b2569e3b2d8ff1dee663095176aaf547ccb3289b` | Authentic K0 components, constructor inequalities, `Action::Fact`, `Action::Link`, source occurrence ownership |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` | Fact/link admission, typed drain, worklist dispatch, pair memo/completion |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` | Canonical owner selection, physical bound append/readback, opposite-bound replay |
| `crates/yu-solver/src/candidate_context.rs` | `33af2efb6ed782e4f143cccff03c62087e6ba8d0fbe90415846537fc2a08cec5` | Initial/current/replay-child retention and acknowledgement |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` | Generation updates, cache invalidation/reopen, possible row merge owner |
| `crates/yu-solver/src/candidate_effect.rs` | `d156fdbf0300387a5aa036053a2cc7eeb6312a803aaf38838e30dd2731ca4945` | Directed logical bound interpretation and relation keys |

The sprint contract retains the full source hash manifest; all six hashes were
rechecked at R341 preparation.

## Parent claim and bounded R341 question

The unchanged parent is audit §6 S0:

```text
ValidK0(s) ∧ NativeComplete₀(s,S) ∧ ρ ⊨ H(S) ∧ Reifiable₀(ρ)
  ⇒ ∅ ⊢₀ s : ρ(v_s) ! ρ(ε_s).
```

S0 is source typing from an independent graph solution. Runtime preservation
and progress require the separate M composition and are not premises of this
source-typing implication. R341 investigates the missing G-to-final-H bridge:
does every inequality of the authentic source family `C_s`, including the
Definition-root Value link, hold under a solution of the final `H(S)`?

For a duplicate or fresh successful source admission of `q`, use
`H_after = H_before ∪ {q}`. A duplicate store receipt does not prove
`H_before ⊨ q`. Any argument that compares the two solution sets as equal must
provide an independent entailment proof. The same constraint must remain in
the logical theory while it is pending, current, or held by a replay/frame; a
queue pop or `ConstraintStore` identity is not its retirement proof.

The target proof must define the row transport explicitly: map the fixed K0
source-component/formal/invocation/root rows into the final live assignment by
the authentic kind-preserving representative map, then restrict to the support
of `C_s`. If a source endpoint contains a non-source auxiliary row, account for
its image instead of silently dropping it. R336 D1 may be applied only after
the proof establishes `ρ ⊨ H(C_s)` and preserves its explicit
`Reifiable₀(ρ)` premise.

## Constructor and owner inventory

R336 rev4 records the independent typing rules and the constructor table. The
source audit for R341 checked the corresponding current owners directly:

| K0 source form / bridge | Emission or endpoint | Admission and final-state owners | Open question for the proof |
| --- | --- | --- | --- |
| Literal | Four directed Value/Effect inequalities are emitted for the result rows (`candidate_source.rs:1558–1573`). | `Action::Fact` → `admit_collected_fact` → `constrain_live_value/effect` (`candidate_source.rs:2404–2432`; `lib.rs:11481–11524,13950–14005`). | Does each admitted inequality persist as a bound or surviving entailment through final work retirement? |
| Parameter Name | The Value endpoint aliases the authentic enclosing Lambda formal; the Name evaluation effect is pure (`candidate_source.rs:1131–1137,1724–1741`). | Any generated pure-effect facts follow the same admission route; binder/formal ownership is registered in source construction. | Confirm every Name occurrence maps to that same formal row; do not treat its unused collector component as the Name type. |
| Value Lambda | Lambda recipe admits the positive Function constructor and its four ports; entry/body Effects are bounded by the return Effect (`lib.rs:11557–11620,11684–11700`). | Recipe/fact admissions enter the same candidate typed work machinery; effect row owner/readback is in `candidate_extrusion.rs`. | Is the whole Function relation and each port inequality in final H, with correct polarity and shared row identity? |
| Apply | Negative Function demand contains the argument Value/Effect, fresh invocation Effect, and result Value; callee/invocation Effects flow to Apply Effect (`shadow_apply.rs:4085–4158,4207–4224`). | Candidate recipe admissions and later typed drain/dispatch; `lib.rs` and `candidate_context.rs`. | The demand is a source obligation; pair memo completion must not be used as a substitute for its logical witness. |
| If | Conditions are constrained by Bool; each branch Value and each child Effect flows to the result rows (`candidate_source.rs:1632–1655`). | Direct `Action::ValueConstraint` and fact emissions share typed admission and owner-bound recording. | Account for each condition, both branches, and each distinct occurrence/slot; no constant-condition branch may be omitted. |
| Group | Its child's Value/Effect flow to the Group result (`candidate_source.rs:2038–2050`). | Emitted facts plus ordinary candidate bounds. | Keep the exact child/result row map and both sorts. |
| Binding-free Block / StatementBlock | Final expression Value/Effect flow to result; each prefix Effect flows to the block Effect (`candidate_source.rs:2050–2101`). | Emitted facts plus ordinary candidate bounds. | Preserve prefix order/value discard semantics and every prefix-effect inequality. |
| Definition-root output | Authentic `Action::Link` records body Value ≤ `DefinitionValue` root; no root Effect row (`candidate_source.rs:2146–2165,2428–2432`). | `admit_candidate_value_link` starts a typed drain; subsequent bound insertion/replay is in `lib.rs` and `candidate_extrusion.rs`. | This is the first decisive case: prove the body-to-root inequality survives final H; do not replace it with equality or type the body at the root without this Link. |

The K0 source family excludes nonrecursive local bindings, recursive roots,
modules/imports, annotations, Comp, operations/handlers, Variant/Case,
Tuple/record adaptation, roles/members/operators/interpolation and scoped
experiments. These exclusions are only the audit's staged proof domain; they do
not change the original product goal or Simple-sub A/B obligations.

## Native state owners inspected

1. `lib.rs:11481–11524`: each successful `ConstraintStore` receipt records
   provenance, polarizes the endpoints by kind and calls the live typed
   constraint path. Fresh versus duplicate changes store admission, not the
   logical statement of the incoming `q`.
2. `lib.rs:14186–14245,14289–14366`: a candidate drain retains the initial
   request, queues it, transfers popped work into a current frame and proceeds
   through transport/context/dispatch. The bounded source obligation cannot be
   declared gone merely because it leaves the queue.
3. `lib.rs:14432–14463,15295–15376`: dispatch consults `pair_is_current`;
   `record_typed_pair_admission` calls `mark_candidate_pair` before publishing
   the typed-pair memo. `pair_is_current` combines a memo hit with a current
   relation's `completed[generation]`. This marker is a scheduling/cache fact,
   not, by its name alone, evidence that a source inequality is entailed. The
   exact relation owner and the pre/post logical H must be proved.
4. `candidate_extrusion.rs:635–875`: bound insertion canonicalizes both
   endpoints, selects one exact owner lane, appends the incidence, reads the
   complete directed `BoundKey` back from that physical slot, and rejects a
   mismatch. The logical interpretation is owned by
   `candidate_context.rs:3311–3321` and treats positive/negative owner bounds
   with opposite directions.
5. `candidate_extrusion.rs:878–938,1070–1112`: replay enumerates opposite
   bounds and creates each pair consequence. R339's reviewed candidate covers
   only children actually generated by this replay path; it does not supply
   the initial source Link or all designated/processing/FunctionPort cases.
6. `candidate_context.rs:2238–2285,2358–2452,3888–3908,3992–4056,4185–4228`:
   typed-drain frames, replay children, queue transfer, acknowledgements and
   retirement have distinct owners. A child remains represented in the replay
   operation until transfer/acknowledgement; use the precise frame state in H.
7. `candidate_intrusion.rs:423–455,595–704`: candidate-pair completion is
   relation/generation scoped; a row merge canonicalizes bounds, increments
   generation and reopens a diagnostic root. R336 L0 excludes high-level
   copy-derived intrusion in authentic K0, but the proof must still justify
   every reachable generation/merge path it uses rather than rely on the
   broad-file exclusion alone.

## Primary source-lane disposition

No source defect is established by this read-only census. At least five actual
source/native owners were inspected: `candidate_source.rs`, `lib.rs`,
`candidate_extrusion.rs`, `candidate_context.rs`, and `candidate_intrusion.rs`.
There is therefore no authorized implementation slice for this sprint:
`NO_SAFE_CODE_SLICE`. The proof lane owns the retention theorem/counterexample;
the source census supplies exact constructors, transition owners and pins.

R338 admission and R340 S0 dependency corrections remain separate OPEN delta
reviews. This census does not certify either amendment, all of N, cache
coverage, W/Z, M, principality, original A/B, or production readiness.
