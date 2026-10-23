# Sprint R341 — K0 source-constraint retention into S0

Status: FROZEN / Luna-issued, revision 1.  
Branch / baseline: `research/simple-sub-intrusion` / `d6610bb03cd1f9037df834982722e0022fc79209` (same as upstream).  
Selector: `/root/r333_selector` recommended this bounded S0 bridge at the R341 boundary; STOPPED.  
Primary: `/root` (Luna).  
Contract SHA-256: set in the primary-owned current-state receipt after this file is frozen.

## Original outcome and success evidence

**Unchanged parent:** user audit `docs/Yulang Simple-sub 拡張：全体証明への移行監査・証明設計.md`, SHA-256
`b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`, §§4, 6
(G/N/S), 9 and 10.3. The full goal remains proof-backed Yulang inference and
execution through the same Yulang2 playground examples on the evaluation
machine. Original Simple-sub A/B, quantifiers, source/native correspondence,
principality and production gates remain intact.

The S0 claim is unchanged:

```text
ValidK0(s) ∧ NativeComplete₀(s,S) ∧ ρ ⊨ H(S) ∧ Reifiable₀(ρ)
  ⇒ ∅ ⊢₀ s : ρ(v_s) ! ρ(ε_s).
```

R341's bounded proof question is the missing G-to-final-H supplier: for the
authentic K0 source constraint family `C_s`, including the Definition-root
Value link, show that a solution of final `H(S)` satisfies every member of
`C_s`, using one explicit kind-preserving row restriction/transport map. If the
claim fails, provide an authentic completed K0 state and a valuation of final
`H(S)` that violates an exact source inequality. Apply R336 D1/G-sound only
after this bridge and its explicit `Reifiable₀` premise are established.

**Source admission rule:** fresh and duplicate successful receipts both add
`q` to the logical work theory: `H_after = H_before ∪ {q}`. Duplicate
`FactId` identity is not evidence that `H_before ⊨ q`. Any equality-of-solutions
claim across admission needs an independent entailment proof. Do not treat
`pair_is_current`, `completed[generation]`, a queue pop, or store provenance as
proof that the source inequality is solved. Keep a pending/current/processing
obligation in H until a same inequality or justified surviving entailment
represents it.

Success is one of:

1. a proof/refutation of retention for the authentic root `Action::Link`;
2. a source-qualified inventory of all seven K0 source forms and the root
   bridge, extending the invariant across the authenticated constructor family
   or naming the first exact exception; and
3. a precise S0 application that records the source-row support, sort-preserving
   representative/transport map, and unchanged `ValidK0`,
   `NativeComplete₀`, `H(S)` and `Reifiable₀` premises.

The before/after evidence is the currently open final-H-to-C_s bridge, reduced
to an owner-complete retention theorem or to the first authentic exception.
An R341 result does not close all N, cache coverage, W, Z, M, S0 without its
stated premises, principality, original A/B, catalog support or production.
S0 is source typing only. Runtime preservation/progress require the separate
M composition and actual runtime realization.

## Exact authority and dependencies

- Audit design file and SHA above are user-provided, untracked and read-only.
- R336 reviewed D1/G-sound source typing: `notes/theory/2026-10-23-r336-k0-d0-d1-rev4.md`,
  SHA-256 `4bcbe71ec9f2372baca884e3db737c16fc19ad2a51103965ade5ca4c2ecf4973`;
  review SHA-256 `d03b7a23bcec2bd0575bf391342f92353b46b840cbcfa70deea7500786fd892e`.
- R337 context preservation proof SHA-256
  `e14b8125a505c3001021396b8c6e949e3b0a58f61ecf2785f915dbdde65dfc62` and
  source census SHA-256 `771c3c8ab2a69336579c78a7583097b8d1839bf0d6fe97f2e69da27e77500e6a`.
- R338 proof SHA-256 `f438939f99c212324a397f527d46d4a4ab565733e4b2e9e2ae55254e96ca9bf0`;
  rev1 review input SHA-256
  `1361b0223e8950c3e6546f1cbcb9cd25bd7a0ca038511f7c55cad29d3659fa6d`;
  current rev2 SHA-256 `56174af37c13d2e6ac846b84c3fd71075bceefb8b05474c1f8b3d6d5b2c50ac9`.
  The admission correction is still awaiting independent delta review. R341
  must derive the admission semantics from the pinned source and audit rather
  than assume either census revision's disputed equality claim.
- R339 replay-retirement candidate SHA-256
  `8797013ab5ea77655629fce45031fb28e1c5557979c1f213b9268abd31080c87`; use
  only for actual `candidate_replay_bound` children and its stated premises.
- R340 contract SHA-256
  `5de2605641bc28bdea416be1d7eea69a0bff4a689d39b33a2c2738b23cc7642c`; Apply
  proof SHA-256 `7ae75ef26d6bfa441989e9655dda89fbed2927d0061f5d8445246d587a0d7737`;
  full source census SHA-256
  `de3902d834a68f0d4f5b269f4bddac7d900d44bfe8dc118b05b451372cf24078`.
  Its immutable rev1 prefix is 16,711 bytes with SHA-256
  `5b9fd45dc51a902c96a23586b4965a674b8429554340d8c3d01d4410746ecf5f`.
  The S0/S0+M correction is awaiting independent delta review.
- Primary R341 source census:
  `notes/theory/2026-10-23-r341-k0-source-retention-census.md`, SHA-256
  `729c224785d42ee3577351e6a001668fe97a17fb2323aa532f52bbc8a1be0eeb`.

Production source SHA-256 pins:

| Source owner | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_source.rs` | `0dc798e48e70505093e52b31b2569e3b2d8ff1dee663095176aaf547ccb3289b` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_context.rs` | `33af2efb6ed782e4f143cccff03c62087e6ba8d0fbe90415846537fc2a08cec5` |
| `crates/yu-solver/src/candidate_effect.rs` | `d156fdbf0300387a5aa036053a2cc7eeb6312a803aaf38838e30dd2731ca4945` |

No production source file is leased for editing.

## Two continuing lanes

**Proof lane — one Sol/high `prover`, 2,400 seconds.** Exact output leases:

- `notes/theory/2026-10-23-r341-k0-source-constraint-retention.md`
- `tasks/agent-loop/inbox/20261023-r341-k0-source-retention-prover.md`

One multi-stage assignment: (1) prove/refute authentic root-Link retention,
including admission → cache decision → owner-bound append → drain retirement →
final H; (2) audit Literal, parameter Name, Value Lambda, Apply, If, Group and
binding-free Block/StatementBlock; (3) extend the persistent-witness invariant
to all authenticated K0 inequalities, or stop at the first exact exception;
(4) apply the result to the unchanged S0 source-typing implication with the
explicit row map. Apply R336/R337 only inside reviewed premises. Use R339 only
for its replay-child family. Do not claim `completed` means semantically
entailed; investigate the `record_typed_pair_admission` /
`mark_candidate_pair` / `pair_is_current` relationship. No descendants, code,
tests, Cargo/build, runtime probes, scratch files or Git.

**Source/implementation lane — Luna, 2,100 seconds.** Own the frozen primary
census and verify each source/native owner in that note. No compiler defect has
been established after inspection of more than two actual owners, so record
`NO_SAFE_CODE_SLICE`; make no compiler semantic or implementation change.

The two narrow dependency deltas run alongside the proof under one fresh,
non-contributor read-only reviewer, aggregate cap 300 seconds, message-only:

1. compare only R338 rev1 snapshot bytes/hash with the R338 rev2 admission
   correction and return a separate disposition;
2. compare only R340's 16,711-byte rev1 prefix with the S0/S0+M appendix against
   audit §6 S and the accepted R340 finding, returning a separate disposition.

Do not re-review the unchanged R338/R340 proofs. Do not infer the R341 result
from either amendment's acceptance. After the proof and census freeze, Luna
assigns a fresh non-contributor `compiler_referee` up to 900 seconds for the
bounded theorem, source-owner correspondence, exact assumptions/falsifier and
S0 application. Luna adjudicates and integrates; no producer or coauthor
reviews their own artifact.

## Source path and open premises

K0 constructors emit source-owned inequalities or authentic endpoints in
`candidate_source.rs`; `Action::Fact`, `Action::ValueConstraint`, recipe
admission and the root `Action::Link` enter `lib.rs`'s typed work path. The
independent final-state interpretation reads directed owner bounds and retained
work. `candidate_extrusion.rs` owns physical bound insertion/readback and
opposite-bound replay; `candidate_context.rs` owns drain/replay transfer and
retirement; `candidate_intrusion.rs` owns generation changes/reopen. The exact
mapping and remaining exception search are in the pinned R341 source census.

Open suppliers: source-complete K0 census and authentic admission; sound final
H interpretation including every pending/processing/replay frame; cache and
generation correctness; any reachable intrusion owner not excluded by L0;
all seven constructor cases. R336 G-sound remains conditional. W, Z, full N,
M, and any removal of the S0 solution/reifiability premises remain later gates.

Falsifier: a source-qualified authentic K0 successful completed state `S` and
one explicit assignment `ρ` with `ρ ⊨ H(S)` but `ρ ⊭ q` for an exact source
constraint `q ∈ C_s`; identify the H definition, row map, source occurrence,
admission and retirement transitions. A hypothetical valuation without a
reachable authentic state is a missing premise, not a compiler counterexample.

## Permissions, leases and resources

Exact write ownership:

- Luna: this contract, `notes/theory/2026-10-23-r341-k0-source-retention-census.md`,
  and `tasks/agent-loop/current.json`.
- Prover: only the two exact proof/handoff files listed above.
- Delta reviewer: read-only, message-only; no output file.
- All prior frozen artifacts and production sources: read-only.
- User-provided audit document: read-only and never staged.

Total cap: **6,000 seconds**, no carryover: Luna source/contract lane 2,100;
proof assignment 2,400; both delta reviews together 300; fresh final review 900;
integration reserve 300. Reserve two slots for final review/integration. The
three legacy UNKNOWN workers remain quarantined and retain their reservations;
with Luna, one proof worker and at most one reviewer the maximum is six active,
reserved or UNKNOWN assignments. No Astra assignment. A missing model/effort
observation remains UNKNOWN. A failed launch consumes its attempt. No daemon,
nested CLI, hot reload or after-session work.

No tests, `cargo`, build, or execution probe are authorized by this proof packet.
The primary may run the repository's static `python3 tools/agent_sprint.py
check` for current-state consistency after synchronizing state; it is not
mathematical evidence.

## Frozen seams, review and continuation

Freeze proof, handoff, source census and all direct dependencies before final
review. Acceptance requires no open blocking/major finding in this bounded
result; any accepted repair must preserve the original S0 premises and be
re-reviewed as a delta. A reviewer rejection is adjudicated by Luna, and the
proof lane continues only within the same scope/lease/budget. Source-qualified
counterexample refutes this bridge and blocks dependent S0 use, but does not
weaken the full product goal.

Next related steps inside this envelope are the seven K0 constructor audit,
exact cache/retirement source checks for this invariant, parent application to
S0, and frozen handoff. Return to Luna before changing source domain, semantics,
premises, worker count, resources or write paths. Consult the dispatcher at the
next sprint boundary, a source-qualified exception, a substantive dependency or
lease change, or the integration seam—not after each lemma or review receipt.

At the closeout boundary, update compact current state and durable outcome,
preserve all UNKNOWN leases and OPEN gates, run only the static sprint check,
inspect the full intended Git range, and commit/push only exact approved paths
with a non-forced update.
