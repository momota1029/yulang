# R345 — K0 initial-drain obligation preservation

**Status:** ACTIVE, revision 1, admitted by primary `/root` at the pinned
`addd4ea9f` baseline. This is a fresh sprint; no R344 budget or authority
carries over. Primary `/root` owns this contract,
the read-only source census, `tasks/agent-loop/current.json`, review adjudication,
outcome and Git integration.

## Original goal and bounded outcome

The unchanged parent objective is the full Yulang2/Simple-sub source/native A/B
theorem and catalog, including source-to-runtime correspondence. The original
audit remains governing for that scope and its quantifiers. The whole-language
semantics document fixes the intended typed elaboration, boundary evidence,
world-indexed value/computation interpretation, effects and Q1–Q8 closure
conditions. Neither source document is weakened or replaced by this K0 packet.

R345 advances audit N/D2 from the exact residual left by R339: initial/current,
designated, processing and Function-port obligations must remain represented
or be entailed after successful cache suppression, dispatch, child handoff and
typed-drain terminal/frame retirement. The result is a bounded same-row-set
solution-preservation theorem, or the first source-qualified counterexample or
precise missing premise. No full N, cache coverage, W, Z, S0, whole-language
soundness/principality, original A/B or production gate closes here.

### Independent K0 algebraic interpretation

Use the R338/R339 `H(S)` interpretation, independently of source typing and
runtime success. For a same-sort task `q=(l,u)`, let `φ(q)` be the fixed K0
Value comparison or Effect inclusion. For a bound key `(o,p,b)`:

```text
β(o, Positive, b) = b ≤ o
β(o, Negative, b) = o ≤ b
```

The interpreted theory is

```text
H(S) = B(S) ∪ Q(S) ∪ P(S) ∪ R(S) ∪ D(S)
```

where `B` projects existing direct/exact Value and Effect bounds and retained
owner keys with attached relations; `Q` interprets pending typed work; `P`
interprets actual current/initial requests, pending dispatch, designated and
saved processing pairs/relations, and live caller/local transfers; `R`
interprets each unretired replay child slot; `D` interprets retained structural
dispatch children. Physical duplicate incidences remain distinct, while their
identical formula contributes idempotently to this conjunction. Bare memo,
generation, completion, acknowledgement and historical source-store labels do
not independently add formulas.

This `H` is the existing narrow K0 algebraic interpretation, not the semantics
document's `Vⁿ_{W,θ}` / `Cⁿ_{W,θ}`, source boundary evidence `k`, or contextual
effect interpretation. Their connection remains open. Do not use preorder
transitivity for optional concrete record comparison.

### Transition and admission contract

For every successful administrative transition in the contracted initial
drain family that removes a logical formula `φ(q)` from `H`, establish either
(a) the identical formula remains in `H_after`, or (b)
`H_after ⊨ φ(q)`. Then show
`Sol(H_after)=Sol(H_before)` for that same-row-set transition. A newly admitted
source inequality is separate:

```text
H_after = H_before ∪ {q}.
```

Do not assert equality for source admission unless `H_before ⊨ φ(q)` has been
proved independently. A duplicate identity, cache membership, generation
stamp, or successful queue operation supplies no such entailment by itself.
If a transition allocates rows, identify the exact extension and compare by an
explicit projection; do not silently call it same-row-set preservation.

Trace the actual lifecycle through `start_typed_drain`, dequeue/current
publication, `pair_is_current` and `dispatch_live_item`, Function-port child
admission/enqueue/dispatch, replay-child handoff where reached, and
`candidate_step_typed_drain_terminal` restoration/pop. Include Value and Effect
sorts, polarity, exact task/owner identity, pending and processing state, and
the R337 ordinary-context premise. Function-port children need their actual
four-port variance operation and relation; a direct replay-bound witness cannot
be generalized to them without proof.

## Fixed inputs and exact pins

- Branch `research/simple-sub-intrusion`; baseline and configured upstream both
  equal `addd4ea9ff2b868fd01dca28c34e6c2b0d6e42d8` at admission.
- Governing user audit:
  `docs/Yulang Simple-sub 拡張：全体証明への移行監査・証明設計.md`, SHA-256
  `b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`.
- Whole-language semantics input:
  `docs/yulang-whole-language-semantics-ja.tex`, SHA-256
  `6246e7dc179a795b372603eac8cd64bf783ba69e9a4a733bcfc012ebd6869612`.
- User-requested aligned audit revision (context and crosswalk only; it does
  not redefine `H(S)` or promote a gate):
  `docs/Yulang Simple-sub 拡張：全体証明への移行監査・証明設計（全言語意味論整合版）.md`,
  SHA-256 `bea755595302d5b98fb1880fb89b505ad783a6e428c639aae6734b167df86d65`.
- R339 contract rev2: `953d0edfffc99645ab137819ae44d35a7df03b8e775b4e97317f825657dfaa00`.
- R339 obligation-retirement proof: `8797013ab5ea77655629fce45031fb28e1c5557979c1f213b9268abd31080c87`.
- R339 outcome and its fresh bounded review receipt:
  `07abaf5ee285917a4f49ce94fbf287b115dfcdbd20f8275bdcb6bcc3acec0701`.
  Accepted scope: ordinary emitted replay-child `q` retention only. Whole-frame
  initial, designated, processing and FunctionPort obligations remain open.
- R338 D1/D2 contract, proof and source census:
  `d742fa449c81b8b3cc918f53f93fc462dccb98565a2ed817e0b64162919ee403`,
  `f438939f99c212324a397f527d46d4a4ab565733e4b2e9e2ae55254e96ca9bf0`,
  `56174af37c13d2e6ac846b84c3fd71075bceefb8b05474c1f8b3d6d5b2c50ac9`.
- R337 context proof and R336 D0/D1 proof:
  `e14b8125a505c3001021396b8c6e949e3b0a58f61ecf2785f915dbdde65dfc62`,
  `4bcbe71ec9f2372baca884e3db737c16fc19ad2a51103965ade5ca4c2ecf4973`.
  Preserve their exact premises; R337 supplies only ordinary context
  lifecycle, and R336 S0 retains its original four premises.
- Exact source owners reached by this packet:

| Owner | SHA-256 |
|---|---|
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/candidate_context.rs` | `33af2efb6ed782e4f143cccff03c62087e6ba8d0fbe90415846537fc2a08cec5` |
| `crates/yu-solver/src/candidate_effect.rs` | `d156fdbf0300387a5aa036053a2cc7eeb6312a803aaf38838e30dd2731ca4945` |
| `crates/yu-solver/src/candidate_source.rs` | `0dc798e48e70505093e52b31b2569e3b2d8ff1dee663095176aaf547ccb3289b` |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |

Re-verify every pin before proof review. HIR/runtime/compiler source is
read-only. Extend the manifest only for a named owner actually reached, with
reason and exact hash. The user audit and semantics `.tex` stay untracked and
are never staged.

## Lanes and exact leases

**Constructive proof lane — requested `prover`, Sol/high, maximum 3,000 seconds.**
It may continue through related initial-drain cases and the exact first
counterexample/missing-premise analysis under this fixed claim. It owns only:

- `notes/theory/2026-10-23-r345-k0-initial-drain-preservation.md`
- `tasks/agent-loop/inbox/20261023-r345-k0-initial-drain-prover.md`

**Read-only source lane — primary `/root`, maximum 2,400 seconds.** Census
source ingress, dispatch, Function-port lifecycle, task/term orientation and
terminal restoration in the pinned owners. It owns only:

- this contract;
- `notes/theory/2026-10-23-r345-k0-initial-drain-source-census.md`;
- `tasks/agent-loop/current.json`.

After both artifacts freeze and the proof worker has stopped writing, assign one
fresh non-contributor `compiler_referee`, requested Sol/medium, maximum
1,500 seconds. Reviewer has no write lease. Reserve 300 seconds for integration
and state synchronization. New sprint cap: **7,200 seconds** total, charged
conservatively when granted. No Astra, carryover, renewal, tests, Cargo/builds,
execution probes, descendants, external contact, or worker Git. Preserve the
three legacy UNKNOWN workers, their quarantined leases and reservations. Keep
the six-assignment active/reserved/unknown ceiling.

No compiler edit is authorized by the source census. At least the actual
`lib.rs` dispatch/terminal owners and `candidate_context.rs` Function-port
admission were inspected; no source-qualified defect is established, so the
implementation disposition is `NO_SAFE_CODE_SLICE` unless the frozen evidence
changes that finding.

## Review, falsifiers and stop boundary

The source census must identify, for each removed formula, the exact
constructor, kind/polarity, source occurrence or Function field, queue/frame
owner, removal transition and remaining bound(s) or retained slot. It must
distinguish new source admission from recording/dispatch/retirement. Unknown or
unreachable state combinations are not treated as reachable counterexamples.

Fresh review challenges the independent `H(S)` definition, every lifecycle
case, frame restoration of previous processing, the `pair_is_current` shortcut,
duplicate relations, Function variance and the same-row-set premise. Its
falsifier is an authentic reachable ordinary K0 path whose post-retirement
`H(S)` is satisfied by a valuation that falsifies a removed formula, or an
omitted reachable owner/transition. The reviewer also checks that bounded K0
algebraic preservation is not described as full typed-view/source semantics.

Stop on any pin mismatch, unreconciled writer/lease, exact counterexample,
missing reachable owner, accepted blocking/major review finding, budget cap,
or user STOP. If a required D0/A/B contract change appears necessary, return to
Luna for versioned replanning; do not reinterpret a frozen premise. Only Luna
adjudicates, updates current, stages explicit paths and integrates. The next
selector consultation is at the frozen review/integration seam, a material
counterexample/dependency/lease change, or sprint end.
