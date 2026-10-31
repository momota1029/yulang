# Sprint EFFECT-PERMISSION-DEFINITION-CALL-BRIDGE/r1

Status: ACTIVE after Luna admission; source baseline `bc2a0836ec`  
Branch: `research/simple-sub-intrusion`  
Authority: ongoing user-authorized Yulang soundness research; `rules/goal-driven-sprints.md` §§1–5; original parent remains `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1, 3, 5.  
Selector: `/root/r3_selector`, sprint-end consultation after consumer-residual/r1.

## Original outcome and success evidence

Establish the exact source-owner path for the existing consumer fixture from its
provider value through module `Definition` recursion and `Call`, returned value,
tuple-pattern projection, and effect extraction; alternatively identify the
first unsupported transition. Preserve the original source domain, effect
hygiene claims, fixture and expected output. The source-demand/oracle claim and
any claim that a contribution is lost remain OPEN unless each identity edge is
derived from the pinned constructors and same-contribution evidence.

The original residual observation is retained as outcome (4). The empty test
census is finite observation only. The fixture contains no Catch/handler and
does not observe subtraction. This sprint neither changes semantics nor closes
the original parent, H/A/B, source/native, principality, termination or
production gates.

Success: a typed provenance graph with explicit source constructor, endpoint
direction, owner and contribution identity for each supported edge, plus an
application to the exact fixture; or an exact first missing edge. The graph
must reject provider, Call-result or projected-component substitution while
holding the contribution identity fixed. A separate extraction statement must
show whether the same contribution is retained in the returned computation.

## Two continuing lanes

Proof lane (`lean_prover`): identify module-definition recursion/Call authority;
derive typed provenance-edge and same-contribution extraction lemmas from the
actual constructors; apply them to the frozen source/native evidence; state the
first unsupported premise if application fails. Do not reuse a conditional
publication/replay lemma as an unconditional residual theorem.

Implementation lane (`implementer`, Luna/high): read-only source-route audit
through the exact pinned `candidate_source.rs`, `candidate_effect.rs`,
`candidate_scheme.rs`, `shadow_apply.rs`, and `lib.rs` inputs; produce a compact
owner-to-owner trace or exact missing edge. First admission gate is
authentication of the prior `candidate_effect.rs` delta. Preserve current
bytes `1715046b…`; seek exact predecessor bytes matching `6f20ac00…` only in
authenticated retained artifacts. If absent, retain `DELTA_AUTH_UNRESOLVED`
and declare `NO_SAFE_CODE_SLICE`; do not edit candidate source, overwrite,
reverse-engineer or claim rollback. Any new candidate instrumentation, clean
baseline workspace, Cargo or Lean execution requires Luna's versioned contract
amendment and separately frozen inventory/release.

## Exact pins and leases

Read-only source pins:

| Path | SHA-256 |
|---|---|
| `crates/yu-solver/src/candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| `crates/yu-solver/src/candidate_effect.rs` | `1715046b29b760fe70b3c2fb05665dad23e7f95ad05883c39d06d4da37b925ab` |
| `crates/yu-solver/src/candidate_scheme.rs` | `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707` |
| `crates/yu-solver/src/shadow_apply.rs` | `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `FormalPermissionAuthenticatedSiteExport.lean` | `d6fc3e11f26350f6cf03d7afc248500778e3bf4a8ee816582630aa5f5feeeb84` |
| consumer Rust handoff | `c873113f179634be7f9e29e90eea95f717bd50f4ceb314c239379e488ce8b1fe` |
| consumer proof handoff | `7437b723ac103af620dd35dd348ec78fbd82c176eb9893b4acf0578da9b817db` |
| consumer review | `505463444165018764e3b4680b58a624f43da7eeeccd2db6489d6ed4d5088691` |
| consumer outcome | `570f6df0b10886d248a4214a3671e8a23e143a7e6270e4d19cb43b457b1ba9d2` |
| verified 280-entry invocation-1 inventory | `a1785f08ca2fc0a2fbdae0e1dd1d1345e41c8d2db36180bc912f163def7560f0` |

Fresh output leases: `notes/theory/lean/YulangClosure/FormalPermissionDefinitionCallBridge.lean`, `tasks/agent-loop/inbox/effect-permission-definition-call-proof.md`, `tasks/agent-loop/inbox/effect-permission-definition-call-rust.md`, and this contract. No other writes. Source reads stop at the pinned owner boundary; a newly discovered callee requires a Luna amendment and re-pin.

## Resources, review and stop

Envelope: 1,400 seconds total (Rust/source audit 500, proof 350, fresh review
250, Luna 150, contingency 150); two producer assignments, zero Astra. At most
two Cargo invocations sharing 180 seconds and two Lean invocations sharing 120
seconds; actual execution requires separately frozen input inventories and
Luna release after source-route and provenance gates pass. One heavyweight
process at a time; Cargo observed RSS ceiling 2 GiB, Lean 1 GiB. No execution is
authorized by this contract before those gates.

Fresh nonauthor review checks delta provenance first, then module Definition/
Call authority and every provider→Call→result→pattern→extraction edge, including
the fixed-contribution substitution falsifier. No review of moving bytes.
Workers stop on handoff, scope boundary, unresolved provenance with no safe
read-only step, resource bound or user STOP. Luna updates current/history and
consults the dispatcher at the next material boundary. All unknown legacy
identities and quarantined paths remain untouched; capacity release is not
cessation or lease release.
