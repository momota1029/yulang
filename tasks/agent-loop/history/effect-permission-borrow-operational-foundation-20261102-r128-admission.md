# R128 admission — operational permission-borrow fragment

Contract SHA-256: `4f4c71e44ce17a8123a0d4f8bbc4f3e10f253e64d4d3fa0411b4c3059afff451`.
Input manifest SHA-256: `3d067a53f428f18d33b291313e7db6a654ae70271f29af51921cf339d39eb827`.
Baseline: `yulang3` / `3f90fa0b741e1365afb3a4108184cec6f487d4da`; Rust source baseline `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`; pinned Lean `4.35.0`.

## Authority and live roster

Admitted under the user's continuing Rust/Lean soundness and effect-hygiene
goal. The user separately asked to analyze and push Rust implementation; that
request remains in force. The concrete Rust candidate is already frozen and
reviewed at R127, but R111 still forbids source integration until its private
6-GiB verifier gate is satisfied or versioned policy is changed. This sprint
does not weaken that gate and does not write Rust source.

Immediately before admission, `collaboration.list_agents` showed `/root` active
and every previously listed child completed. No RUNNING/WAITING child needed
notification. The 16 UNKNOWN historical assignments and all exact quarantined
leases remain unchanged. The existing authenticated capacity receipt already
releases exactly those 16 reservations; this admission applies no second
override and does not release any path.

## Assignments, leases and limits

- `/root/r128_permission_borrow_proof`, registered `lean_prover`, requested
  configured proof model / high effort, ≤600 seconds: Lean module and proof
  handoff only.
- `/root/r128_rust_source`, registered `researcher`, configured default Sol /
  high, ≤300 seconds: static source handoff only; immutable blobs and frozen
  patches only, no dirty/quarantined reads or Rust execution.
- `/root/r128_independent_review`, registered `compiler_referee`, Sol/medium,
  ≤240 seconds after both artifacts freeze: review handoff only.
- Luna owns this contract, manifest, admission, `current.json`, outcome,
  adjudication and Git. Astra budget is zero. Total active assignment envelope
  is at most 1,380 seconds.

Only the exact outputs in the contract are leased. Lean execution is direct
native Lean 4.35.0 with `-j1 -M768`, at most 90 seconds per call and 180 seconds
aggregate; no Lake, project imports, generated `.olean`, cache, install, copy,
worktree, storage probe, Cargo, Rust compiler, tests or broad audit. The
combined new artifact ceiling is 128 KiB.

## Success boundary

Success means checked local operational definitions and theorems, complete
types/axioms, a frozen immutable Rust source map, and independent acceptance.
It does not close the original parent, actual Rust pointer/heap bridge, R45
extraction, R111 compile gate, source integration, or production. A source
counterexample, missing identity field, unsound transition, Lean failure, or
unresolved reviewer finding is retained as an open result, not repaired by
adding an assumption.

## Launch and compact-state receipts

Supported `collaboration.spawn_agent` calls accepted `/root/r128_permission_borrow_proof`
and `/root/r128_rust_source`; both are recorded RUNNING in the `R128` session
with observed model/effort still UNKNOWN. The read-only reviewer remains
NOT_STARTED until both outputs freeze. No prior RUNNING/WAITING child was live.

To admit this sprint within the 16-KiB state limit, the primary removed only
resolved primary-owned lease rows whose artifacts remain preserved in the
repository and whose closed outcomes are archived: five R98 paths (contract,
admission, outcome and two diagnostic logs); three R108 paths (contract,
admission and outcome); the R59 state-compaction closeout lease; the R104
Lean module and proof-handoff leases; and the two R107 protocol/reconstruction
handoff leases. No worker row, UNKNOWN/quarantined lease, dirty source path,
pending item or artifact was deleted. The active `candidate_scheme.rs` lease
remains FROZEN. Static `agent_sprint.py check` passed after admission.


## Versioned amendment r2 — exact identity and bounded repair

The initial contract's candidate `Family Arg` had a declaration plus an argument
list. Frozen source handoff r1 (SHA-256
`42c9db25645a5e54146027ff474546cce06048d63e2a4752f8cff3f52f375323`) identifies
Rust `SourceEffectId` as exactly module plus declaration fields. The proof author
acknowledged this mismatch and the proposed correction before amendment, with no
active check or output process; the author reported prior assignment wall time
UNKNOWN and will receive at most 120 seconds of additional active work. The
correct model is `Family ModuleKey SourceNodeKey = { module, declaration }`,
with opaque key components and explicit decidable equality. No argument field is
claimed; broader argument interpretation remains OPEN. Require an unequal-module
/ equal-declaration discriminator and retain duplicate `[9,9]` behavior.

Contract r2 SHA-256: `7102e4fedd44aa6d1fd59511043e8655f487f30d5a1b252263d9d7d4852b0803`.
It preserves the first failed direct Lean check at 4.582810527s and permits at
most two further checks, each ≤90s, aggregate ≤175.417189473s including the
initial check. The assignment envelope is not reset; theorem statements,
quantifiers, transitions and premises stay fixed except the specified identity
representation correction and parser/tactic repairs. Any need for a new premise,
semantic transition change, or weakened claim is a stop condition.

Manifest r3 SHA-256: `434211f70b380de57c3106e9e995c9465351789820397e5b9a20b8cff69f9d88`.
It fixes a mistyped r2 source digest for `source_annotation.rs`, pins the frozen
source handoff, and lists the amended contract/output. Source owner is STOPPED;
proof owner acknowledged and is WAITING for exact resume. R111 verifier gate,
Cargo 0/1, Rust integration prohibition, all UNKNOWN worker observations and
quarantined paths are unchanged.

## Proof result r2 — frozen before review

The proof worker returned STOPPED with no active process, descendants or
unaccounted output. Corrected Lean module SHA-256
`2042c8ee50c8123e93857ee0eab9e95c9eab5d47d63a649ff4552568a47507d7` (13,869
bytes); proof handoff revision 2 SHA-256
`8b351bf240ca57e7a3cc489ab54e670819c7b442c6ed74ee6b0fe392d936dcf5` (65,061
bytes). The three direct native Lean invocations exited 1, 1, 0; total measured
checker time 6.051535335 seconds. Both resumed check slots are exhausted. Ten
complete theorem-type/axiom audits are retained; dependencies use only
`propext`/`Quot.sound`, except the unequal-module discriminator which uses no
axioms. No sorry/admit/project axiom/bypass match was found. Independent review
is pending. Source-to-model equations, R39/R45 application and the original
parent remain OPEN. This result does not release or change the R111 Rust-source
integration gate.

## Closeout and review adjudication

Fresh independent review handoff SHA-256
`77be7cb1f0263af2f3eba68b0fac6fd39f8388bcdbbf9685233afb32e7db1db9` returned
no blocking, major or minor findings within the local-model scope. Luna accepts
only that local subgate; source simulation, eight source equations, parent and
production remain OPEN. Outcome receipt SHA-256
`70a8f047d87de3316d2020b74e72931b1208a2b3b0afcd1bfe904f961de9ba02` records the
review, all three Lean exits and limitations. Dispatcher recommended
`CLOSED_LOCAL_MODEL_ACCEPTED`, an evidence-only Git checkpoint, and no further
source-analysis sprint absent a new verifier or concrete source-attachment
method. R111 source integration remains gated and is not authorized by this
closeout.
