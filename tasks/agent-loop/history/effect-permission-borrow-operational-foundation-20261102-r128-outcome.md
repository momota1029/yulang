# R128 outcome — checked local borrow model accepted

Status: **CLOSED_LOCAL_MODEL_ACCEPTED**. The user’s standing Yulang soundness,
effect-hygiene and Rust-delivery objective remains OPEN and authorized. This
receipt closes only R128’s standalone local operational-model subgate.

## Fixed objective and before/after evidence

R128 constructed a small Lean model for permission-record capture, shared borrow
stability, request copying and indexed consumption. The first candidate used an
argument-bearing family identity and failed its first Lean check. Immutable Rust
source audit established that `SourceEffectId` consists of exactly module plus
declaration. Versioned contract r2 corrected this source representation and
allowed only bounded parser/tactic repairs, without changing theorem scope,
transitions, premises or source-domain claims.

Final `Family ModuleKey SourceNodeKey` has exactly opaque module and declaration
keys with explicit decidable equality. A discriminator proves equal declaration
keys in unequal modules remain distinct. The model derives stable selected heap
reads from its transition rules, derives membership from successful guarded
consumer reads, and joins capture, first-position search, transition stability
and field copying. The `[9,9]` example distinguishes first capture at index 0
from later successful local membership at index 1.

## Frozen artifacts and review

| Artifact | SHA-256 |
| --- | --- |
| Contract r1 | `4f4c71e44ce17a8123a0d4f8bbc4f3e10f253e64d4d3fa0411b4c3059afff451` |
| Contract r2 | `7102e4fedd44aa6d1fd59511043e8655f487f30d5a1b252263d9d7d4852b0803` |
| Manifest r1 | `3d067a53f428f18d33b291313e7db6a654ae70271f29af51921cf339d39eb827` |
| Manifest r2 (superseded digest typo preserved) | `c2750b7ecc152885ff602966d8cb67711f6543e366c8dca0f760e84f160be7cf` |
| Manifest r3 | `434211f70b380de57c3106e9e995c9465351789820397e5b9a20b8cff69f9d88` |
| Lean module | `2042c8ee50c8123e93857ee0eab9e95c9eab5d47d63a649ff4552568a47507d7` |
| Proof handoff r2 | `8b351bf240ca57e7a3cc489ab54e670819c7b442c6ed74ee6b0fe392d936dcf5` |
| Source handoff r1 | `42c9db25645a5e54146027ff474546cce06048d63e2a4752f8cff3f52f375323` |
| Independent review | `77be7cb1f0263af2f3eba68b0fac6fd39f8388bcdbbf9685233afb32e7db1db9` |

The fresh `compiler_referee` returned **no blocking, major or minor findings**
within the local-model scope. It matched all five frozen artifact hashes, all
21 manifest input hashes, the pinned `SourceEffectId` owner hash, and the frozen
virtual receiver reconstruction. It confirmed transition induction, distinct
identity fields, actual consumer membership, capture-only first-position
reasoning, duplicate-index behavior, final theorem types and complete axiom
reports. Review was read-only; no check or build was repeated.

## Checks and resource record

Pinned native Lean 4.35.0 ran directly with `-j1 -M768`. History is retained in
the proof handoff: invocation 1 exit 1 (4.582810527004767s), invocation 2 exit
1 (0.7150449030013988s), invocation 3 exit 0 (0.7536799049994443s); total
6.051535335005610s. The first two failures are not proofs. The final invocation
accepted all ten audited declarations. Full types and `#print axioms` output
are frozen in the handoff. Dependencies use only `propext` and `Quot.sound`,
except `unequal_module_same_declaration`, which has no axioms. Both allowed
recheck slots are spent; no further Lean execution is authorized by R128.

`python3 tools/agent_sprint.py check` passed as static scheduling validation.
No Cargo, Rust compiler, tests, Lake, project build, generated cache, Rust source
edit or compiler check occurred in this sprint.

## Explicit residuals and separate Rust gate

All eight Rust-to-model equations remain OPEN: complete family equality and
clone fidelity; ordered vector publication; full-vector borrow plus heap and
transition simulation; native family/index interpretation; ordered search
correspondence; exact request-field transport; registration/packed-index/
pointer selection interpretation; and the same-record Option/Vec read equation.
R39 PRE construction, R45 extraction/certificate application, R114 transport,
original A/B obligations, full effect hygiene, source inference soundness and
production remain OPEN.

R127’s Rust candidate remains frozen and independently reviewed, with target
hashes: `lib.rs` `6eb6b5df29bda1d1bd1fecabcbc2cc6e85e777dda2045f1d1ab86084f64cd84f`,
`candidate_receiver.rs` `335f5f2cd4841dd8288306623ee863606e355b9ceda6948ab6877d944bed3165`,
and `candidate_effect.rs` `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01`.
R111’s private aggregate 6-GiB verifier is unavailable in the current WSL
configuration. Cargo remains 0/1. Its existing contract prohibits source
integration before that verification or an explicitly authorized, versioned
policy change. No Rust source commit or push occurred; this outcome is only an
evidence checkpoint. The user has been asked whether to retain that gate or
authorize a versioned compile-free source-push policy; no answer is recorded
here.

## Runtime, Git and current-state disposition

All R128 authors and reviewer are STOPPED, with no subprocesses or descendants.
Unknown historical workers and quarantined runtime source paths remain intact.
Only primary-owned R128 records and Lean artifacts are eligible for the
separately reviewed evidence checkpoint; dirty solver files, quarantined
`machine.rs`/`receiving.rs`, other untracked work and all unrelated changes are
excluded. Primary must inspect the explicit stage list and complete outbound
range before committing/pushing. No force push.

## Evidence checkpoint Git receipt

After independent review and explicit path staging, Luna committed the exact
12-path R128 evidence range as
`6f8fd21a359390b1e95f7b97f6ba30a253babf77` (`research: accept R128 local
permission borrow model`). The inspected range was one commit ahead of the
observed `origin/yulang3` base `3f90fa0b741e1365afb3a4108184cec6f487d4da`; its
name-status contained only the R128 Lean module, contracts/manifests, frozen
author/review handoffs, admission/outcome and `current.json`. The range passed
`git diff --check`. It was pushed without force to
`origin/yulang3:refs/heads/yulang3`, which advanced from `3f90fa0b7` to
`6f8fd21a3`; local `origin/yulang3` now matches that full commit. Dirty solver
sources, quarantined runtime sources, and unrelated untracked artifacts were
not staged. This is a pushed evidence checkpoint, not the requested Rust source
integration.
