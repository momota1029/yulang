# NATIVE-LAUNCH-PROJECTION/r6 amendment 01 — immutable proof/core source reads

Status: ADMITTED by Luna. Base contract SHA-256:
`01236acb3ef9134788e58aa888ec7d498ddd24fa9f64250c4f1fc2837f03034a`.
R6 source baseline remains `7b3ad7074`.

## Reason and disposition

The Rust lane's exact output leases overlap three of the base contract's source
read paths: `candidate_scheme.rs`, `candidate_context.rs`, and
`candidate_extrusion.rs`. Astra observed `candidate_context.rs` change from its
initial input hash while reading. It stopped source reads. The proof lane also
stopped using those moving paths for source-dependent conclusions. No mixed
read is retrospectively authenticated.

Luna reconstructed the immutable input bytes from the exact R6 baseline commit,
not from a moving Rust output. The three proof/core source inputs are now
available at the new read-only copy paths below. Proof and Astra must use those
paths for these three source bodies. Rust retains its exact existing output
paths and grant. Other inputs, objectives, parent quantifiers, source domain,
success predicate, output leases, reviewer/check gate, and all budgets are
unchanged. This adds no compiler or production authority.

```text
isolated/native-launch-projection-r6-proof-input/crates/yu-solver/src/candidate_scheme.rs
  35c58dca3748595e273cd53bfba07da2be3fd340ec63c56f6a18adea5e514fb1
isolated/native-launch-projection-r6-proof-input/crates/yu-solver/src/candidate_context.rs
  57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e
isolated/native-launch-projection-r6-proof-input/crates/yu-solver/src/candidate_extrusion.rs
  80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61
```

These are primary-created, exact-file, read-only copies from
`isolated/native-launch-projection-r6-baseline/`, itself archived from commit
`7b3ad7074`. No worker may write them or read their changed output counterparts
as baseline evidence. All other proof/core Rust inputs stay on the already
admitted, hash-verified snapshot paths because the Rust lane has no write lease
for those files.

## Additional exact proof read

The proof lane may read the following source-scope locator, limited to §§1, 3,
and 5, to map the approved source-preservation obligation and its original
quantifiers. It does not alter semantic authority or prove source/native
correspondence:

```text
notes/theory/2026-10-13-intrusion-source-preservation-proof.md
SHA-256 3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271
```

Proof and Astra must ACK this amendment SHA, all three new copy hashes, the
additional document hash, and the unchanged base contract before reading these
bodies or using these paths in a conclusion. The proof lane may also read the
following frozen Astra handoff as an independent lead only; it must rederive
any source claim from the amended immutable inputs:

```text
tasks/agent-loop/inbox/native-launch-projection-r6-core.md
SHA-256 c8ca2b528fcaf4b62c578535cfbe570db92dfa47cae5d1c025c0fd4b0072482d
```

Revalidate only what was read from the overlapping mutable paths; retain
earlier observations only when they were from independently pinned immutable
inputs. No grant reset, renewal, or extra stage is issued. The Astra lane has
stopped after its third stage on the detected read/write collision; no Astra
restart or unspent-budget credit is granted. Its handoff is retained with the
source/hash race qualification.
