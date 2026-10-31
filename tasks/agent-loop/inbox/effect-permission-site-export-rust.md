# EFFECT-PERMISSION-SITE-EXPORT-20261028/r1 — Rust handoff

Contract: `tasks/agent-loop/sprints/effect-permission-site-export-20261028-r1.md`,
SHA-256 `712ba875f6f1d31fde5732aea7dc07b24769be77407590ac9ec4626c407e9f11`.
Assignment: `/root/effect_permission_source_transport_rust`; handoff revision 4,
post-invocation-2. Requested role/model/effort: registered implementer,
Luna/high. Observed model/effort: UNKNOWN to this worker interface. No
descendants. Both allowed Cargo invocations are used; no retry was made.

## Frozen source and evidence pins

Writable source at final freeze:

- `crates/yu-solver/src/candidate_effect.rs` —
  `92b8a6c59f1c052a47f12c8c858fa675eaddfa83d514f6ed3e2982bb88b1a182`
- `crates/yu-solver/src/candidate_scheme.rs` —
  `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`

The candidate_scheme lease is unchanged and was not edited. The exact read-only
contract pins were rehashed and matched: `candidate_intrusion.rs`
`475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97`,
`candidate_extrusion.rs`
`80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`,
`lib.rs` `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`,
`shadow_apply.rs` `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`,
`Cargo.toml` `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`,
decoder Lean `7c01a80c8d8e868d9349a3d02ec2d465ca976edfb515e04b57161b5c9744a67f`,
native Lean `a5ccf179ef6e5396adb46c18ced108052cba4022119efd0daa0d026b4c368de1`,
prior outcome `20d1e42b0e88ea1c4695ea34d31168596b944a41f0d282050266d8812396bfca`,
prior Rust handoff `08760fd52e67d3b405638c8b378e98915ca903be7a96b4840aade071f5c2000f`,
failed conditional Lean source `c737dc721df6c77506dc3176fd3863c5103573124f92dd51636037be8de625a7`,
Lean handoff `ccd778ebb4880a6922238b00df08c97a4a0cbb5471277f9baa9cc28078812980`,
and independent review `2e750075c318c433e4476027b16af01fb3d034df4ea609b98e7dac8ab2d34b9b`.

Prior Rust and Lean STOP receipts and the review's stopped-writer finding were
read before work. The parent confirmed the Lean audit process had ended before
Rust activity resumed. A wrong-path incident briefly modified the prior
sprint's inbox handoff; it was restored byte-for-byte to SHA
`08760fd52e67d3b405638c8b378e98915ca903be7a96b4840aade071f5c2000f`, which
the primary independently rehashed. That old path was not accessed again.

## Test-only source observations

The candidate_effect test instrumentation records enclosing
`SourceAnnotation.position` separately from nested `SourceEffectRow.position`,
plus constructor, owner, occurrence, parameter offset and full Function/Tuple
path. Its recursive zipper walks the actual `SourceAnnotationType` Function
and Tuple nodes and records `(path, nested row position)`. It is intended to
join ordinary source origins, concrete operands, allocated Effect rows,
canonical `Capture::intern` endpoints, materialized captured Effect nodes and
exact returned owner ports. A paired symbolic-tail fixture observes memo
miss/hit, delegated tails and distinct delegated ports using the same separate
annotation and row coordinates. No numeric-position equality is used for
source-tree association.

These are provisional test-only observations. The ordinary-source joins have
not been established by execution. The existing unequal-transport assertion
is unchanged in its original test. The separately named identity observation
omits that assertion. Both invocation filters selected only the combined
identity/delegation test; the original unequal test was not selected. Previous
frozen ordinary-source runs reported identity pairs `[(19,19),(21,21)]` and
`[(21,21),(23,23)]`; those are separate bounded evidence, not evidence for
this changed test or for unequal transport.

## Invocation 1 — compile failure

Revision-1 pre-run source hash was
`2147af187b39e1b3f3e69dddb3ecfb1d9524c2bfe2009befbdcac34dbd5fee78`, handoff
SHA `c08824866ff8ddf5770a72c1bf626a679caa73c95cb6457f59517fa1efce5ae0`,
argv SHA `14de73c8a5d4b8840fcd1939e6d2d04649f3d6db4e33c8b6da8d82f656d343d6`,
and manifest SHA `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`.
The primary released this one invocation. Compilation stopped before tests ran
(exit 101) with four test-only errors: moved `complete` value, and three
reference comparison mismatches in the delegated-site assertion. No test body
ran.

Raw receipts in `/tmp/yulang-effect-permission-site-export-20261028-r1/rust-target/`:

- `rust-output.txt` SHA `a8329d2a9ed7bb9eac21b3d2288f0571c6565a61fdd746361a58a3f8916e966b`
- `rust-status.txt` SHA `39b8dc3fc8b44765c8e6f1adee04c5b465e555ab791cc42d0d9e810d5b64297c`
- `rust-time.txt` SHA `5a2d57d7b27dbe515f2a983721e6af1cc830dcbcf128bd5fb065eab6f6606e44`

Elapsed time was 34.47 seconds; maximum RSS was 1,159,624 KiB.

## Invocation 2 — test reached but owner lookup panicked

Only the four compiler-directed fixes were applied: clone `complete` before
creating the `Arc`, and dereference the three borrowed tuple members in the
delegated-site comparisons. `git diff --check` is clean. Source hash is now
`92b8a6c59f1c052a47f12c8c858fa675eaddfa83d514f6ed3e2982bb88b1a182`.

The primary released one invocation using frozen revision-3 argv
`rust-target/rust3-argv.txt` (SHA
`bec8b193cbfe70693cee8ee7d69daecbd8a0a8aed781f2cbd4a357f76b21f2bc`) and
manifest `rust3-manifest.toml` (SHA
`aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`). It
compiled and ran the single selected test
`candidate_effect::tests::formal_permission_site_export_identity_and_delegation_observation`,
which failed with exit 101 at `candidate_effect.rs:3169`. Indexing
`source_session.batch.candidate_source.schedules[&owner]` panicked because the
separately reconstructed source session has no schedule-map key equal to the
owner from the independently lowered source passed to
`CandidateInference::solve`. The panic precedes the source-tree, capture,
delegated-tail and exported-port joins. None was observed in this run.

Raw receipts:

- `rust3-output.txt` SHA `b567fa5d0be0227606a33b67c80790b3ea28a24f09591fa5da61bd8bb96e4053`
- `rust3-status.txt` SHA `39b8dc3fc8b44765c8e6f1adee04c5b465e555ab791cc42d0d9e810d5b64297c`
- `rust3-time.txt` SHA `601c5202c18136574ae122b83370d08aa51db50b0399b1741747ea1aaf328b87`

Elapsed time was 42.75 seconds; maximum RSS was 1,669,792 KiB. The two
invocations used 77.22 seconds of the 180-second shared Cargo cap. Both
allowed invocations are exhausted; no retry was made.

Revision-2's superseded 180-second argv remains preserved at `rust-target/rust2-argv.txt`
(SHA `54a674c3fd64bea90092e778cf63377fe9d02ee9a048461ef97c043025ba009b`).
The executed 145-second revision-3 argv and both manifests/raw receipt sets
remain in the exact scratch directory above.

## Outcome and remaining transition

The structural zipper and trace fields are implemented, but actual annotation
to nested-row association and the source-to-capture-to-export identity joins
remain unverified. The exact blocked transition is associating the
`FormalAnnotation` action and annotation tree to the same lowered source owner
used by the solver. The current test reconstructs an independent HIR/session;
its owner key does not index that session's schedule map. Any continuation must
preserve the exact source owner and must not infer the association from equal
positions or manufacture identifiers.

Unequal representative transport, a qualified activated copy-side Parent
write that changes this row's own chain, the original parent theorem,
source/native closure, A/B, effect hygiene, principality, termination and
production remain OPEN. No Lean theorem or independent review is claimed.
No source semantics, API, expected output, recovery or preflight changed.
Only `candidate_effect.rs` changed among Rust source leases; `candidate_scheme.rs`
remains at intake hash. New source evidence is limited by the failed test run;
no source-impossibility claim follows.

New leased handoff path:
`tasks/agent-loop/inbox/effect-permission-site-export-rust.md`. Scratch paths
are confined to `/tmp/yulang-effect-permission-site-export-20261028-r1/rust-target/`.
Next related step requires a newly bounded packet to map the exact source
annotation/action owner to the solver's lowered HIR and independently review
the frozen failure receipts. The current packet is out of Cargo invocations.
