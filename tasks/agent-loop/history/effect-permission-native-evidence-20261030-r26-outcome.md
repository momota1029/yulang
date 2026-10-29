# R26 outcome — CLOSED_INCOMPLETE

Disposition: `CLOSED_INCOMPLETE — PREFLIGHT_REJECTED`.
Sprint: `ANNOTATION-HYGIENE-NATIVE-EVIDENCE/20261030-R26`.
Baseline: `9a74a70a32ebda716a00c7203d8e606343cf442a`.
Governing R2 amendment SHA-256: `72c9bb96cf5e651dcb8a551bbffb8ad5b2477def0d0a1ab354469cc051acdd7b`.
R2 schema raw SHA-256: `e767fb0c71752691c4ca953621105a1c7a1f4b3f5809423a71c30588d2d1a5ee` (canonical `118319c84980812e0a2bf5f5f4c968ddd4fba2fd08cdac0a65ca841510c0f9e7`).
R2 input manifest SHA-256: `2c6f136c1e498de2cfdc71a49deff4371822b0582cf5e84d411c46137c92a44c`.

## Rust candidate result

The independently reviewed R2 candidate was rejected at preflight. No compile ACCEPT, Cargo run, or runtime authorization exists. The reviewer authenticated the exact candidate and R1 archive hashes, then found three major gaps in `machine.rs`:

1. `TemplateOwnerResolution.node_index` is not joined to the immutable `TemplateNode::Owner` record for its template; another positive index passes, and the authored mutation covers only zero.
2. Outer control-chain evidence can omit all `ReceiverReturn` and `OwnerReturn` boundaries while retaining Catch records, passing through vacuous checks without proving the required connected chain.
3. The selected `OwnerReturn` mutation is conditional and changes no record on the initial capture, where that frame does not yet exist.

The dispatcher recommended `CLOSED_INCOMPLETE — PREFLIGHT_REJECTED`, no author resumption in R26, and a separately admitted continuation for any repair. Required next evidence includes exact immutable template-node lookup, required connected boundary endpoints, and mutations that prove they changed applicable records before asserting rejection. The author and reviewer are stopped. All six Rust leases remain FROZEN.

The R2 frozen files and their reviewed hashes are:

- `machine.rs`: `c232c15d5260f68e50bf45493a15f99ce053267c895e8a382e1065963d3b3a3c`
- `receiving.rs`: `dffb3fa5ce3d9437b347840e56fe5da80a143b358745f251838f66fa3065a23f`
- `program.rs`: `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907`
- `receipts/hygiene.json`: `2b8be967abbd33eb45846b3a26c4616bf58b7d60539499962f53b19a0c369577`
- Rust handoff: `5c8ad4181105873492b50c943d972c962ad171f3a869dcd046e40cde20c4fb9f`

The immutable rejected-candidate archive is `tasks/agent-loop/history/effect-permission-native-evidence-20261030-r26-r2-rejected-candidate-snapshot.tar.gz`, SHA-256 `9de55a878ad07a3488e43d59a2f0d9984baf884d786bca4f53a2b290c40ef75a`; its embedded inventory SHA-256 is `8520bf59b070a52444a1d4cd44f3d6999989255383c60f5704ab457c101106b2`. Every archived candidate member was read back and matches the exact reviewed hash. `build-target` is absent. The R1 candidate archive is preserved at `tasks/agent-loop/history/effect-permission-native-evidence-20261030-r26-r1-candidate-snapshot.tar.gz`, SHA-256 `94a81f34e37b7418809cf1b4f618e8d060f7afbd52231388649b80df938b85ef`; its inventory SHA-256 is `19e3da6112f6b24ff54a33fd84836287212fcccd2e2a9606de0855c86b271f76`.

The observer remains uncompiled and unexecuted. No Cargo, Rust compiler, tests, formatter, Lean/Lake/checker, or runtime process was run for the R2 review. Fixtures, expected outputs, manifests and runtime semantics receive no new approval from this result.

## Separate Lean result and open gates

The R26 Lean candidate remains a separately checked **conditional abstract result**: all 22 requested declaration types and complete axiom reports passed the pinned audit; only `propext` and `Quot.sound` occur. Its independent review accepted that conditional model scope. This does not authenticate the rejected Rust observer, establish native/source application, or close the parent theorem. Native/source correspondence, original A/B claims, parent proof, effect hygiene, soundness, principality, termination and production authority remain OPEN.

## Resource and stop receipt

At closeout, charged upper bounds were: Luna primary 3,000/3,600 seconds (600 remain, including a 500-second closeout reserve); Rust author 774/1,500 (726 remain); Lean 497/600 (103 remain); reviewers 428/1,000 (572 remain). Aggregate charge is 4,699/6,700 seconds. No remaining capacity is transferred to R26 or used to resume it. The live roster showed the author and referee completed, with no R26 child running. The six Rust paths remain FROZEN; unknown-path quarantines are unchanged.

The parent research goal remains ACTIVE and OPEN. Any Rust repair requires a separately admitted continuation envelope; R26 itself is closed incomplete.
