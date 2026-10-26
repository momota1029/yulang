# Independent review: selected pre-merge association observer

Status: scoped PASS; instrumentation and recorded evidence only.
Reviewer: `/root/original_recursive_closure_r3`, independent of this extension's
author (`/root`). Review window: 2026-10-26 17:04:49--17:06:29 UTC,
approximately 1 minute 40 seconds within a 12-minute bound. The reviewer
performed no writes, builds, inference runs, Git operations or child delegation.

## Frozen reviewed patch

`notes/theory/fixtures/2026-10-26-native-association-observer.patch`
is 3,154 bytes, SHA-256
`890fdc94090809ae33c0af93b4bccd7f0cd22447aad2752dea1c02c975a0231c`.
The saved private before-files match the previously reviewed observer:

- Context: `2689160a5b130f9b3c69e5a8053d95feaa51b8f5968bd8445ba342863168e7d7`.
- Intrusion: `af3e33b3429cf897c218967d8347b6126387e9023d669b285cd706579f94bf7c`.

The differences from those before-files are exactly the patch's two file
hunks. The extended source hashes are respectively
`0c7eb06e357fbb57e2e10ce3d308ed6dace5c07a0c4bd1b534f2e34fea57517a` and
`3cecc6455588e79873fbc2b613eacdbfe38c5c8119441b2bfbcd539ceb45a868`.

## Findings and scope

No solver-state mutation, constraint change, inference-decision change or
error-export bypass was found. Parent/source/Graph/context/evidence lookups use
immutable references. The readout precedes representative checks, journal
writes, bound copying and row mutation at the selected merge. The production
`shadow_apply.rs` remains byte-identical, including conflict rejection by
`ArtifactMismatch` from successful intrusion/graph exports.

One scope correction was raised and accepted: the patch dumps parents 0--4
and relations 0--67, not the entire unknown context. It does not print total
counts or a completeness claim. Its one Graph Debug value is unfiltered.
No rerun was needed for this selected-prefix result.

The 337 selected lines contain five parents, one Graph, 68 relations,
105 dependencies, 33 origins, 63 admissions and 62 emissions. No printed
RelationId points outside the printed prefix. All 62 emission admission
references resolve to printed admissions. This is syntactic evidence closure,
not semantic source-incidence authentication.

The reviewer filtered the combined stderr directly. Its 1,404 PROOF_TRACE
lines reproduce SHA-256
`3d8e9aab2c3339efd6ab22059284919e6863bfc057a0201fa0a9e44175df744d`;
its ASSOCIATION lines reproduce
`cdceaf656e6100e3361d344bf9f927bf43925099c2077b3e3c654ac585765d36`.
Combined stderr SHA-256 is
`8a52c0817b0201b4f5262aad61631c0a8b717c2f8b6a0dfe4986f8cc5222cf29`.

The recorded run is observer exit 0, 0.372 s, no timeout/cutoff, one Int/Bool
conflict and seven source Calls. The initial build failure was preserved
(exit 101, 4.796 s, wrong `self.candidate_source` field). The final build uses
`self.batch.candidate_source`, exits 0 in 8.877 s, and has log SHA-256
`a4226663135b05e178c9a27810b77d0be2deeaec679e940407e962910a332126`.
The run receipt SHA-256 is
`a9d259750d8c1b495fffb1f0e9e85910e8abc5f7aa1d3474cf7e7e658e01c503`.

No original signed association, source typing, whole principality or termination
claim was part of this review. The accompanying observation note records these
same evidence boundaries. Raw evidence remains outside Git. Review does not
authorize applying the patch to production.
