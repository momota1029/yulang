# Concrete declaration and export-root review

Sprint `concrete-declaration-and-export-root-qualification-20261016` ended
partial-reviewed under contract rev1
(`8ebeca77cdc1b3d651f613cfc5d44b8120252d9e95ff1592593a3d25cab0b961`). It
continued from baseline `46ea212940f3ec3afba5cd87e12d765fa606a342`.

## Proof lane

The frozen proof artifact
`notes/theory/2026-10-16-choose-phase-declaration-qualification.md`
(`cd03ed21dbda0be64c928bf0b09803b768e1cf0336315a1534dc44e0148fc478`) and
handoff
`tasks/agent-loop/inbox/20261016-choose-phase-declaration-qualification.md`
(`167cd06664cbbaae2eef135404f02525e10e6c3b5cd7656a9551496590aa79e1`)
received a fresh CLEAN review. All 38 direct dependency pins and the contract
hash matched. The bounded result is that the pinned inputs do not instantiate
the actual original choose clause/IF address, complete telescope, Request
gluing/action, or effective demand transport. It does not establish global
nonexistence, close a parent theorem, or authorize production. D_tail,
H1/H2/JOINT_DEC/F1/FK1/F5 remain open.

## Implementation lane

The frozen implementation handoff
`tasks/agent-loop/inbox/20261016-source-final-root-export-law.md`
(`7cc834e1c3fa627f1738b7638e6f08787c30c0d6766991061fba8f34fba48000`)
received a fresh CLEAN bounded review. All 38 direct dependency pins, the
contract hash, and the proof artifact/handoff hashes matched. Direct inspection
supports the candidate registration, root capture, fresh-use, and ordered
same-session restoration path. The selected design-level `R_e` still has no
demonstrated association to an actual HIR/source registration, candidate root,
and use occurrence. No detached displayed-scheme-plus-information extractor,
package-only consumer, or field law was found.

The reviewer recorded two low wording findings for any future successor
receipt: `ConstraintBatch::emit_candidate_source` is implemented in
`candidate_source.rs:551` (not `shadow_apply.rs`); and the falsifier about
registry lookup should name the discarded exporting session, leaving caller
environment infrastructure for fixed live anchors distinct. The reviewer did
not treat either as a substantive contradiction. The frozen author handoff
remains unchanged.

## Runtime and remaining work

Proof author, implementation author, and both fresh reviewers STOPPED. No tests,
builds, probes, compiler edits, API changes, or Git operations occurred in the
assignments or reviews. The next sprint should seek the actual declaration and
source-root instances at their owning HIR/source registration paths, then
connect those instances through the candidate root and export/use path. Keep
the proof supplier and source/export correspondence as separate obligations;
do not infer parent closure or promotion from this bounded audit.

The old UNKNOWN worker reservations remain quarantined, with no capacity
transfer. H1/H2/JOINT_DEC/F1/FK1/F5, principality, and production remain OPEN.
