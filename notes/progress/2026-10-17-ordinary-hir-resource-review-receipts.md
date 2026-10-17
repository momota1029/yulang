# Independent review receipts: ordinary HIR resource correction

Sprint: `ordinary-hir-application-admission-implementation-20261017`, rev2.
The immutable target set was proof artifact `226d389d8fb68b6ddec328dd0f6ece4a4f3f2e344eff3f434d10b0a3d02b37ad`, proof handoff `28cc30876831203661ea237c20925249ac48ed5a9cc7fa648c36491dcb51d062`, amendment `e8b53a773675ba54f0cb5dcc4d62a993e8dd16954e0c92c58fdfc80c620d411e`, amendment handoff `23f637cdb64ef6ab237fef6dacb4abeec06bf19efa75d8f8f2d0202c09a67d80`, and sprint rev2 `8baa53c23fb83e3cdefb393b41c6d92a51aeba3c5090f4f5b52f8cc3f6f4714a`.

## Compiler referee

CLEAN within the resource/error-reference scope; 90/180 seconds charged,
requested Sol/medium, observed model/effort UNKNOWN. Verified `V=2m+1`,
`E=m+1`, `R=m(m+3)/2`; independent flat Apply slices require R physical
slots. `O(V+E+R)` construction follows when each Apply destination is
materialized once, Group forwards without copying, and disjoint child subtrees
plus unique leaf events preclude per-list dedup scans. Checked counts,
fallible reservations, final ID resolution and private publication remain
implementation obligations. All five hashes and 57 proof pins matched. No
writes, tests, builds or probes.

## Spec auditor

MAJOR authority finding, otherwise CLEAN for resource/spec scope; up to
120/120 seconds charged, requested Sol/low, observed UNKNOWN. Replacing adopted
rev4 §2's linear all-retained resource guarantee with output-sensitive
`O(V+E+R)`, worst-case quadratic, is a performance-design change requiring
explicit user approval before implementation. Syntax, flat error lists,
ordering, diagnostics, dense IDs, identities, source domain and original theorem
quantifiers remain unchanged. All five hashes and 57 proof pins matched. No
writes, tests, builds or probes. User approval later recorded in
`ordinary-hir-application-error-reference-adoption.md`.

## Pre-code architect

MAJOR authority finding, otherwise technical CLEAN; 90/90 seconds charged,
requested Sol/medium, observed UNKNOWN. Agreed explicit user approval remains
required; approval has since been recorded. Checked the same lower bound and
output-sensitive argument. Added binding implementation obligations: one
materialization per Apply, Group forwarding without cloning, checked child/R/
byte/ordinal arithmetic, full fallible destination reservations before
publication, no partial module/list or duplicate/truncated diagnostics. Measure
R and reference allocation/storage for clean and unresolved spines and Group
wrapping. Transfer accounting: implementation 1800→1710 supplies architect90;
reserve120→amendment90+reserve30. No writes, tests, builds or probes.

All three reviews were sequential and stopped before user adjudication. These
receipts validate the resource correction only; they do not certify the Astra
structural proof, source/native Call correspondence, solver behavior or parent
theorem. Original theorem conditions closed: 0.
