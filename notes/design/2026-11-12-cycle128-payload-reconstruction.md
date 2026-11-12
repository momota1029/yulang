# Cycle128: reconstruct source obligations from raw dictionaries

Status: Draft implementation contract. Scope: I-18 item5 only.

The input is one root occurrence, a raw selected-key dictionary, and the existing
resolved frames. Each node uses the checked visible declaration lookup to compute
its complete canonical child occurrences. A simultaneous list traversal rejects
both missing and extra raw children. It never truncates a zip or invents a child.

The independent judgment is the existing PayloadEvidence of the actual Plan
relation. The target is: for every checked registry, frames, root, payload and
source tree, reconstruction succeeds with that tree iff the tree reads back the
same root/payload and has Plan Evidence. The output is consequently unique.

Next, compose reconstructed source trees with the existing variable materializer.
For every successful preparation, the raw payload is preserved and one fixed
source witness works in every model of the recorded whole batch. This reduces
manual recipe inputs; it does not discover selected keys, frames, readiness,
allocator provenance, or model existence. A failed materialization is deferral,
not language rejection. The general B4 evidenceNode field remains unfilled until
candidate/model bridges exist. No Astra candidate or driver definition changes.

## Full nominal model extension after fresh integration6e1e848

Astra's new CommonBridge interprets the same recorded ordinary state in the full
nominal carrier. Dictionary equations can therefore quantify over arbitrary
nominal assignments rather than only the Common image. The variable-pattern
compiler remains unchanged; its source variables may denote genuine nominals.
A constant nominal73 fixture checks that this extension is nonvacuous.

The dictionary-only recording adapter also targets GeneralNominalState by
lifting local atoms through the separate type/row source maps and appending them
to the full state's global ordinary list. It retains base/view/descriptors,
source ownership and reserved identities. Its exact model law is conjunction of
the original full-state Models and every dictionary equation. This is an
explicit finite dictionary transaction, not Step, candidate selection, new
allocation, model existence for arbitrary input, or source stabilization.
Item 5 candidate-readback adapter

For each root/key, find the actual visible declaration with matching role, then reuse the existing nominal argument lookup and inspection report to obtain bindings. Build a per-root dictionary frame with per-key captures, retaining the nominal allocator's exact allocation and source identity functions. Empty bindings on absent lookup/arguments are only a total-function fallback; the Survivor-to-Plan proof establishes that neither absence applies.

A checked registry makes the selected declaration unique. Existing Survivor premises imply the computed Plan with exactly the original candidate children. Mapping finite indexed or raw PayloadEvidence through this implication permits executable reconstruction without caller-supplied Frames or descendant occurrences.

This does not establish existence of a complete candidate-evidence tree, run recursive candidate search, prove materialization success, or construct general B4. Existing Survivor readiness, root-output, freshness, consistency, coverage and emission restrictions are preserved as premises, not weakened.

## Same returned witness across candidate and source evidence

For a fixed nominal Context and raw payload, independent recursive Survivor
Evidence plus successful supported-variable preparation implies that the actual
returned dictionary is the same candidate witness. Its original raw readback,
existing candidate evidence and arbitrary-full-model source Instance all hold
on one fixed tree. The full nominal recording preserves original Models.
This conditional theorem keeps both premises explicit; it supplies neither the
candidate forest nor successive child contexts nor materialization completeness.

## Combined-premise nonvacuity

A dedicated checked singleton registry uses a terminal variable head at known
source interval `(1,1)`. Its actual existing Survivor, raw candidate evidence,
computed-frame preparation success and concrete full transaction model all
hold together. The joint theorem returns one Readback witness carrying both
candidate and independent nominal source evidence. No candidate guard changed.
