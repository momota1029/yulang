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
