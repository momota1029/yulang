# Intrusion parent ports retain polarity

Date: 2026-10-02
Status: exploratory design correction; non-authoritative
Scope: reconcile the SCC intrusion sketch with the audited Simple-sub
extrusion transition
Implementation authority: none

The intrusion sketch previously illustrated one parent per SCC variable even
though its later section mentioned polarity-indexed representatives. That
single-parent picture could be mistaken for the ordinary Simple-sub extrusion
simulation. It is now replaced with a parent-port candidate keyed by
`(ExtrusionCall, VarId, Polarity, BoundaryLevel)`. Boundary-facing occurrences
select the port using their call and polarity. Independent incoming uses apply
independent freshening maps to the ports of a fixed generation call.

The discriminator is `L(v)=[Int]`, `U(v)=[]`. Positive extrusion admits
`Int ≤ p+`; negative extrusion admits `p− ≤ Top`. Source-side propagation can
also impose `p− ≤ p+`, while `p+=Top, p−=Bottom` remains a valid pair. A shared
parent loses this pair, so one-parent-per-variable cannot claim equivalence to
ordinary Simple-sub extrusion on this input. This does not establish
unsoundness or nonprincipality of every possible successor relation; a more
compact quotient would need a separate soundness/principality theorem and an
account of the changed solution space.

The reference operation's memo table is local to an extrusion call. The
candidate map therefore names call scope; whether a successor component
persists those ports or recreates them per boundary operation remains open.
The complexity estimate is correspondingly changed from `O(V+E)` to a
hypothesis `O(P+E_P)`, where `P` counts required ports and `E_P` counts their
visited bound incidences. The relationship to graph size depends on the
unproved port-allocation rule.

This correction preserves the sketch's exploratory status. It does not prove
intrusion correctness, root-order independence, Yulang Oracle adequacy, or
effect transport. The active next work remains the unified declarative
effect/source relation and its symbolic typed-family preservation through the
SCC lifecycle.

Independent review:

- `compiler_referee`: the polarity discriminator blocks one-parent
  equivalence to the reference operation; using it to reject all successor
  sharing would overstate the result. The repaired call-scope and use-freshening
  delta review closed without remaining findings.
- `spec_auditor`: no mismatch with the non-authoritative charter; the diagram,
  maps, and call scope must consistently describe polarity ports. The only
  finding on the first delta was stale wording, corrected in the sketch.

No compiler code or tests changed. `git diff --check` passed; this note records
a research correction, not a closed semantic gate.
