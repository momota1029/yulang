# Cycle163: finite selected packet coverage and I26 settlement

Status: proof design, no language change. Fresh I21/I24/I25/I26 apply.

The remaining JointClosure theorem concerns semantic Evidence. I26 additionally
uses an inductive ledger discharge. A classified finite dictionary alone does
not discharge its packet children (cycle162 recursive counterexample).

Define PacketCoverage on the selected descendant graph: every selected node has
an actual recorded packet with exactly that occurrence and selected child list.
No settlement or semantic Evidence is assumed. Induct on the finite classified
dictionary to derive actual Discharged, then PacketSettled for matching packets.
Use the existing trusted-input/readback rule and output fact membership to admit
output facts. This is a conditional finite ledger criterion, NOT a proof that
ordinary reachable/stable states automatically contain all terminal packets.

Independent worker scope: packet-free Joint closure and actual generated consumer.
Existing state/guard/Step/Stable definitions remain unchanged. New modules are
imported by Yulang.lean; small separate audits, no frozen Audit/README edits.

## I20 alias extension

Exact occurrence coverage is too restrictive when an existing recorded site is
reused through Alias. AliasCoverage instead records a concrete packet, its exact
children, the two site memberships and an actual Alias between occurrence IDs.
Finite selected-tree induction constructs Discharged using packet/alias rules;
no semantic Evidence or discharge proposition appears in this structural cover.
