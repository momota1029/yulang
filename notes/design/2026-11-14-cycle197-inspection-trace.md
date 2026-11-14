# Cycle197: finite successful inspection footprints

Status: proof work, no language-semantics change.

The goal is to discharge the cycle196 report-equality premise for nested nominal
patterns rather than only variable patterns. Define a finite successful trace
from the *actual* old inspector's descriptors, scalar heads, query syntax and
argument positions. A second structural certificate preserves only observations
visited by that trace. Neither condition mentions semantic Evidence or equates
whole reports.

Prove by syntax-directed recursion that the actual reinspection report agrees,
then use the existing same-model finite-tree transport theorem. Both endpoints
of a nonpoint nominal interval must be traversed. Variables do not inspect
heads and remain unconstrained. A concrete descriptor refresh must change an
unvisited observation while preserving a nominal trace, to demonstrate a
strict extension beyond the variable-only special case.

The general WF/V6 EvidenceNode is not claimed: arbitrary refresh can modify a
used descriptor, and no claim here supplies a trace or current witnesses for
every selected final node. Scope: dictionary-soundness helper only.
