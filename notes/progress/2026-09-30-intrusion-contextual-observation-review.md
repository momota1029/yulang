# Gate C contextual observation relation candidate

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Classification: reviewed unselected proof-interface candidate; no implementation authority

## Candidate relation

The abstract-semantics draft now proposes a contextual operational comparison
for a complete source-induced continuation `K`. Source events include
constraint-producing forms, ordered member-root preparation, incoming uses,
component publication, and final module observation. Constraint source events
are lowered separately by Oracle and intrusion; TypeVar IDs, evidence IDs,
weights, and origins are not assumed to be identical inputs. Well-formed runs
prepare every member in Oracle order, publish only after all member results,
and instantiate external uses after publication. Prefixes support step
simulation only; the public result is observed on a completed run.

Each execution returns an internal transition trace and a separately projected
public result. The trace records projection attempts and retries, evidence
decisions, latches, gateway escalation, default-root fallback, event routing,
use insertion, and publication. An attempt-local error or round latch is not
itself treated as a terminal public outcome. The public observation retains
success/failure, ordered observable diagnostics and locations, and exported
module observations, subject to an unresolved normalization contract.

The proposed parity criterion quantifies over every supported complete `K`
from paired states satisfying the root-indexed state relation. Oracle and
intrusion must produce equal normalized public observations under one identity
correspondence that fixes shared anchors and consistently renames fresh local
identities per use. Internal traces need only correspond through the root/use
simulation; they need not be equal. Positive/negative bound reachability at
requested use roots and shared anchors is retained only as optional debugging
evidence. Graph isomorphism is not a required parity condition because the
charter targets Oracle-observable behavior, not a particular internal graph.

## Independent review and repairs

An `architect` review recommended this rooted contextual shape to cover later
constraints, failures, and use behavior without selecting a type carrier. It
also found a wording conflict between an “immutable shared component graph”
and sequential root epochs; the draft now says each root attempt reads an
immutable selected input while later attempts may start from newer solver
states. It also distinguishes terminal projection failures from nonterminal
attempt errors and Oracle fallback continuation.

The first `compiler_referee` review found that the initial event alphabet
omitted later constraints/interleavings and conflated internal projection
errors with public outcomes. The first `spec_auditor` review found that
mandatory bound-graph isomorphism would impose an unapproved representation
constraint. The draft was revised to use source-level events with
machine-specific lowerings, complete contexts ending in module observation,
separate internal traces/public observations, explicit publication/use order,
and optional graph witnesses only. A focused delta review by both roles closed
those findings with no new blocking or major issue.

## Remaining Gate C obligations

This is a proof interface proposal, not the theorem. The exact supported source
and event alphabet, source-to-event map, paired initial-state relation, and
machine lowerings remain undefined. Public type/interface normalization and
which diagnostic fields are externally observable also remain unresolved.
The draft does not prove contextual parity, source lowering equivalence,
root-step simulation, use-event simulation, solver adequacy, soundness, or
principality. The carrier and recursive subtype preorder remain unselected.

No tests, measurements, or compiler changes were made for this design slice.
The focused Rust Oracle interval tests from the previous slice are separate
characterization evidence and do not close this relation. Gate C remains open;
the next work is to fix the supported source/event envelope and observation
normalization, then prove the source lowerings and ordered root/use simulation.
