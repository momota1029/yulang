# Cycle197: journal soundness across mixed actual executions

Design: recover semantic packet Instances from installation events in an actual
WF execution, even when ordinary-context growth and same-slot nominal refreshes
are interleaved. Do not introduce a new operational semantics or assume final
packet installability. Extend the earlier ordinary-only journal induction.

## Exact scope

`GeneralNominalMixedJournal197.MixedStep` is the conjunction of the unchanged
actual `boundary.Step` with a context classification. Its first arm is the
existing exact ordinary `Extension`. Its second arm is a same-slot `View`, an
actual source-preserving `Refines` certificate, and the old registry's nominal/
variable-only query syntax. No arm contains Evidence or report equality.
`steps` explicitly erases the classification to an actual WF execution.

For every finite mixed path from `initial context root`, every packet in the
final journal, and every model of the actual final state, `packet_instance`
constructs its current Instance with the same occurrence, declaration key and
complete child list. Actual install steps supply fresh packet instances; old
packets are preserved through both context-update arms. Thus callers provide no
source-instance or final-Installable premise.

`recorded_tree_sound` gives complete-payload semantics for any finite tree of
actual recorded packets. `uniform_dictionary` additionally uses explicit final
journal coverage and accessibility to choose a complete model-independent tree,
then proves it sound in every final model. Coverage/accessibility remain open
for arbitrary stable executions; this is not the general EvidenceNode theorem.

`universal_evidence` separately transports already available whole dictionaries
along such paths from arbitrary starting states, allowing model-dependent source
witnesses. This supports a minimal concrete nontrivial execution regression.

## Concrete mixed path

`GeneralNominalMixedExample197` has two genuine WF steps: enqueue the root into
an explicitly unqueued source state, then perform the previously certified
nominal descriptor insertion at slot0. The first step changes the site journal;
the second changes the nominal table. `real_changes` proves both changes and
`actual_path` proves the unrestricted WF path. `inhabited` provides an actual
common assignment and the complete nested-nominal final payload. No semantic
transport premise is assumed for the fixture.

This fixture is deliberately **not** claimed to start at the canonical initial
state, nor to prove Initial/Reachable. Its journal contains no installed packet,
so it exercises the mixed classification and nonvacuous evidence transport, not
a concrete instance of the general installation-recovery theorem. The latter is
proved for all paths from actual `initial` by induction over real step witnesses.

No changes to the actual relation, language specifications, existing files,
state constructors or target boundary were made.
