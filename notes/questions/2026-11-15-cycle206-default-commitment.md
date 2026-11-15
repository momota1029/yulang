# I37: total Evidence repaired; operational commitment omits defaults

## First proposal: delay the unrestricted node theorem

Keep total semantic Evidence and its successful old204 join/default regressions,
but delay unrestricted EvidenceNode. Preserve the closed counterexample. Do not
weaken output equations, restrict selected inputs, or assume the node conclusion.
Per I34, this cycle stops after publishing verification and this proposal.

## Exact closed refutation

`GeneralDictionaryDefaultGap206Counterexample.not_evidenceNode` proves
`¬ B4SkeletonV7.EvidenceNode (GeneralDictionaryTotalBoundary206.boundary roles)`.
The separate `positive_premises` proves Checked, Initial, Reachable, an actual
model, Stable, selected key37 with empty children, and the empty child evidence.

The terminal implementation has scalar Int input at source1, no explicit body,
and role default output = positional argument0. Its named output targets a
DIFFERENT linked source0, with no fixed source head. The all-Int assignment
satisfies the default; another genuine model assigns bottom to source0 and Int
to source1/2. Both satisfy the source. Thus the output is satisfiable, and
OutputConflict is false, but it is not true in every unchanged source model.

`Committed` currently tests total packet Holds and recorded children. The packet
emitted schema has no explicit output requests here and omits the role default.
It is therefore already committed in every model with no children. Installation
is disabled as non-novel; the state is stable. No refresh can supply a head at
source0, because the bottom model witnesses the absence of a universally valid
head. Semantic Evidence correctly rejects the bottom-output model. This is an
operational commitment/effect-coverage gap, not an Evidence guard to discard.

This is a fully checked Lean boundary fixture, not a claim of a parser/runtime
surface test. No language-semantic restriction is proposed.

## Possible next repair (not executed)

Make commitment include the chosen role-default/class output effects, or add
an explicit effect-completion transition which records every requested body
(explicit/default/override) before the state counts as stable. Preserve exact
requested targets, body provenance, shared centers, ordered children and
same-model equations. Re-establish preservation, progress, termination and
classification for the changed operational boundary; merely changing Evidence
cannot make the current exact field true. Review defaults for merged requests
and already-recorded parents together rather than one syntactic guard at a time.

This changes Step/Stable/commitment beyond I37's Evidence-only successor. It is
left for a new instruction. The old-to-new migration proved this cycle is only
the named concrete terminal-default fragment, not an unrestricted conversion.
