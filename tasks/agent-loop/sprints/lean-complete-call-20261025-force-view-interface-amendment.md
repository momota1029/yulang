# Call Force/View source-to-interface gap packet

Status: **FROZEN by Luna as a research/input packet**. This document records a
formalization gap and a concrete continuation gate. It does not change Yulang
semantics, grant implementation authority, or close any proof.

## Target obligation

Before defining an independent raw Call machine or dispatching
call_step_erasure / call_raw_successor_coverage, represent the source evidence
needed to execute a Force on a View-wrapped thunk. The representation must
retain distinct Force effect and result positions and the construction that
relates them to the observed thunk. It must also let the consumer preserve that
exposure through normal return, Req suspension, and the source-defined
Fail/Bad paths.

The admitted syntax is not narrowed. Endpoint type equality, absence of a
transition constructor, or a trace condition cannot stand in for this input.

## Frozen source evidence

- docs/yulang-operational-type-safety-ja.tex, SHA-256
  a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b.
  - §12.3, lines 303–307: Force(Delay M) → M; a raw term missing the
    constructor required by a reduction rule goes to Bad.
  - Lines 331–335: an active child step is lifted through expose; child
    Fail/Bad propagates as that same result.
  - §12.4, lines 468–470: a Scope crossed by Req is saved and reconstructed;
    suspension is not normal return.
  - Lines 485–494: expose decorates requests, stores remaining exposure in the
    continuation, decorates normal results with result-path metadata, and
    Force/Call execute their body under expose.
  - Lines 515–520: observations use every currently executing View, including
    Views outside an intervening handler.
  - §12.33, lines 1231–1236: syntax nodes have static labels distinct from
    dynamic owner/View-occurrence/activation identities.
  - §12.45, line 1245: Force has force.effect; normal results use a separate
    force.result transport.
  - §12.52, lines 1531–1533: Delay retains the body graph for future force;
    Force re-observes that graph in the current diagram and connects View
    entry, body, and View exit without conflating effect/result.
- notes/design/2026-10-02-typed-boundary-realization-draft.md, SHA-256
  1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb.
  Its status is Draft and it grants no implementation authority for full source
  realization. §§388–415 distinguish a complete-call view from a force view,
  identify p_force as the forced thunk's current effect position, and leave
  elaboration of executable typed views from raw source—including demanded
  forces—as an explicit input obligation. §§441–460 require saved inner View
  scopes to retain their typed packet and port on suspension/re-entry.

## Producer obligations

The source/decorating producer for each executable typed Force must provide
evidence for all of the following:

1. The Force syntax node's stable source label and the current observed thunk
   graph/body selected at this execution.
2. A source-owned force.effect position and a distinct force.result
   correspondence, with their types and component paths.
3. The rule mapping the observed wrapped value's existing paths to those two
   Force positions. The rule must identify its source construction; an
   arbitrary PathRule.adapterMap or equal endpoint types do not establish it.
4. The dynamic View occurrence identity and current owner/world inputs needed
   when this Force is actually executed. Do not reuse the static label as a
   dynamic identity or activate latent positions merely because they are
   present on the value.
5. The force body's retained typing derivation and thunk capture data, so body
   execution is the source body under the present execution context.

The source fixes the required distinction and current-position re-observation.
The exact Lean data constructor or record that transports this evidence remains
to be frozen by the next versioned contract after the producer is identified.

## Consumer obligations

The Force consumer must be independently defined from the raw computation
semantics, not from CallControlStep or a typing premise. Its cases must:

1. For a valid thunk, enter the actual delayed body under the active
   force.effect View and preserve the existing Call owner, active context,
   world, operation instance data, receipt/metadata state, and literal typed
   suffix.
2. On normal return, perform the separate force.result transport and leave
   precisely the Force View occurrence. The source requires effect and result
   positions to remain distinct.
3. On Req, attach event-time observations for all active Views and save the
   Force exposure/continuation state needed to resume. Do not treat suspension
   as normal return or drop a Call View outside an intervening handler.
4. On Fail and Bad, retain the source distinction and the exact source
   propagation rule. Do not silently apply an arbitrary cleanup relation as a
   source law. If a world effect on these paths is not specified by an
   accepted source rule, record that premise as OPEN.
5. For malformed raw Force (including a non-thunk constructor), produce the
   source-required genuine Bad outcome. Typed-image coverage must then rule
   it out from substantive typed canonical-form premises.

force.effect activation, world updates on entry/exit, and Force-view cleanup
must be checked against the accepted source owner before their Lean operations
are frozen. The current core's general viewReturn, suspendView, and
underspecified failWorld fields are not by themselves a Force-specific
producer/consumer contract.

## Existing representation gap

The final r9 candidate hashes are recorded in
tasks/agent-loop/sprints/lean-complete-call-20261025-r9-outcome.md.
Relevant current shapes:

| Type/field | Current data | Missing Force input |
|---|---|---|
| TypedCall.PortPath | component labels, PortKind, type | source-owned Force effect/result path construction |
| TypedCall.ViewOccurrence | dynamic identity and one path | distinct effect occurrence and result correspondence |
| TypedCall.Comp.force | one Value | Force source label/decoration and Force plan evidence |
| TypedCall.Comp.expose | effect View, result View, body | construction-directed pair from the forced value |
| TypedCall.CallView | call owner, receipt, carrier/interface/adapters/captured Views | Force-specific evidence for body Forces |
| CallState | world, head, frames, callView, contexts, literal suffix | Force-entry state/observation derivation |
| Metadata | scope/view return and suspension, cross release, eligibility, generic failWorld | accepted Force-specific entry/exit and failure behavior |

In the r9 candidate, forceDelay and forceEmbeddedOriginalDelay enter bodies
without installing Force exposure. There is no successor for
.force (.view thunk occurrence). enterExpose, returnExpose, and requestExpose
can consume a supplied pair; they do not prove where the pair comes from.
returnExpose transports the result occurrence, while requestExpose retains the
effect occurrence. Their correctness for Force depends on the missing producer
evidence and the source-owned lifecycle rule.

## Determined behavior and open input

The accepted operational source determines that Force of a delayed body enters
that body; a required missing raw constructor is Bad; Force uses the current
diagram; a Force View is active around its body; normal result metadata follows
the separate force.result path; and a Req retains active exposure and typed
continuation state. Fail and Bad remain distinct and child failures propagate
as the same result.

The current evidence does not identify a concrete executable decorator
constructor that creates the force.effect / force.result pair and proves their
mapping for every View-wrapped thunk. It also does not license a new
Force-specific world-update or failure-cleanup policy. This gap is therefore
OPEN source/formal correspondence, not an inconsistency or counterexample to
Yulang.

The source owner packet must answer:

- Which source-typed node/decoration record carries p_force and its separate
  result correspondence?
- How does current-world re-observation produce the dynamic Force View
  occurrence from the wrapped thunk without losing path/owner data?
- Which exact existing source transition implements View entry and exit on
  Ret, Req, Fail, and Bad, and which world effects are identity/context-stack
  changes versus explicit World changes?
- How does the producer prove the pair's source correspondence, including
  nested/captured View-wrapped thunks and arbitrary typed suffix preservation?

## Next continuation gate

Luna should freeze a separately versioned representation contract only after
the source owner evidence answers those questions. That contract must assign
disjoint Force-plan implementation, S simulation, and C successor-coverage
leases; pin the producer, consumer, and all dependency hashes; retain the full
source domain; and require serialized Lean checks before either proof lane
starts.

An independent falsifier is a source-admitted View-wrapped thunk whose
force.effect exposure or force.result transport cannot be derived from the
decorated typed source without fabrication, conflation, or loss of its event
observation, continuation, owner, world, or literal suffix.
