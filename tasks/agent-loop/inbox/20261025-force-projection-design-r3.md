# Force source projection design — primary capture r3

Status: **FROZEN by Luna for independent spec review**. This is Luna's
structured capture of the read-only final from
`/root/force_projection_architect_r3`; it is not an architect-authored file,
an accepted representation, or a theorem.

## Provenance and dependencies

- Sprint contract:
  `tasks/agent-loop/sprints/force-projection-design-20261025-r3.md`, SHA-256
  `b9d7453a0ea6e782cbfd7f6a78e88bbb7a723546bc130a8b8990fdc6c1a56b29`.
- Worker requested Sol/medium; observed model/effort UNKNOWN. It wrote no
  files, had no descendants, and stopped. Exact elapsed time, CPU and peak
  memory are UNKNOWN; its full 300-second grant is charged.
- The worker reports all thirteen pinned file digests matched initially and
  finally. Luna independently rechecked all thirteen and confirmed they match.
  The r2 review is a final-response receipt, not a hashable input file.
- The worker ran no Lean/Lake, build, tests, Cargo/native commands or Git
  operations. Luna's later `git add` attempt failed because `.git` is
  read-only; no index or commit changed.

## Architect's outcome and invariant

The result is a **candidate representation design; correspondence is
unproved**. It proposes no semantic change and closes no parent gate.

The source decoration/representation owner constructs Force evidence; the
Control context owner preserves it through execution, suspension and re-entry.
Every represented executing or suspended View must retain its source position,
interpreted packet, typed paths, transport evidence and body/capture lineage.
Current observation comes from executing delimiters. Stored values and
suspended delimiters do not create observations merely by existing.

## Candidate source and represented configurations

Keep raw syntax/data separate from extrinsic typing so malformed Force steps
remain definable:

```text
SourceConfig =
  (declarations, immutableValueGraph, computation, concreteWorld)

SourceDecoration =
  labelled source syntax + retained derivations + finite typed templates

RepresentedConfig =
  (declarations, immutableValueGraph, rawHead,
   executingFrames, concreteWorld, segmentBoundary, literalSuffix)
```

`SourceConfig` is the paper's independently specified machine, not a relation
defined by represented successors. `SourceDecoration` records the paper's
decoration construction and does not assert execution safety.

Required data responsibilities:

```text
TypedPacket:
  value-view identity, underlying graph reference/value, type descriptor,
  interpretation substitution, provenance

DelayPayload:
  source introduction label, body code label and code,
  captured bindings with original packets and slots,
  retained body derivation, latent force graph,
  interfaces connecting captures/body/result to the value graph

ForcePlan:
  static Force label, forced packet, current owner,
  resolved DelayPayload,
  force.effect and force.result typed paths,
  effect and result interface correspondences and source derivations

ViewSpec:
  source label, packet, effect path, result transport specification,
  interpretation substitution, lineage

ExecutingViewFrame:
  fresh dynamic occurrence, ViewSpec, saved outer ambient

SavedViewFrame:
  ViewSpec and capture binding information
  -- no capture-time outer ambient to restore on resume
```

These are record responsibilities, not finalized Lean declarations. Dynamic
View identity differs from both the static syntax label and value-view identity.
Typed paths include structural labels, semantic ports, type/template nodes and
instantiated parameters. Add distinct `forceEffect` and `forceResult` ports.
Replace unrestricted `PathRule.adapterMap` evidence with derivations from
actual finite source transport templates: identity, prefix insertion/removal,
fixed terminal-port pairs, composition, and the selected adapter's declared
correspondence. Equal endpoint types create no edge.

## Candidate projection and transition equations

Define `pi` by structurally decomposing the paper configuration: follow its
unique active computation; reify source frames with their packet,
interpretation and decoration; copy concrete history and executing/search/saved
context distinctions; retain the entire literal suffix at the segment
boundary; and translate source result constructors directly. Fresh identities
are copied from source allocation. A deterministic allocation convention is
optional representation policy; otherwise commuting claims are equivariant
under fresh renaming. Projection is independent of Call typing; typing becomes
an additional theorem about projected states.

For suffixes, extend represented `Frame.view` to retain complete View data and
preserve the suffix list literally during segment-local transitions. Its
erasure can keep the existing `.view identity` list. An old arbitrary suffix
with only IDs cannot be upgraded from `FramesTyped`; its producer must supply
the omitted source data. This is a correspondence obligation, not permission
to restrict source programs.

Let `C` be the executing context, `A(C)` its ambient observation packet, and
`P(V,w)` the View's potential incidence interpreted in concrete world `w`.
The candidate equations are:

```text
resolveH,theta(v) = Delay(M, captures, graph)

C[Force_ell(v)]
  -> C[View_j(v, force.effect, M)]
```

The result-path specification stays with the delimiter. `j` is fresh, owner is
inherited, and Force allocates no receiver. Resolution follows references,
wrappers and type interpretation without executing latent children; keep
administrative resolution steps explicit where the paper counts them.
Formation consumes the retained derivation of `v : U A`, resolved Delay
introduction, captured packets and intervening source transport derivations.
It constructs separate body-effect and body-result interface connections,
including descendant latent paths rather than only endpoint type `A`.

```text
enter(V, A):
  push ExecutingViewFrame(j, V, savedOuter=A)
  ambient := A union P(V,currentWorld)

leaveRet(frame, Ret w):
  ambient := frame.savedOuter
  Ret transportResult(frame.ViewSpec, w)
```

Saved-ambient union/restoration follows the paper (`1352–1356`). Result
transport uses finite Flow templates and a fresh output value-view, preserving
the underlying value and transported latent ports. For Force, correspondence
uses the thunk's `force.result` subtree, distinct from observing
`force.effect`; body-produced result provenance remains attached.

**Unverified formalization inference:** the exact combined Force result
Flow-row construction must be checked against the paper's generic return and
projection transport rules before any Lean constructors are frozen. The paper
specifies a separate result transport but does not print a standalone
Force-result row equation. Do not replace this obligation with an arbitrary
result callback.

Actual emission is defined at the emission context:

```text
C[perform_o,T(p)]
  -> C[Req(q,p,cont(empty,x.Ret x))]

q.observations :=
  [Observe(q, interpretedPacket(V), effectPath(V), occurrence(V))
   | V is executing in C]
```

Traverse the whole executing context, including Views outside handlers and in
the literal suffix. Capture-time or stored packet lists are not substitutes.
Bubbling preserves this immutable event packet and adds no observation.

```text
View(V, Req(q,p,K))
  -> Req(q,p, appendSavedView(K,V))
```

`appendSavedView` retains the View specification, result transport, typed
paths and binding provenance; it suspends the delimiter and structurally
restores the surrounding executing context. It is not normal result transport.
Captured frames retain actual nesting order. Handler selection determines
the cut: the selected handler and its outer Views stay outside the selected
continuation; forwarded requests retain their handler as prescribed by the
paper. Preserve the complete literal suffix through segment-local bubbling
until its own rules execute.

Resume:

```text
K = cont(B,x,N)
rho = fresh injective renaming of B, fixing free names
Resume(K,a) -> (rho · N)[a/x]

A0 := currentResumerAmbient
Ai+1 := Ai union P(rho · Vi,currentWorld)
```

Interpret captured packets and future reads under the same scoped substitution.
Rebuild each executing frame's saved ambient from the current `Ai`; allocate
fresh dynamic occurrences per execution. Never restore capture-time outer
ambient. Control-name substitution acts on bound owner/handler occurrences in
code, profiles, receipts, View specifications, saved packets and future reads.
It fixes free ambient names, family identities, State scopes, shared resources
and type arguments as the paper prescribes. Static labels stay fixed; dynamic
View freshening is separate.

Failure equations:

```text
resolveH,theta(v) has a non-Delay constructor:
  C[Force_ell(v)] -> C[Bad malformedForce]

F[Fail r] -> Fail r
F[Bad r]  -> Bad r
```

Apply these for each active-child frame. Neither outcome uses normal result
transport, emits an event, or becomes the other. Represent terminal failure
without an observable executing-context projection; invent no failure-world
restoration. Preserve raw resolution errors as their own Bad cases.

## Producer/consumer mapping

| Producer | Retained fields | Consumer / required change |
|---|---|---|
| Source decoration | Static labels, complete port templates, licensed correspondences | `CoreSyntax`: richer Force syntax and path evidence |
| Delay introduction | Body/capture derivation and graph interfaces | Force formation; preserve through wrappers and aliases |
| Value transport/read | Packet provenance and interpretation | Force resolution, result transport, capture and later reads |
| View entry | Fresh occurrence, ViewSpec, saved ambient | `ControlSyntax`: concrete entry/return/capture rules |
| Source context/suffix construction | Every View payload and frame typing | Replace ID-only suffix conversion and `suffixViewMatch` |
| Perform | Actual-context immutable observation packet | Handler search; no recomputation while bubbling |
| Capture | Literal frame order, bound/free classification, saved View specs | Resume formation and coherent re-entry |
| Scoped substitution | Interpretation action across captured fields | `CoreSubstitution`: separate from term-variable renaming |
| Raw computation | Distinct Fail/Bad constructors | Add Call Bad head and child propagation |
| Source typing | Body, frame, suffix and transport derivations | `ControlTyping`: strengthen coherence separately from raw steps |

`ControlComposition` needs corresponding preservation/progress cases and revised
View behavior. `CoreControlBridge` remains limited to its established Original
fragment; it cannot supply wrapped Force provenance. `CoreExecution`'s bare
Original Force rule is not the complete decorated Force rule.

Required correspondence diagram:

```text
paper source configuration  --paper rule-->  paper successor
             | pi                              | pi
             v                                 v
represented configuration --concrete rules--> represented successor
```

Prove it by source-rule cases and structural context decomposition. Independently
prove successor coverage by inversion on represented raw constructors. Recover
the paper configuration by plugging retained frames around the head; establish
`plug(pi(s)) = s` up to explicitly chosen administrative decomposition and
fresh-name equivalence. These are obligations, not results of this packet. A
represented step defined only as “some source step projects here” hides the
executable equations and is rejected.

## Adversarial cases and unresolved decisions

- Nested returned thunk: result transport retains latent graph; creation and
  return do not enter a future Force View.
- Shared witness across outer/inner Views: saved-ambient restoration retains
  the outer witness.
- Outer View across a handler: emission sees it before search; capture does not
  incorrectly put it inside the selected continuation.
- Repeated resume under different ambients: rebuild saved ambient chains per
  run; freshen bound names and executing occurrences, fix free ambient names.
- Fail, malformed Force Bad and child Bad: preserve outcome/reason and bypass
  normal return transport.
- A name shared by saved and ambient packets: rename only saved bound
  occurrences; global destructive renaming fails.

These are design checks by inspection, not executed tests. Remaining decisions
for Luna are rich View payload layout, administrative-step accounting and
fresh-name presentation. The exact Force-result Flow-row equation needs source
checking; the architect asserts no observable semantic choice. If the paper
allows different observable behavior, stop at that equation. Reject the
candidate if a required transition cannot be computed from retained fields or
if transport creates a path unlicensed by source derivations.

Required next gate: fresh `spec_auditor` checks all equations, field mappings,
the generic Force-result Flow row, suffix completeness, Bad/substitution cases,
and the executable correspondence obligations. Only after review and Luna
adjudication may a new implementation grant be frozen. F
`force_plan_formation` and P `force_context_projection` remain proposed
successor propositions, not issued claims; S/C, Call A/B, native correspondence
and the full parent remain OPEN.
