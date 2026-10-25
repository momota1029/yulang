# Force source-interface review input — primary capture r2

Status: **FROZEN by Luna for independent spec review**. This artifact records
the read-only final response from `/root/force_source_interface_architect_r1`.
It is Luna's structured capture, not an architect-authored file and not an
accepted Lean interface.

## Provenance and assignment

- Sprint: `FORCE-SOURCE-REALIZATION-20261025/r1`.
- Frozen contract: `tasks/agent-loop/sprints/force-source-realization-20261025-r1.md`,
  SHA-256 `fcbf06e2823c9781361cb62c31818c933faac2ae81dddb963bb89d3eb863b460`.
- Worker: `/root/force_source_interface_architect_r1`; requested
  `gpt-6.1-sol` / medium, observed model/effort UNKNOWN.
- The worker followed its higher-priority read-only role, wrote no file, had no
  descendants, returned its final response, and stopped. Exact elapsed time,
  CPU and peak memory are UNKNOWN; the full 300-second grant is charged.
- The final response stated that all twelve pinned inputs matched on initial
  and final revalidation. Luna independently recomputed all twelve hashes
  below. The response printed the r1 contract digest with an embedded space;
  the corrected actual digest is recorded above.
- No Lean/Lake, build, test, Cargo/native command, or Git command was run for
  this assignment.

## Pinned inputs revalidated by Luna

| Input | SHA-256 |
|---|---|
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` (Draft only) | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `tasks/agent-loop/inbox/20261025-force-view-source-producer-investigation.md` | `90506b6c8cf98487690550b95255e37806a79ab527646d1bf12192dfb82dfc1c` |
| `tasks/agent-loop/sprints/lean-complete-call-20261025-force-view-interface-amendment.md` | `8d7ad0d788d559d5efa3e7b75953221d8a7bd9586ffe09ac1f705fe6a3862406` |
| `notes/theory/lean/YulangClosure/CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `notes/theory/lean/YulangClosure/ControlSyntax.lean` | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| `notes/theory/lean/YulangClosure/ControlTyping.lean` | `e52aaca8baa5c3312a200952ef07fa7e304686d2642c154831de0365646a497f` |
| `notes/theory/lean/YulangClosure/ControlComposition.lean` | `9a48a5f2ef15eb947478757e0fa74457579183ccdbab90f2518886590e33fc40` |
| `notes/theory/lean/YulangClosure/CoreControlBridge.lean` | `30a0007aea313eccc42531bf346891c010dbed7b4b34cea1aebe7043a9a6d99a` |
| `notes/theory/lean/YulangClosure/CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `notes/theory/lean/YulangClosure/CoreSubstitution.lean` | `fc73d6d60d28f2abb54049a5715751d27df47ad93dbeb8f52966cf98a747bd2f` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |

## Captured source equations

The equations below are the architect's reported interface obligations, copied
as mathematical notation rather than proposed Lean declarations.

Let `ell` be the stable Force syntax label, `v` the current wrapped value,
`M`, `Gamma_cap`, and `G` its retained body, captured packet and latent graph,
`pE = force.effect`, `pR = force.result`, `j` a fresh executing View
occurrence, `C` the current context, and `S` the literal typed suffix.

1. Resolve the underlying value without evaluating latent children:
   `resolveUnderlying(v) = Delay(M)`. The static label `ell` and dynamic
   occurrence `j` have different roles; Force introduces no receiver owner.
2. The retained typing derivation supplies body/result types and graph/capture
   lineage. The current diagram, not Delay creation activity, supplies Force
   execution activity.
3. Expose the effect port as `View(v, pE, M)`. Separately transport the normal
   result through `pR`; the source correspondence has explicit terminal-port
   pairs such as `a · s -> b · s`. Endpoint type equality creates no edge.
4. For outer ambient packet `A` and this executing View contribution `Pj`:

   ```text
   enter:       savedOuter = A; ambientInside = A ∪ Pj
   normalLeave: ambientAfter = savedOuter
   ```

   Set subtraction is invalid when enclosing Views share witnesses.
5. Observe an event only when the occurrence is executing in the emission
   context: `Observe(q,v,p,j) iff View(v,p,...) with occurrence j is executing
   in Cemit(q)`. This includes Views outside intervening handlers. Bubbling
   creates no new event.
6. Capture retains crossed inner Views and the remaining computation. Resume
   adds them to the **current resumer context**, under coherent name
   interpretation and fresh executing occurrences; it does not restore the
   captured outer ambient over the current one.
7. `Fail r` and malformed-Force `Bad r` propagate as themselves. A Force whose
   interpreted underlying constructor is not Delay yields Bad. Neither takes
   normal result transport. No additional failure-world operation follows.

Source anchors: operational paper §§ ordinary transitions and Bad/Fail
(`303–335`), current-context observation (`515–526`), source decoration and
Force ports (`1186–1257`, especially `1245`), concrete context representation
and saved-ambient/resumption rules (`1296–1388`, especially `1352–1386`), and
retained Delay graph/current Force re-observation (`1531–1532`). The draft is
not authority for an encoding choice.

## Captured missing projection and owner

The architect reports that the current Lean representation has no concrete
projection

```text
pi : SourceMachineConfiguration -> RepresentedExecutionConfiguration
```

Its required Force-entry equation must compute from the source configuration
and retained typed derivation:

```text
pi(C[Force_ell(v)], S)
  -> pi(C[View_j(v, force.effect, M)], S)
```

The construction must carry the derived body/capture lineage, distinct result
transport, fresh `j`, current owner/context, saved ambient packet and literal
suffix. Ret, Req/re-entry, Fail and Bad equations must come from that same
projection. The named owner is the source elaboration/representation bridge,
coordinated with the Control context representation owner. The architect
classifies this as a representation definition absent from the current Lean
record, not an unresolved Force meaning.

## Luna's checked Lean inventory

The following are direct observations of the pinned files; whether they prove
the reported gap is the reviewer’s question.

- `CoreSyntax.lean:208–221`: `PortKind` has `carrier`, `callEffect`, and
  `result`; `ViewOccurrence` has an identity and one `PortPath`.
- `CoreSyntax.lean:247–259, 291–307`: `.force` has only a `Value`; `.expose`
  and `ContextFrame.expose` carry effect/result occurrences.
- `ControlSyntax.lean:107–131`: `CallHead` ends in `failed` (no `bad` case);
  `CallState World` leaves `World` abstract and stores frames, view occurrences,
  receipt slots and a literal suffix.
- `ControlSyntax.lean:133–136, 147–158`: suffix conversion retains only View
  identities; an expose frame projects to one `Frame.view` identity;
  `activeViews` returns only each expose frame's effect occurrence.
- `ControlSyntax.lean:160–164`: `CallControlStep` uses general `Metadata World`
  operations. `enterExpose` only pushes the frame; `returnExpose` applies
  `md.viewReturn` to the result occurrence identity. `emitRequest` accepts
  suffix occurrences constrained by identity equality; `requestExpose` calls
  `md.suspendView` and saves the exposed computation. The source-to-record
  equation is not encoded by these constructors alone.
- `CoreSubstitution.lean:527–546`: Call renaming traverses variables in the
  finite syntax; view occurrences, owners and occurrence identities are
  preserved. It does not implement the source control-name interpretation.
- `ControlTyping.lean:80–120`: Call typing checks head/result and context/suffix
  typing but does not relate `World` to the paper's concrete world or
  authenticate the Force path projection.

Relevant alternatives rejected by the architect: equating effect/result
because endpoints have equal types; using arbitrary `adapterMap` or `Metadata`
callbacks as source construction; using set subtraction for leave; recovering
suffix paths from IDs; importing the Original-only bridge as wrapped-Force
semantics; or restricting to bare/closed Delay.

## Falsifier and review boundary

The falsifier is a source-required wrapped or captured Force transition for
which a proposed encoding cannot compute a distinct port, retained lineage,
fresh occurrence, current context or saved-context restoration. Test the
interface against nested returned thunks, shared outer/inner witnesses, an
outer Call View beyond a handler, repeated resume under different ambient
contexts, Fail, malformed-Force Bad and child Bad propagation.

The review decides only whether this captured gap and its owner follow from the
pinned sources. It does not provide `pi`, prove any Lean theorem, authorize a
representation, or close Force formation/projection, Call S/C, Call A/B, native
correspondence or the parent goal. All remain OPEN.
