# CALL-REQUEST-UNWIND-P-20261025 — frozen handoff revision 1

Sprint/contract: `LEAN-CALL-UNWIND-20261025/r1`, packet **P** only;
`tasks/agent-loop/sprints/call-unwind-20261025-r1.md`, SHA-256
`efeaabb27416bd9cb51066c37f8a36d13b3a4ced3eeba7f1f9488ac4ada38a2a`.
Baseline supplied by contract: `64d39df59`, branch
`research/simple-sub-intrusion`.
Assignment/handoff ID: `CALL-REQUEST-UNWIND-P-20261025`, revision **1**.
Outcome class: **candidate**, pending Luna verification and fresh review.

## Exact parent and application

The artifact defines `CallState.captureFrames` with exactly the contract's five
equations: empty list returns the continuation; bind and adapter capture using
`CallState.captureBind`; scope captures `.scope owner continuation`; expose
captures `.expose effectView resultView continuation`. Every nonempty case
recurses on the remaining frames after capturing the innermost frame.

It supplies the exact contract proposition in `YulangClosure.Control`:

```lean
theorem call_request_unwind_exists
    {W : Type} (md : Metadata W)
    (world : W)
    (op : TypedCall.OperationInstance)
    (payload : TypedCall.Value)
    (continuation : TypedCall.Comp)
    (observed : List TypedCall.ViewOccurrence)
    (frames : List TypedCall.ContextFrame)
    (view : TypedCall.CallView)
    (result : Original.Ty)
    (scopes : List Nat)
    (views : List TypedCall.ViewOccurrence)
    (receipts : List TypedCall.ReceiptSlot)
    (suffix : List Frame) :
    ∃ (world' : W) (scopes' : List Nat),
      YulangClosure.Prefix (CallControlStep md) (frames.length + 1)
        ⟨world, .requesting op payload continuation observed,
          frames, view, result, scopes, views, receipts, suffix⟩
        ⟨world', .requested op payload
            (CallState.captureFrames frames continuation),
          [], view, result, scopes', observed, receipts, suffix⟩
```

Parent application: this candidate constructs the raw unwind segment required
by Luna's request composition corollary, including its empty Call-frame
endpoint, actual captured continuation, and exact length. The local
`prefix_prepend` lemma is applied directly in every inductive branch, rather
than filed as a separate result. No additional typing or reachability premise
is added to the unconditional P theorem.

First remaining evidence for P acceptance: actual elaboration on the frozen
inputs, owned by Luna, followed by the contract's signature/axiom checks and
fresh independent review. Q and the supplied-initial-prefix composition are
other owners' outputs. The producer does not certify this candidate.

## Actual constructor evidence and coverage

The directly inspected formal operational owner is
`ControlSyntax.lean:CallControlStep`; `CoreSyntax.lean:TypedCall.ContextFrame`
has exactly bind, adapter, scope, and expose. The proof inducts on the actual
frame list while generalizing world, continuation, and scope context:

| Frame | Actual transition | Continuation/world/scope passed to tail |
|---|---|---|
| bind body | `requestBind` | `captureBind continuation body`; same world/scopes |
| adapter input output body | `requestAdapter` | `captureBind continuation body`; same world/scopes |
| scope owner | `requestScope` | `.scope owner continuation`; `md.suspendScope world owner`; `owner :: scopes` |
| expose effectView resultView | `requestExpose` | `.expose effectView resultView continuation`; `md.suspendView world effectView.identity`; same scopes |

The empty list uses the actual `finishRequest` constructor once. All four
nonempty cases prepend exactly their real one-frame transition to the tail's
prefix. The helper is proved from `Prefix.refl/snoc`; its result length is
`n + 1`. At a cons frame, the tail already takes `frames.length + 1` steps,
and prepending one yields the contract's cons-list length plus one.

The endpoint's viewContext is exactly `observed`, as emitted by
`finishRequest`, rather than the initial `views`. The suffix, receipt slots,
CallView, result type, operation instance, and payload are retained literally.
World and scope endpoint witnesses remain existential. No world or scope
restoration claim is introduced. Expose field order is effect then result.
Bind/adapter capture retains the actual `captureBind` response-index lifting;
ordinary unshifted bind is never substituted for it.

Prior work reused only within its premises: the existing formal constructors
and the existing `Prefix` datatype. Accepted one-step/finite typing are left
for Luna's later composition; they are not used to manufacture transition
existence. Failed r1 typing, assumed-transition probes, and conditional
source-input results are not imported or promoted.

This is evidence about the actual frozen formal relation, not a compiler
source/native correspondence theorem. No new compiler constructor, constraint
generation/accumulation/propagation, level, extrusion, qualifying intrusion,
generalization, metadata law, source rule, or external dependency is added.
Global progress, signal reachability, successor coverage, external resumption,
cleanup/lifecycle correctness, ordinary-Control handoff, original Call A/B,
inference A/B, and production remain OPEN. The Force/view gap and r9 remain
OPEN/UNACCEPTED.

## Frozen source, dependency hashes, and provenance

Artifact: `notes/theory/lean/YulangClosure/CallRequestUnwind.lean`, SHA-256
`e4835bd2c2487b14d658b02373e0507ea6c201b81a1fb81d396b0f05a1850fc9`.
This handoff's byte hash is supplied separately at submission.

The sole direct import is the pinned `YulangClosure.ControlSyntax`.
At activation, the contract SHA and **all 50** source/evidence/build-output
pins in its exact table were read and matched using read-only SHA-256
comparisons. Both leased P outputs were absent before the first write.
Key exact proof inputs:

| Input | SHA-256 |
|---|---|
| `ControlSyntax.lean` | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `CoreSubstitution.lean` | `c4bca75be173f20d7a48751205f488ac5f0057b476e6f52d1ef7abcf046a001a` |
| `ControlSyntax.olean` | `372a3a91210c161b3e7699578f6d7043b5b48eb096bf6b12cb101fcb97f00f28` |
| `ControlSyntax.ilean` | `3ed9083679f8d4be830e05809b096f4b9927335ac623d84fd0a25e2112c8fdf1` |
| `Contracts.olean` | `eac90ceeca9cb6d4479648a92ce9b3b24960c3b0e99de5af2dc7c942e542f6bc` |
| `Contracts.ilean` | `6d24c9e7dd4fe9442150d30b927d2f93b58b592cffd643a96a5078cd3c4a91e8` |
| finite-typing accepted outcome | `f82192a95c9d5cac2474160e56654ffa6b36fa737edca09fd443b3b0fab1456d` |
| finite-typing clean review | `5ad32dc61b81056348607ba8bda344fd6c117806f14bf67dbcc8ae7b268c94c4` |
| finite-typing verification JSONL | `50a0c45503460cc166c45d5099698a1f7b8c3cd6a2cc5bd980f9386a1a86f108` |

The remaining exact transitive hashes are the revalidated frozen contract
table, identified by the contract SHA above. No additional dependency is used.

Sole author/actual worker: `/root/call_step_typing_author`, fresh P START
acknowledged to Luna before activity; proceeded only after explicit lease-state
activation. No descendants or other authors. Requested model/effort:
`gpt-6.1-sol` / `high`; observed effective model/effort: **UNKNOWN / UNKNOWN**.
This producer is ineligible to review P or the combined composition.

## Checks, resources, next step, and cessation

Author checks: exact contract and actual constructor inspection; read-only
validation of every frozen hash and pre-write path absence; manual audit of
capture nesting, both binders, all four frames, endpoint metadata and exact
length. No Lean/compiler/test invocation, Git, scratch file, other output,
descendant, background service, or production edit.

Fresh grant: 900 seconds, no carryover, zero Astra and zero author checker
processes. First local UTC observation after lease activation: 03:30:33;
manual source-reread observation: 03:32:17 (104 seconds between observations).
Initial START-to-first-clock overhead is UNKNOWN and remains part of the grant;
Luna owns the actual launch/resource receipt. Final cessation observation is
returned with submission. Work stops within the cap; no renewal is requested.

Mutual TODO `CALL-REQUEST-UNWIND-P-CHECK-1`, owner Luna: after both authors STOP,
revalidate all frozen pins and compile this exact P artifact as the first
serialized invocation, proceeding only under the fixed contract. Falsifiers:
first elaboration/pin error, missing frame case, wrong length/capture nesting,
swapped views, lost `captureBind` shift, incorrect endpoint viewContext, false
world/scope equality, missing output/receipt, changed signature, or unexpected
axioms. Stop on the first failure; no repair loop under this revision.
Fresh review and composition belong to Luna.

No further in-envelope P step remains. **STOPPED / WRITES STOPPED**, before Luna
verification. New paths are exactly `CallRequestUnwind.lean` and this leased
handoff. No Q/composition writes, scratch paths, descendants, background
processes, or unresolved descendant leases. Pending verification/review; no
reviewed-theorem, parent A/B, source/native, or production closure asserted.
