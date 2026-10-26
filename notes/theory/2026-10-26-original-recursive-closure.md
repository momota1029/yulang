# Canonical retained formal-return evidence

Date: 2026-10-26. Producer: `/root/original_recursive_closure_r3`.

Status: **checked partial source constructor; primary-reviewed at the scope below**. The module
constructs retained evidence at actual source formal Return paths and consumes
that output through the existing original environment decoder. It does not
close recursive L4, the original joint introduction atom, whole Function
membership, original inference soundness, or a source-qualified principality
counterexample.

Implementation: `YulangClosure.OriginalRecursiveClosure`, importing the newly
published `OriginalWorldReadout`. The earlier image-restricted checking overlay
and the overlapping native-world models are retained only in scratch. They are
not the delivered interpretation.

## 1. Governing equations and precise scope

[SG §3.3](2026-10-08-source-generalize-definition-and-proof.md#33-owning-rules-declarations-and-event-telescopes)
assigns actual retained initializer/rebind evidence to Shared, operational
return/response fields to EventField/OneShot, and description-owned checking
proofs to ViewLogic/EventProof. The Shared choice is fixed at its original
actual-event anchor; a later logical view cannot choose another actual retained
output. The original complete Lambda/Call sequence remains receipt, designated
Force, actual typed Return/rebind, body, and own invocation return.

The selected [native recursive interface §2](../design/2026-10-08-native-recursive-interface-definition.md)
separates the body-result description from the complete invocation, which
includes argument effects and pending developments. Its interpretation
transport is not authority to redefine a fixed original domain. The selected
[simultaneous introduction §§3–4](2026-10-08-simultaneous-immutable-root-introduction.md)
uses the complete positive V/W/T/Car operator with exact declared value holes;
no world, continuation, guard, or carrier hole may replace a source obligation.

The current `OriginalSource.Environment` already computes

```text
AnchorKey = (origin, actual eventPath, binder)
postReturnKey =
  (origin,
   priorPath ++ [(formalSite, returnRebind, occurrence, runtime(actualOutcome))],
   (formalSite, shared, 0)).
```

`Environment.extend` retains the complete earlier frame list and adds this
runtime event step. A logical description frame does not add an event step.
The new constructor uses those exact equations, rather than assuming a desired
registration equality.

## 2. Actual source registry and completed-return constructor

`hasFormal` traverses the whole existing `sourceCallOwners context source`
registry. Every closure contributes its original formal site. Application
owners do not manufacture formal-rebind owners. `registered_formal`,
`lambda_formal_registered`, and `every_source_formal_return` connect the
constructor to that source-derived inventory, including nested lambdas and
multiple actual invocations of the same closure. No owning application is
selected as the allowed invocation domain.

`RetainedRebind` retains the exact original anchor key, the **entire** raw
`Outcome`, and the source-fixed descriptor of its formal. The outcome includes
its observation, result, current history/configuration, endpoint objects, and
binding addresses. No raw field is replaced with a checked result or a
provider chosen after execution.

`retainedRebind` is a deterministic constructor on a raw anchor key. It
recognizes a formal Shared binder only when the terminal event step is that
registered formal's actual returnRebind step and the raw outcome contains an
actual Value result. `completed_return_retained` proves the exact readback for
every such source owner and outcome. `pending_return_no_retained` and
`retained_is_completed` prove that pending outcomes do not materialize this
completed output. These statements are data formation laws; a result tag does
not prove that a Return is typed.

The complete original `Inputs`, checked domains, executions, positive
observation obligations, and compatible future relation are not modified.
In particular, this constructor is **not** an additional conjunct restricting
`checkedIncidences`. It also does not prove that every independently admitted
original Function challenge already has the required invocation/frame
registration. That earlier all-future correspondence remains open.

## 3. One canonical strategy, fixed before calls

`canonicalAnchors` is one total strategy fixed before the source events. For a
recognized formal Return key belonging to the fixed original declaration, it maps the complete `RetainedRebind` tuple to a
Shared witness; unmatched and other-declaration anchors retain the original strategy. The source
formal descriptor map is fixed with this strategy. The constructor reads
neither a later checking descriptor nor a future frame.

`completed_return_shared_anchor` proves that the original `anchorValue`
mechanism reads this computed output at the exact post-return path.
`logical_frame_keeps_return_key` proves that a preceding legal logical frame
cannot change that key. `every_old_anchor_preserved` proves that later source
extension never overwrites an earlier key's strategy value.

`extendPrefix` uses the existing extension operation for the entire preceding
heterogeneous telescope, including all logical frames. `prefix_original_strategy`
proves that the original declaration and strategy remain fixed throughout it.
`canonical_prefix_already_fixed` then proves that reusing the local decoder
construction after such a telescope does not change the strategy at all. Thus
the canonical assignment can be installed once at an empty source root and
retained through every later extension; it need not be selected after seeing
a Return or a logical checking choice. This does not assert equivalence when
a different canonical strategy is attached to an arbitrary pre-existing
environment with independently fixed anchors.

The `encode : RetainedRebind s View -> s.WitnessValue` argument is a fixed data
representation map, not a membership or registration law. The module does not
assert that every such map preserves all original witness information. In
particular, a constant encoder would not establish the desired original
semantic representation. A concrete source use still must instantiate the
original WitnessValue representation and its readout. The complete tuple is
present as `RetainedRebind` before encoding; no theorem claims to recover it
from an arbitrary opaque encoding.

Likewise, a globally fixed witness strategy can be lawful for a particular
canonical assignment without being a universal original bind law. A concrete
application to `OriginalRecursivePair.WorldRegistry` still needs the original
witness-position encoding and full current EventField interpretation. The
current Pair registry uses natural-number references. This module does not
postulate or establish an encoding of every original future anchor into those
references.

## 4. Freshness and the actual decoder consumer

`FramePathsWithin` is a physical prefix invariant, with no typing predicate.
The empty root satisfies it, and `extend_frame_paths` proves preservation by
every original `Environment.extend`. `completed_return_key_fresh` derives the
new key's distinction from all earlier frame keys by the actual extra Return
step. No allocator or provider freshness is substituted for source-path
freshness. Applying this invariant across arbitrary publication restoration
still requires the corresponding original restoration invariant; the module
claims only its displayed empty-root and extension constructors.

`decode_computed_formal_shared` consumes the newly computed anchor through the
existing `Environment.extend`, `decode_extend`, and `decodeFrame` operations.
Its inputs are an actual decoded prior environment, a source-registered formal,
an actual raw Value result, the fixed source descriptor/encoding maps, and the
independent runtime readout. It constructs the post-return/post-Shared state
and proves all of the following together:

- decoding the constructed environment succeeds;
- the full earlier Shared frame list is retained and exactly the new complete
  Shared frame is appended;
- the current configuration is the actual Outcome's current configuration;
- the current witness is the new Return's `RuntimeReadout.witness` value.

The final clause deliberately does not equate the new current witness with
its preceding value. Existing Shared anchors remain fixed while genuine new
EventFields/current witness data may change.

The Shared payload produced here adds no duplicate binding or installed-cell
updates: those are already handled by the actual runtime/native-world readouts.
Its witness represents the retained whole raw tuple. Whether this is the exact
original retained-evidence representation is an explicit instantiation task,
not something inferred merely from empty `Shared.bindings`/`installed` lists.

## 5. First original parent residual and finite integration surface

The current Lambda generator's Value branch is

```lean
| .value => suffix formal.site checkedBody
```

A source-faithful candidate integration would place the retained Shared output
inside the actual returnRebind scope, schematically

```lean
| .value => suffix formal.site
    (.sharedE ⟨formal.site, .shared, 0⟩ checkedBody)
```

This is a proposed existing-file change, **not an edit made by this packet**.
Its admissibility must be reviewed with the source-event owner. `executionE`
quantifies only the kernel's admitted returnRebind candidates; it is not the
set of every pending raw observation. The actual source admission constructor
must identify completed typed Return outcomes and their original evidence.
Pending strict-call observations keep the ordered unfinished suffix and do not
execute a fabricated Shared introduction.

The remaining finite integration surface is:

1. connect original actual typed Return admission to this completed Outcome
   constructor, including callback/record/unit-pattern preprocessing where
   applicable;
2. select the exact retained-output representation and source-owned Shared
   binder, preserving all earlier anchors and allowing current EventFields;
3. combine those outputs with `OriginalWorldReadout`'s actual binding/capture
   readout and independent world guards at the resulting original event;
4. identify every selected phase with the full original `checkedObservation`
   and raw execution, then construct the actual postfixed source family and
   apply `simultaneous_introduction`.

Steps 1–4 are not replaced with theorem assumptions in this packet. No claim
that they are proved follows from the decoder theorem. The first unclosed
original semantic supplier is the actual source returnRebind admission and
retained-field representation at the existing Lambda seam.

The initially investigated domain-reading correction is also not integrated.
Removing `input.event = state.assignment.event` from `stateClause` would expose
all-event domain inclusion, but needs complete original fixed-fiber/future
registration. The scratch checking overlay's source-image restriction did not
establish that equivalence and is not promoted.

## 6. Direct-return principality candidate

The primary separately observed native rejection of

```yu
my top h = {
    my f x y = { h x; f {a: y}; y }
    my i: int = f {a: 0} 0
    my b: bool = f {a: true} true
    (i, b)
}
my ignore x = 0
my main = top ignore
```

The inspected source SHA-256 is
`1f1e498263f807cf180c5ea36837aef966647c58831f7d8490599dddf0bcb9f4`.
Native execution/probe ownership and qualification remain with the primary;
this lane did not rerun those compiler probes.

A plausible original source family uses `S = Int | Bool`,
`R = {a: PureReturn(S)}`, fixed captured `H = R -> PureReturn(Int)`, and,
for each lawful `A <= S`, `F_A = R -> PureReturn(G_A)` with
`G_A = A -> PureReturn(A)`. Here the arrows/returns abbreviate body contracts;
the complete callable interfaces must separately retain strict receipt,
argument Force, typed rebind, all pending/resume prefixes, body order, and own
return. The recursive use of `f` is monomorphic within each source instance.
It evaluates only a partial application, which returns the inner closure;
it never recursively invokes that inner closure before the final `y` return.

A finite-intersection alternative `G = G_Int & G_Bool`, `F = R -> PureReturn(G)`
may reduce the coinductive inventory. SG §3.2 permits same-value intersection
introduction, but source formal-description binders occur before invocation
challenges. A proof must show lawful independent source checking views or
retain the required formal/result correlation; it cannot choose the formal
descriptor anew after seeing a challenge. This alternative is not asserted
source-valid here.

Either route needs a genuine joint source family: the entire background in
all four components, actual `f` and captured inner closures, complete worlds,
concrete record/Union fields, and every ordered Call phase. The candidate can
avoid the failed arbitrary-candidate Union-injection argument by constructing
actual ground Int/Bool alternatives in its own family. The actual full
postfixedness and source/publication correspondence are not yet supplied.
Consequently the native rejection is **not** reported by this packet as an
original-source principality counterexample.

## 7. Verification and retained evidence

Verification receipts, full printed declaration types, origin-wide axiom
inventory, dependency hashes, and the finite check ledger are recorded in the
packet handoff and scratch freeze manifest. Every check used the pinned native
Lean 4.35.0/Lake distribution, one thread, `-j1 -M1024`, an isolated cache and a
120-second cap. No compiler code, existing proof module, root import, shared
status, dependency, configuration, or Git state was written by this lane.

Scratch root: `/workspace/scratch/e3678bef96db/recursive-closure-r3`.
Material rejected candidates and failed compiler logs are retained there.
The original partial checking overlay is
`unpromoted-global-event-overlay-check7.lean`; superseded fixed-view and
native-world variants are separately named and are not the final source model.

### Final frozen verification receipt

Final focused build check 24 and full-origin audit check 25 both exited zero.
The origin census found **76 declarations, 39 theorem declarations, and 18
public theorem roots**. Each originating declaration had its type and axiom
dependencies printed. The complete dependency set was `Classical.choice, Quot.sound, propext`; no project
axiom or sorry dependency occurred. The exact public theorem types and their
individual axiom reports are in `public-types-and-axioms.txt`; all originating
reports are in `check25-origin-audit.log`.

Pinned versions were Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, and Lake
`5.0.0-src+eb6cafb`. The final audit took 2.183 seconds and measured
1,019,136 KiB maximum child RSS. Earlier checks did not record peak RSS.
The packet used 25 of its authorized 28 focused attempts; check 19 failed
before Lean because `/usr/bin/time` was unavailable. A Python process-group
runner supplied the final actual resource receipt. Checks 18, 22, and 23
failed during proof repair and are retained, as are all earlier failures.
Check 21 audited the prior canonical version and is not substituted for the
final audit. No default/root build is claimed.

All 12 project modules in the final import cone match the shared repository
byte-for-byte at the recorded HEAD `9a34b280dd23255f0a6583e30b4adbcc34670787`. The final code SHA-256 is
`f3a0c21d73752ee29204438a408a5799ad41ddbab89555109c75c1a3d6b1a63c`. The focused olean SHA-256 is
`a5c97e73576898eb6543562f827d06f080030b3c54f30e991ac079a2b9a8ba57`. The full origin log SHA-256 is
`5051782265b5c9c38f3cf0c12b1e9d18d11671aca09bbaf1fe83793eed8851e2`. The dependency manifest is `final-dependencies.json`.

These receipts establish the displayed constructor and decoder statements
under their printed inputs. They do not establish original source semantic
correspondence or replace fresh independent review.

## 8. Primary review and integration receipt

The primary independently inspected the complete frozen proof, the original
AnchorKey/extend/decode definitions and the source-owner extraction. The
completed Return law computes the new key; it does not assume an event
registration equation. The full-prefix theorem makes the selected strategy
idempotent before arbitrary later extensions. The decoder constructs the
resulting state without assuming an unchanged current witness. Those exact
data-construction claims are accepted.

The primary rebuilt the module and its current imports, then ran the committed
`lean/AuditOriginalRecursiveClosure.lean`. Build and audit both exited 0.
The audit printed all 76 originating declaration types and axiom dependencies,
including 39 theorem declarations and all 18 required public roots. Only
`propext`, `Classical.choice` and `Quot.sound` occurred. No project axiom,
`sorryAx` or checker bypass was accepted. Receipts retained outside Git:

- Build: 13.059 seconds; log SHA-256
  `2d53a5b9e16bc786390b1e493fa42814ea4ac138c1820a1838bf013bb966a42a`.
- Complete-origin audit: 1.604 seconds; log SHA-256
  `5051782265b5c9c38f3cf0c12b1e9d18d11671aca09bbaf1fe83793eed8851e2`.

The subsequent concurrent `OriginalSourceEvents` addition at `3f391497b`
provides a richer source-route-aware retained-output packet and actual formal
installation. It does not change this module's import cone. The present
Site-indexed descriptor map is not a proof of collision-free identity for
arbitrary repeated source Site numbers. Its raw-key law also does not require
that original Shared evidence be recoverable solely from raw Outcome: the
original SG telescope permits already preceding typed EventFields. Faithful
representation and original source admission remain separate obligations.
This integration therefore claims neither those stronger laws nor the original
source counterexample. No existing compiler or source generator was changed.
