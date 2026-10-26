# Independent review: original source receiver construction / r2

Reviewer: `/root`; not the author of the reviewed Lean module, note or handoff.
Producer: `/root/principality_source_r2`.
Verdict: **ACCEPT the stated source construction only**. Original native
receiving-incidence correspondence and original principality remain OPEN.

## Frozen reviewed inputs

| File | SHA-256 |
| --- | --- |
| SourcePrincipalTransport.lean | `ab86c4448dcddcb5e20ef1495e317c4d0fc04ad0ff52c4323779d12f5fde33ee` |
| paired theory note | `971f61bceab6cdbc68ea3900066b84a41176679960fb2ccfd35900b963c93857` |
| producer handoff | `471473c949a7af88a539028a9b4de5ba03740540244b9cf1ce72146d32bbb648` |
| complete audit source | `57bcdf0639d70ca182c0b0467a5f492928afae3023300a456380a77a4f1d6df0` |

Baseline `45d307a0a`; the primary subsequently fast-forwarded disjoint
`ff12ce504`. No imported source of this module changed. The reviewer used the
primary-owned cache, independently building the module and nine dependencies
at the fixed toolchain. The producer's isolated cache was not used.

## Semantic review

The raw program is the unchanged BRD/AR/RZ recursive example. The source
builder itself, rather than a separately chosen constraint graph, computes
its three closure and two application owners. The recursive f remains an
internal monomorphic component at its recursive call. Both exact App trees
retain complete Call, effect/computation, argument compatibility and source
incidence premises. The second record field remains inside the first field's
Return/rebind suffix. These equations do not prove those premises true or
promise that the first call returns.

`h_name_source_derivation` constructs the actual local Name rule using the
existing ordinary-formal interpretation of an allocated installed tuple in
the real recursive context. It does not take Name typing as a premise. It
nevertheless assumes the specified current installed tuple and uses the
already supplied semantic inputs. It is neither a derivation for the entire
program nor complete original primitive/catalogue soundness.

The registry preservation theorem covers every original Frame constructor.
It retains static source ownership; it does not imply runtime activity or
eligibility. The App subject is the callee Name's `returnedValue`, while the
Name proof addresses `finalRoot`. The separate `hReturn` update and runtime
equation correctly avoid equating these ports without a returned object.
The Return data and binder are inputs to a data projection; no `Admitted`
predicate or actual Return event is derived. This limitation is explicit in
both theorem documentation and the theory note.

AR/RZ already contain the full source-side monomorphic event-family middle.
The new module supplies source construction/readout facts needed on that
side, but does not formalize all AR/RZ semantic premises in Lean. The note's
native route is read from the established derivation/current code, not a new
Rust execution receipt. Parent.sources and its `any(qualifies)` consumer
do not authenticate the occurrence's one original receiving projection.
The exact residual equality remains
`actualOccurrence(z).receiver = receiving_index(source_frame(Z_real))`.
No injectivity of erasure, FiberConstant hypothesis, per-port witness,
arbitrary receiver selector or old cross-birth SCC counterexample is used.

The source H receiver is not claimed to be the receiver of native z. No
nonempty qualifying occurrence, lost original typing, principal witness,
instanceOf result or source-qualified counterexample is claimed. The
publication must preserve this scope; the filename is not a theorem that
the original principal-transport obligation has been solved.

## Independent checker and axiom audit

Installed Lake:
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`.
Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
Both invocations used one thread, `-j1 -M1024`, and `timeout 120`.

1. `lake build +YulangClosure.SourcePrincipalTransport`: exit 0, 11 jobs,
   new module 2.3 seconds.
2. `lake env lean -j1 -M1024 --root=.../principality-source-r2
   .../AuditSourcePrincipalTransport.lean`: exit 0, no audit errors/warnings.

The audit enumerated 114 originating declarations: 41 definitions and 73
theorems. All 114 complete type/axiom blocks are unique and balanced; all ten
required roots have theorem kind. It includes private/generated equations
and splitters, not merely the public namespace. The theorem axiom sets are
35 empty, 19 `propext`, and 19 `propext, Classical.choice, Quot.sound`.
No `sorryAx`, project axiom, native-evaluation assumption or checker bypass
was found. The identical audit source is now a reproducible repository file,
`notes/theory/lean/AuditSourcePrincipalTransport.lean`.

Scratch evidence in `/workspace/scratch/e3678bef96db/fresh-scope-r2`:

- `principality-review-build.log`, SHA-256
  `4fd958317147a594bdc5548e1ee2b8dc1c97f2e62a3dc9fbf380779694961b7f`.
- `principality-review-audit.log`, SHA-256
  `33b0418b48adf10ee3ee8f48da43b916f78f00a7aeb65c90ad15462943959f7d`.

The review used two focused checks. No compiler, semantics, toolchain,
configuration or reviewed producer source was edited. Default-target
integration and full native source coverage are separate obligations.
