# Pre-admission owner cut for one F5 Apply occurrence

Date: 2026-10-08
Baseline: `a1a84452cdc21bc41b2136e0f049ab1fdd2f3435`
Branch: `research/simple-sub-intrusion`
Status: bounded read-only source/HIR/core/solver owner audit
Claim class: scoped partial-owner correspondence
Authority: none; no source rule, implementation, or cutover gate is selected

## Result

The exact inner `f x` in `my apply f = { my step x = f x; step }` has a
pre-admission symbolic constructor, but no complete source `F_c` supplier on
the inspected owner path. The symbolic constructor retains the exact captured
formal binder, local Lambda, argument binder and Apply expression, and emits a
`SymbolicGenCall0` record independently of solver admission. These are
lexical/syntactic identities only. Its own unresolved inventory includes
`InitialSourceDescriptorRelation`, `OriginalXi`, `OriginalTypes`,
`OriginalScopes`, `EmittedGenCall0Membership`, and the complete emitted Call
clause/joint witness.

This refines the previous field crosswalk: there is a source-directed symbolic
demand and Gen-Call-0-shaped record before solving, but no interpreted
environment, semantic `R_f` anchor, complete dependent Function, or emitted
membership that would make it the selected source object.

## Owner path

- `yu-hir::retain_shadow_local_binding` checks and retains the exact inner
  Apply, callee/argument Name resolutions, capture and source positions.
- `yu-hir::shadow::Form`/`Premise` retains structural Lambda/Bind/Use/Apply
  topology and explicit pending call-view, signature-position, occurrence,
  provider, evidence and output-leg obligations.
- `yu-core::shadow_call_formation::generate_captured_from_skeleton`
  constructs one `SymbolicGenCall0` and `SymbolicDemand` from that skeleton.
  The demand contains `SymbolicRegistration { declaration, outer_scope }`,
  local scope, argument declaration and call identity. It does not carry an
  interpreted source descriptor relation, original `xi`, or semantic root.
- `yu-core::shadow_derivation` projects the candidate as `PendingCall` and
  eight structural Apply addresses. Its contract explicitly provides no
  endpoint, effect, role, receipt, typed port, inference or admission judgment.
- The separate solver candidate maps its Apply recipe to a negative
  four-port Function demand, then admits the structural `callee <: demand`
  fact. No consumer joins the core symbolic record to that Term.

The symbolic call-formation module explicitly states that its terms have no
solver or production consumer. This is scoped to the inspected producer and
consumer path, not a repository-wide absence result.

## First missing authentic input

The selected source Call construction takes an interpreted environment,
original scope and shared `xi=(nu,K,D)` as inputs. Under those inputs it
constructs the complete dependent `F_c` at the captured formal's original
`R_f`, then requires the existing `WF_Dec`, `VIncl`, whole-argument/provider,
callable-execution containment and typed-call evidence obligations.

The earliest missing field in the inspected compiler path is therefore the
initial source descriptor/environment relation at the same original scope.
Without it, `SymbolicRegistration` cannot certify `R_f`, and its
`SymbolicDemand` cannot be identified with complete `F_c`. The negative
four-port Term remains only a structural approximation. The source-theory
constructor is conditional on its inputs and is not a current compiler object.

No implementation or semantic-policy question is resolved here. The pending
flat Application owner decision remains separate from this current-path
finding. No compiler code, tests, builds, probes, measurements or Git
operations were performed during the audit.
