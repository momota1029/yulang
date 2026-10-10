# Ordinary Function ports: polarity before the child wrapper prefix

Date: 2026-10-10
Status: independently reviewed conditional algebraic derivation and bounded
frozen-source bridge; no source-reachability theorem, production conformance,
or gate closure
Assigned checkout baseline: `3c42971ea6f53604537cf2c66ed3873f94ee248b`
Frozen Oracle source: `9f03827ff^`, resolved by the primary as
`6a18bd24bd0fa8b07e3eca5e099bfa8646320e3a`
Exclusive output lease: this note only
Worker: `/root/function_port_proof`, constructive proof leaf; no delegation

## Objective, authority, and evidence boundary

Derive the ordinary Function argument/result context by composing the actual
port operation with the subsequent positive-wrapper operation. The governing
authority is [contextual attachment admission](../design/2026-10-10-contextual-attachment-admission-design.md)
§4, Function ports and Positive wrapper. Section 3 requires exact operation
order and shared child identity. Sections 3.1 and 6 retain the selected
attachment grouping and bounded implementation scope. This note makes no new
semantic decision and does not promote a shared proof status.

The source excerpts below were supplied by the primary from its read-only
inspection of the frozen Oracle commit. This leaf did not independently
extract the Oracle blobs. Their content and locators are explicit supplied
evidence, distinct from the algebraic definitions. No current uncommitted
implementation change is a premise or a conformance claim in this note.

## Frozen statement, quantifiers, scopes, and exclusions

Fix one existing source scope and one ordinary comparison of a positive
Function lower `F_l` against a negative Function upper `F_u`. Let `P` be its
actual inherited exact context expression. For every such `P`, every selected
ordinary port `f`, and every fixed source-local positive wrapper weight `w`
satisfying the hypotheses below, define the child-local context

```text
C = PrefixLeft(w, Identity).
```

The required conclusion for the context after port descent and positive-wrapper
consumption is

```text
Argument Value or ordinary Argument Effect: PrefixLeft(w, Swap(P))
Result Value or Result Effect:                PrefixLeft(w, P).
```

The hypotheses are:

1. The parent firing is an ordinary Function comparison. Argument Effect uses
   its ordinary branch; the special syntactic `Neg::Bot` passthrough branch is
   excluded. This is selection of the named claim, not a source rejection rule.
2. The selected child really has the specified positive wrapper at the positive
   endpoint *after* the Function port has reversed or preserved its endpoints.
   The wrapper operation is then encountered with the transported parent
   context. An upper negative wrapper or a wrapper already consumed on the
   parent is not this hypothesis.
3. `C` is exactly the closed unary prefix above: its only context input is
   Identity. The fixed `w` is the weight of that child constructor. It is not
   an independently selected marginal context or a weight reconstructed from
   the child's endpoint IDs. Closed here describes the supplied local context
   expression; it imposes no new restriction on ordinary source inference.
4. The conclusion concerns the primitive operation expression at these two
   transitions, before any subsequent admission, normalization, replay, filter
   discharge, extrusion, or omission. No extra transition is inserted between
   the specified port descent and wrapper consumption in this statement.

All endpoint sorts, annotation occurrences, attachment/member identities,
resolved operands, lexical binders, providers, dependencies, and constructor
lineages are fixed as supplied by this one source comparison. Neither the proof
nor substitution below renames or equates them. There is one actual `P` shared
by the port firing; there is no independent witness choice for its children.

This is a universally quantified algebraic derivation under the stated source
shape and transition hypotheses, with a bounded frozen-source bridge. It does
not establish that arbitrary contexts `P` or arbitrary prefixes `w` are
reachable from accepted source, that all emitted tasks are activated, or that
all possible bounds are replayed. It excludes arbitrary effect soundness,
effect hygiene, complete Call behavior, required principality, handler/runtime
behavior, lifecycle/rollback/certificates, generic residual generation,
termination, concrete formal-row admission, and public/default/F5 cutover.

## Explicit algebra and direct derivation

Use exact context syntax with constants `Identity`, unary `Swap(K)`, and unary
`PrefixLeft(w,K)`. These names retain their input expression and the complete
source-local `w`; they do not denote a quotient by observed effect counts.
Define

```text
S(K)   = Swap(K)
L_w(K) = PrefixLeft(w,K)
T_f(K) = S(K)   for Argument Value and ordinary Argument Effect
T_f(K) = K      for Result Value and Result Effect.
```

The local expression `C` represents the unary constructor template
`L_w(hole)`. Replacing its designated Identity context input with a supplied
input is context substitution, not substitution in a source type, effect
operand, or lexical binder. It leaves `w` and every original scope unchanged.
It does not assert a generic composition rule for arbitrary child-local
context DAGs.

The port transition supplies the intermediate context `Q = T_f(P)`. The next
positive-wrapper transition has input `Q` and supplies `L_w(Q)`. Thus the
ordered two-step composite is `L_w(T_f(P))`. For each argument port,
substitution of `T_f(P)=Swap(P)` yields `PrefixLeft(w,Swap(P))`. For each result
port, substitution of `T_f(P)=P` yields `PrefixLeft(w,P)`. These substitutions
derive the claimed equalities for every fixed `P,w` in the stated envelope.

This proof does not assume that Swap is injective, an involution, or compatible
with prefixing. It does not assume PrefixLeft commutes with Swap or that either
unary operation performs directed mix. In particular,
`Swap(PrefixLeft(w,P))` records a different order: it consumes the child wrapper
before the Function polarity transition. Its exact syntax has a Swap root;
the required argument expression has a PrefixLeft root. Semantic coincidence
in a special weight case cannot authorize replacing one exact operation tree
by the other. No alternative replay or reconstruction layer is required.

## Frozen Oracle constructors and consumers

All locators in this section refer to the supplied Oracle commit, not current
workspace line numbers. File blob identities supplied by the primary are:

| Frozen file | Git blob identity |
| --- | --- |
| `crates/infer/src/constraints/machine/propagate.rs` | `d558e7b9c17d33e91c5bb39c4cd85ebbfa4a8b09` |
| `crates/infer/src/constraints/mod.rs` | `14860e3664a7ac05f7493f1d51fe69a6f34216e5` |

The actual Function owner is the Function match in `machine/propagate.rs`.
The positive/negative Function terms supply the following child endpoints and
operations; the consumer of the inherited weight is each emitted child task:

| Ordinary child | Positive endpoint `<:` negative endpoint | Frozen locator | Emitted inherited weight |
| --- | --- | --- | --- |
| Argument Value | `F_u.arg <: F_l.arg` | `propagate.rs:226`–`:233` | `let swapped = constraint.weights.swapped()` at `:226` |
| Argument Effect | `F_u.arg_eff <: F_l.arg_eff` | `propagate.rs:247`–`:255` | the same swapped weight |
| Result Effect | `F_l.ret_eff <: F_u.ret_eff` | `propagate.rs:257`–`:263` | `constraint.weights` |
| Result Value | `F_l.ret <: F_u.ret` | `propagate.rs:264`–`:270` | `constraint.weights` |

The separate Argument Effect passthrough uses `both_from_right()` when the
syntactic argument effect is `Neg::Bot`. The algebra above does not substitute
Swap for that operation or infer this branch from current purity observations.

Positive `Stack` and `NonSubtract` lower-wrapper consumers at
`propagate.rs:19` and `:31` enqueue their inner comparison with
`constraint.weights.with_left_prefix(weight)`. The weight is that wrapper's
actual source-local weight. These calls supply the second transition used in
the proof. For an argument, the positive endpoint carrying this wrapper belongs
to `F_u` after reversal; for a result it belongs to `F_l` without reversal.
This endpoint fact is why one must identify the actual child wrapper rather
than move a parent wrapper through Swap.

The supplied exact weight-operation bodies are:

```rust
// constraints/mod.rs:3566
pub fn swapped(&self) -> Self {
    Self {
        left: LeftConstraintWeight::from_right_weight(&self.right),
        right: RightConstraintWeight::from_stack_weight_pops(
            &self.left.to_stack_weight(),
        ),
    }
}

// constraints/mod.rs:3577
pub fn with_left_prefix(&self, weight: StackWeight) -> Self {
    Self {
        left: LeftConstraintWeight::from_stack_weight(&weight).compose(&self.left),
        right: self.right.clone(),
    }
}
```

The first body is a directed weight conversion, not evidence of a lossless
exchange of arbitrary left/right data. The second places the new left weight
as the first operand of `compose` and preserves the inherited right weight.
Identifying `compose` with ordered left composition, and these conversions
with the intended Swap interpretation, supplies the weight-level reading of
the exact syntax theorem. Full semantics of those helpers, filters, active
families, arithmetic/overflow, and subsequent canonicalization are not proved
by these excerpts. The operation-order observation itself does not depend on
an invented lossless interpretation of Swap.

Consequently the bridge established by the supplied code is local and
conditional: a Function child receives the port's transformed inherited
weight, and a subsequent positive-wrapper task prefixes its own weight to
that weight. The excerpts do not authenticate a particular parsed source
fixture or complete worklist trace. Stored constraints alone are not evidence
of their activation or complete replay.

## Dependency snapshot, checks, runtime, and handoff

The governing workspace file was read and hashed as
`717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc`.
Equality of that file with the assigned checkout baseline was not independently
checked by this leaf. The frozen Oracle identities above are primary-supplied;
this leaf made no Git query or mutation. No changing compiler file is a direct
dependency. No changed dependency hash was observed during this assignment.

The yulang-proofs skill and the relevant orchestration, research-lab, authority,
compiler-engineering, and Git-concurrency rules were read. Requested runtime:
`gpt-6.1-sol` / `high`. Effective model/effort and launch-role metadata are
unavailable in this child session and remain **unknown**. The inspected prover
role file has no model/effort pin; configuration requests Sol/high subagent
defaults. Those files and the packet do not establish actual execution settings.
No Astra escalation, child agent, or external contact occurred.

Verification owner for this note: this leaf. `sha256sum` recorded the governing
dependency and runtime/skill inputs. A focused `python3` note-integrity script
checked final newline, balanced fences, whitespace, five section headers,
baseline/formula presence, the local authority link, and the unchanged governing
dependency hash: PASS. Its first invocation incorrectly expected six headers;
that check assertion was corrected to five without changing the artifact.
These are document checks, not proof tests. No compiler test, build, executable
model, benchmark, or source execution is claimed. Read-only command concurrency
peaked at four invocations; the two lightweight note-check invocations were
serial. No numeric CPU/RAM or elapsed-time measurement was collected. The
primary retains global budgets, independent review, shared records, and Git
integration.

Next action: the primary assigns independent review of this frozen derivation
and supplied source bridge, then checks the actual implementation constructor
and consumer against the ordered expression if that gate is pursued.

Commit packet: exact lease is
`notes/progress/2026-10-10-function-argument-effect-contravariance-proof.md`;
baseline `3c42971ea6f53604537cf2c66ed3873f94ee248b`; frozen Oracle parent and
blob identities are recorded above. Independent compiler-referee review
accepted the conditional algebra and source bridge after the primary corrected
the minor Function-port locators. No producer certification or broader
source-reachability claim is made. Proposed checkpoint message:
`research: derive ordinary Function polarity before child effect prefixes`.
Shared-record deltas left to the primary/curator: record the bounded algebraic
derivation and primary-supplied Oracle order evidence; retain source
reachability, execution/completeness, implementation conformance and the wider
semantic/cutover gates as open. No shared record was edited.
