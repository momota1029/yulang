# Oracle subtype and recursive-bound map

Date: 2026-09-30
Reference: frozen Yulang2 Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Classification: source-implementation characterization; not a new semantic contract

## Findings

The Oracle's public polarity AST in `crates/poly/src/types.rs` is finite:
positive nodes include union, negative nodes include intersection, and all
polarities can contain variables, constructors, or functions. It has no `mu`
or other recursive type node.

Subtype entry is `AnalysisSession::subtype` in
`crates/infer/src/constraints/machine/entry.rs`; `step_subtype` in
`crates/infer/src/constraints/machine/propagate.rs` compares finite shapes and
propagates variable lower/upper bounds. The observed structural rules include
union splitting, intersection splitting, contravariant Function arguments and
argument effects, covariant returns and return effects, and invariant equal-
head nominal arguments. Different nominal heads diagnose a cast requirement.
Function argument-effect propagation has a special pure-bottom case.

Canonical subtype-constraint and bound deduplication keep propagation finite.
The inspected cycle paths terminate through duplicate constraints/bounds and
alias-cycle handling; no explicit coinductive rule accepting a repeated
recursive comparison pair was found. Compaction later recognizes a
`(variable, polarity)` already in progress and emits a recursive bound side
whose endpoints refer to variables. Oracle ordinary scheme instantiation
freshens that identity and restores its lower/upper interval as subtype
constraints. Thus the concrete observable mechanism is finite type syntax plus
a variable-bound graph and recursive interval records.

This invalidates using equi-recursive/coinductive comparison as an assumed
Oracle subtype law. It does not prove that a separate denotational model using
regular trees can never characterize the Oracle's observations. Such a model
would need a correspondence theorem; the Oracle source alone does not justify
that rule. Nor does this map establish that every retained recursive interval
has a satisfying assignment in a chosen semantic carrier.

## Evidence and limits

Relevant Oracle locations:

- `crates/poly/src/types.rs:740-846` — finite polarized type forms.
- `crates/infer/src/constraints/machine/entry.rs:493,970,1092-1118` — subtype
  entry, draining, and canonicalization.
- `crates/infer/src/constraints/machine/propagate.rs:4-476` — finite shape
  propagation, variable bounds, Function variance/effects, and nominal rules.
- `crates/infer/src/constraints/bounds.rs:630,815` and replay planners — bound
  insertion/replay and duplicate suppression.
- `crates/infer/src/compact/collect/mod.rs:746-790` and
  `crates/infer/src/compact/collect/type_nodes.rs:653` — recursive side
  detection and recording during collection.
- `crates/infer/src/constraints/tests/case_01.rs:898-990` — finite alias-cycle
  propagation probes.

The implementation map was read-only. No tests, Python, or measurements were
run. It characterizes the concrete Oracle implementation, not a proof of type
soundness or principality. Next define a declarative finite-constraint
semantics that preserves recursive variable intervals without treating them as
recursive type equations, then relate its steps and public normalization to
these Oracle observations.
