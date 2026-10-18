# Design: bind caller evidence to one parse and retain it in HIR

Status: R25 design candidate, awaiting independent review. This note defines a
transport boundary only. It does not select or certify the meaning of caller
evidence.

## Existing seam

`SemanticImports` is currently a unit placeholder. Lowering receives it and
ignores it. `HirSourceIdentity` retains parse-branded `SourceNodeKey`s. The
`CandidateInference` owns the exact `Arc<HirModule>` it solved, and
`RuntimeProgram` owns an `Arc<HirModule>` as well. Therefore the smallest
cross-phase transport location is the immutable HIR artifact; solver/runtime
need no new semantic input for this structural experiment.

## Proposed boundary

Replace the unit-only input with an optional `CallerEvidenceBinding`. Its
binding metadata is immutable and the binding retains an opaque, owned,
`'static + Send + Sync` caller payload through a reference-counted owner, plus
the exact parse-root key, an admitted top-level binding declaration's source
key, and the `ModuleIdentity` it is intended for. `SemanticImports::empty()`
remains the existing no-context input. This preserves the existing
`HirModule: Send + Sync` invariant.

Binding construction must receive a `ParsedFile`, the intended
`ModuleIdentity`, an exact source key obtained from that parse, and the
caller-owned payload. It rejects a foreign parse key immediately. Lowering
checks the binding against its own parsed root and exact module identity, then
requires the source key to occur among that HIR's admitted top-level binding
declaration keys. A parse root, expression, unsupported item, or arbitrary
same-parse node is rejected. This first API does not claim operation-annotation
identity: effect/operation declarations have a separate feature-dependent HIR
identity path and need their own exact binding design before they can be used
as anchors. The completed `HirModule` retains the owner and all binding keys;
it must not retain detached integer addresses or a weak handle.

The structural observation is limited to correspondence:

```text
bound HIR = this parsed root + this module identity + this retained source key
```

It does not assert payload authenticity, scope correctness, lifetime or
dependency validity, common `(W0, xi, h0)`, `j0`, `a0`, license/incidence,
phase actions, world validity, `JointWF`, or any original theorem premise.
No compiler component may infer these facts from payload presence, Rust type,
successful binding, or a matching key. In particular, no public trait,
Boolean marker, `VerifiedJointWF` type, fallback-to-empty behavior, or
solver/runtime semantic consumption is introduced.

## Failure and ownership contract

Foreign parse, foreign module identity, and unavailable/mismatched source
anchor are explicit errors. They cannot silently become `SemanticImports::empty()`.
Reusing the value with a fresh equal-text parse fails because the parse brand in
`SourceNodeKey` differs. A cloned `SemanticImports` or `HirModule` shares the
same owning allocation. Candidate/runtime preservation follows from their
existing ownership of that same HIR. HIR structural equality remains about the
existing source/lowering projection; evidence correspondence is queried
explicitly and is not treated as a type or semantic equality judgment.

The payload container must own all data needed for its retained lifetime and
preserve `HirModule: Send + Sync`; borrowed or non-thread-safe payloads are not
accepted by this API. `Arc<dyn Any + Send + Sync>` with `'static` contents is a
possible transport representation, subject to review of the exact call sites.
The immutable claim applies to binding metadata and allocation ownership, not
deep immutability of arbitrary caller contents: a payload can use interior
mutability through another clone. The transport lemma therefore preserves the
same payload allocation and binding keys, not an invariant that its contents
never change. Any semantic immutability/activity premise remains independently
caller-established. A review finding requiring a different semantic constructor
pauses implementation before that choice is adopted.

## Falsifiers and focused evidence

The transport claim is falsified if a context bound to one parse/module/anchor
is observable as bound to another; if a fresh equal-text parse is accepted; if
the owner can be dropped while HIR still reports it retained; or if mismatches
silently fall back to empty imports. Focused tests may establish only these
structural properties and `SemanticImports::empty()` compatibility. They do
not establish semantic authenticity, source soundness, inference correctness,
or any parent theorem.

## Authority and remaining premise

R24's approved caller-ownership decision supplies responsibility to the
caller; it did not specify this Rust transport API or establish an authentic
semantic instance. The user selected caller-supplied evidence for R25. This
design is the reversible, source-bound transport interpretation of that
choice. The caller's independent construction/justification of an authentic
same-fiber context, all original guards and phase histories, and the unchanged
parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remain OPEN.
