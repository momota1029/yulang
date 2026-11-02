# Canonical literal generation adoption

Status: Authoritative for the abstract Simple-sub literal generator
Approved-by: user, adjudicated by Luna primary
Approved-at: 2026-11-02
Proposal: `notes/design/2026-11-02-canonical-literal-generation-proposal.md`
Reviewed proposal SHA-256: `d5162f2cf08eda28455d0a086205811c12c26d2bf99dff92712ef87934bb3eab`

## Adopted equation

For every original raw literal `l`, the abstract source-directed generator
returns the canonical descriptor and payload-bearing value:

```text
generateLiteral(q,l,ξ; r,e₀,ω) =
  ⟨ source = (q,l),
    synthesis = Value(PaperTypes.literalType(payload(l))),
    value = PaperTypes.Value.literal(payload(l)),
    intrinsicEffect = empty,
    return = Comp(empty, PaperTypes.literalType(payload(l))),
    root = r, event = e₀, scope = ξ, witness = ω ⟩
```

The equation covers all eight original payload constructors: unit, bool, int,
floatBits, string, bytes, path and character. It consumes the original
payload-bearing source node. It does not inspect a source derivation, chosen
typing, `Kernel.atom`, a solver result, or native success to select the
literal's canonical type or value.

## Preserved boundaries

This adoption fixes the mathematical literal-generation equation only. The
arbitrary-solution interpretation into the original descriptor, value, root,
event and effect carriers remains a proof obligation. The generated result
must be connected to the actual original literal-rule consumer under the same
assignment, occurrence, root, event, scope and shared witness.

The source rule's intrinsic effect is empty. Contextual permission, inflow,
residual effects, Call effects, guards, futures, checking alternatives and
conversion obligations remain in the enclosing source judgment. Synthesis,
written target and final root remain distinct ports. This adoption adds no
special-solving step to propagation, extrusion, intrusion or generalization.

This decision does not assert Rust/native correspondence, narrow source
support to currently represented native literal families, decide the pending
typed-Union question, instantiate the complete `SourceProblem`, or close any
parent theorem. Parent-premise delta remains zero until a checked theorem
derives the original constructor premise from an arbitrary satisfying
assignment and consumes it in the unchanged parent proof.

## Authority

The user directed that the proposed definitions be adopted and that Yulang's
inference guarantees be pursued with definitions that support a Lean
soundness proof. Luna adjudicates that instruction as approval of the exact,
bounded R237 equation above. The separate user authorization to generate Lean
caches changes only verification resources and is not the source of this
semantic decision.

L1 remains the authority for the original source introduction. This adoption
resolves only the generator-authority question identified by R237; it does not
resolve carrier interpretation, arbitrary-solution readout, source-rule
application, principality, termination or implementation correspondence.
