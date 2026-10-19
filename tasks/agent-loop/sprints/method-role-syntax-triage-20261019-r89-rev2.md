# R89 revision 2 — method/role syntax boundary adjudication

Status: COMPLETE; no source or test writes.  
Revises R89 revision 1 (`tasks/agent-loop/sprints/method-role-syntax-triage-20261019-r89.md`, SHA-256 `f8e7222ef60035ae7a2a6844ae756536a009ca1cd81d18a8c94deb19bf10f0d3`).  
Baseline: `6eb68efa47a8272981aca84ad091c61e28868f2b`.

## Fixed result

The one R89 command ran on:

```yu
role Pick 'container 'key:
    type value
    our container.pick: 'key -> value
my answer = 1
```

It exited 1 before candidate inference, reporting `Structural(ErrorGroup)` at bytes `59..79`, exactly `our container.pick: 'key -> value`. This is a parser diagnostic, not an inference/runtime result.

The RLD Role grammar says its signature surface is an ordinary `BindingStatement` whose target is `Pattern [PatternTypeAnnotation]`; its explanatory example uses `our x.eq: T`. The same RLD residuals section explicitly defers the `Pattern` identifier + `.field` continuation (`container.fold`, `container.index`, `a.show`) and records that standalone Pattern does not implement it. These statements conflict for dotted role signature targets. The stable-core `attached_impl_pick` fixture also uses a type `with:` companion; the Type-Attached Impl addendum explicitly excludes declaration-companion `with:` and companion-member ownership. The full fixture therefore crosses two separate boundaries and cannot authorize a parser workaround by itself.

The exact R85 source with a plain signature target (`my second: int -> int -> int`) produced no syntax diagnostics; `yu-playground` proceeded to `unsupported source: current candidate lowering/inference cannot observe this program`. That is evidence of parser acceptance followed by missing candidate semantics. The latter remain behind R85's exact adoption gate.

## Disposition

No code or test fix is authorized by the existing syntax surface for the dotted target because the Authoritative document itself contains conflicting statements. No parser error is suppressed, no candidate source is admitted, and no dispatch rule is inferred. R85's positive `Role::member` offer is a separate route that avoids dotted target syntax; its parser accepts the exact proposed source, while CandidateInference does not yet implement it.

The next user decision should select the method/role route and settle the precise scope:

1. Adopt the exact reviewed R85 positive `Role::member` contract (canonical SHA-256 `fee3feaec5e8873fe4f056df3a9ae9ca16c342f0a8b314c027a35719eedd4609`) and proceed to a separate proof-backed implementation sprint; or
2. prioritize stable-core dotted role signatures and type `with:` companions, which needs a reviewed syntax addendum resolving the RLD internal conflict and the companion ownership boundary before implementation.

This is a genuine language-scope decision. Neither option closes the six effect-hygiene fronts, original Simple-sub/evaluator A/B, source/native correspondence, or production gates. R50 remains NOT_ADOPTED. The next runnable milestone under option 1 remains conditional until the user selects that exact contract.
