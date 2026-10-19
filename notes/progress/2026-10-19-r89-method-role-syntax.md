# R89 closeout: method/role parser boundary

Date: 2026-10-19  
Sprint: `method-role-syntax-triage-20261019-r89`, revision 2  
Baseline: `6eb68efa47a8272981aca84ad091c61e28868f2b`

## Probe and result

Luna ran the one authorized diagnostic command from revision 1 on the reduced RLD role input. It exited 1 with `Structural(ErrorGroup)` at bytes `59..79`, spanning the role signature `our container.pick: 'key -> value`. The parser rejected the source before candidate inference. No code/test/build was changed under R89.

The earlier complete stable-core `attached_impl_pick` probe reported a structural error over the same role signature and two diagnostics at the later `struct ... with:` boundary. Those inputs expose separate contracts and were not treated as a single parser defect.

The exact R85 snippet with the plain `my second: int -> int -> int` signature passed syntax diagnosis and reached `CandidateInference`, which returned `unsupported source: current candidate lowering/inference cannot observe this program`. This separates parser acceptance from missing candidate role/member semantics. No inference or runtime success was observed.

## Authority trace

- RLD-G/RLD-T in `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` composes role body items from canonical Statements and describes a signature as an ordinary Binding with a Pattern TypeExpression annotation; the example is `our x.eq: T` (around lines 22942, 22974).
- The same authoritative Role residuals explicitly defer identifier + `.field` Pattern continuation and say standalone Pattern does not implement the Y2 dotted target (around lines 23426–23431). This conflicts with the dotted `x.eq` signature example. R89 found no separate adjudication that resolves this scope.
- The Type-Attached Impl addendum (around lines 26962–26984) excludes declaration companion `with:` and companion-member ownership. The stable-core fixture's `struct ... with:` route is outside that addendum.
- The checked-in stable-core expectation remains protected. Its existence does not tell the parser which of these deferred/conflicting syntax boundaries to implement.

Thus R89 does not establish that the observed diagnostic violates one unambiguous approved grammar clause. No parser workaround or expected-output change is safe under the current decision surface.

## Next decision and preserved scope

Two concrete routes remain:

1. Adopt the reviewed R85 positive `Role::member` offer, exact SHA-256 `fee3feaec5e8873fe4f056df3a9ae9ca16c342f0a8b314c027a35719eedd4609`, then issue a separate proof-backed role/member source→constraint→runtime implementation sprint. The syntax already parses; CandidateInference and runtime dispatch remain unimplemented.
2. Prioritize dotted role targets and type-attached `with:` from the stable-core fixture, first with an independently reviewed syntax addendum that resolves the RLD conflict and companion owner.

The user's broad request favors method/role progress but does not select between these exact routes. R85 remains AWAITING_USER_ADOPTION. All six effect-hygiene fronts, original Simple-sub/evaluator A/B (OPEN 0→0), source/native correspondence and production remain open; R50 remains NOT_ADOPTED. No workers or Astra were used for this primary-only triage; the three inherited UNKNOWN identities and board quarantine remain untouched.

R89 contract revision 1: SHA-256 `f8e7222ef60035ae7a2a6844ae756536a009ca1cd81d18a8c94deb19bf10f0d3`.  
R89 revision 2: recorded in `tasks/agent-loop/sprints/method-role-syntax-triage-20261019-r89-rev2.md`.  
Governing architecture at inspection: SHA-256 `08beb9711c2373e161a408b19a6ccd6c08e24e0b41791e7fac2ea0a332dec1ed`.  
Current next action: user selects one exact method/role scope; no semantic adoption is inferred from the broad priority request.
