# Applied producer and descriptor-to-seed bridge

The applied concrete-only producer is integrated in checkpoint
`24be694c5` and its accounting repair was reviewed/integrated in the same
checkpoint. The producer milestone remains bounded: it does not admit the
negative concrete source form or close
`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`.

This sprint advanced the proof and implementation-readiness lanes:

- The internal producer constructs both polar Function terms over one fresh
  row, retains an inert Permission on the exact typed path, and publishes after
  ordinary links 43/44. In a live unchanged construction snapshot,
  `formal_domains[parameter]` and the path recover the exact raw effect-row
  occurrence. This is a candidate constructor lemma, not a theorem.
- A source-owned Operation seed, exact physical emission/admission, and checked
  FunctionPort/ordered Replay evidence can support a conditional native
  incidence certificate at that recovered port. No current consumer validates
  it as adopted `At(D,w,delta)` or realizes the complete original dependent
  witness `w`.
- Source preflight rejects the negative concrete row before it emits the
  FormalAnnotation action. That is the first missing source event. The next
  source gate needs its owning source-signature authority; the N-Ingress gate
  needs formal-construction, Function-propagation, emission, and context
  consumer owners. No new event ID has been shown necessary.

Proof artifact:
`notes/theory/2026-10-17-npair-applied-producer-seed-bridge.md`, SHA-256
`45cfefb49b6a1ca567ea603558c95b0dfed22a776b23d3b5ed200e373befa579`.
Proof handoff SHA-256:
`986c4391063348592d6be13c9db549692b1fdcefcbc5eb72dd1ad5da68150a12`.
Readiness Draft:
`notes/design/2026-10-17-npair-descriptor-seed-association-contract.md`, SHA-256
`9f4e2d9f2ccc6f972d9a6eb99910a0e9a44c982eda0646f512f687ec9d518395`.
Readiness handoff SHA-256:
`b96b55b05992748f89842e417ce035f83a9df6cce12109043d28ec1a295c5dde`.

Fresh compiler-referee and architect reviews of the frozen outputs were both
CLEAN. They confirmed the constructor/path inverse and reviewable conditional
certificate while preserving the open source-admission, semantic-witness,
lifecycle and consumer gates. Primary adjudication accepts the outputs as
candidate static evidence and an unapplied readiness Draft only. They carry no
compiler, source, consumer or semantic-change authority.

No tests, builds, Cargo, probes or source/compiler execution ran. The static
`python3 tools/agent_sprint.py check` passed; it is consistency evidence, not a
proof check or independent review. Sprint envelope usage was 1350/1560 seconds:
proof 720, readiness 360, coordination 30 and two reviews 240. Optional
compile-only verification, unused coordination allocation and reserve are
retired at close without transfer.

The next useful work is to turn the precise source-admission and N-Ingress
frontier into separately owned, reviewed gates while continuing the original
receive obligation. Keep source admission, authentic `At`, transport,
whole-presentation `rho_u`, actual receive consumption, subtraction, F1/FK1,
soundness, principality and production OPEN.
