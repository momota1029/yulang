# Forward realization of the original NPAIR witness

The sprint continued the original `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR`
obligation without changing its source domain or quantifiers. Starting from the
complete original contribution witness `w` avoids reconstructing semantic
witnesses from native IDs, but the path still lacks the source constructor
evidence that relates that same `w` to the exact Operation seed.

The proof identifies two missing premises: `eta_op`, which places the same `w`
at the actual Operation result-effect port in its dependent predecessor context;
and `realization_op`, which relates the actual source declaration/reference
instance and that incidence to the native Operation origin, view, member, port,
emission and admission. FunctionPort and ordered Replay evidence supports only
conditional structural incidence. Adopted `At(D,w,delta)` remains unproved.

The current receive negative-concrete formal still fails source preflight before
the `FormalAnnotation` action. This is separate from the semantic realization
gap. `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN, as do
transport, the actual receive consumer, subtraction, F1/FK1, soundness,
principality and production.

The implementation-readiness result is an unapplied Draft. It bounds a future
structural-only validator and grants no source, compiler, consumer, semantic or
production authority. Two fresh reviewers noted the same minor clarification
for any executable contract: distinguish one-shot validation of a fixed live
snapshot from a persistent subscription to later lowers, and define certificate
lifetime accordingly. This does not block retaining the current Draft.

Frozen outputs:

- Proof: `notes/theory/2026-10-17-npair-forward-source-witness-realization.md`,
  SHA-256 `1d2c827cdf7661cc77a9edbb869bffd3cdcca7b51afba418789eaae9abf3cb3a`.
- Proof handoff SHA-256
  `184bcd86658ef5ed7f77513986b15be13e3f9e3b5223968153cc730fd5e309ad`.
- Readiness Draft: `notes/design/2026-10-17-npair-forward-witness-ingress-code-contract.md`,
  SHA-256 `f1615c43ef74829cde9e53b7169614f015733eb81e40dc5966ba4430189081fe`.
- Readiness handoff SHA-256
  `bdd4c84d3deb238682e3953cb64ee653a015426588e7f5f0eb8314d55bc8591b`.

Three sequential fresh reviews covered the frozen bundle. The compiler referee
reported CLEAN. The architect found no blocking issue and gave a LOW lifecycle
clarification. The spec auditor found no blocking or major conformance issue and
gave a minor clarification on that same boundary. All five bundle hashes and
all 21 proof-manifest dependencies matched during review. Primary adjudication
accepts these as candidate static evidence and an unapplied Draft only.

`python3 tools/agent_sprint.py check` and `git diff --check` passed. No tests,
builds, Cargo, probes, or source/compiler execution ran. The sprint charged
1890/2100 seconds; the unused 90-second coordination remainder and 120-second
reserve are retired without transfer. Parent and production gates remain OPEN.
