# Question: close the original-registry representation cut

Question ID: `call-reify-registry-construction`
Question revision: `q3`
Predecessor/history: approved `q2/d1` (integrated at `a4e789ee4`); q1 remains preserved as pending history
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revisions: `e8e037ecf` (current records), `fe3a73734` (selected-source P_old construction attempt), `c0d304113` (separate unadopted L construction)
Task/thread locator: current conversation; no stable external identifier is available
Governing sources: `notes/design/2026-10-10-call-reify-construction-direction.md`; `notes/theory/2026-10-10-selected-source-p-old-construction-attempt.md`; `rules/design-authority.md`; `rules/compiler-engineering.md`

## Requested scoped decision

The complete Call contract for `f 1` remains fixed. Approved q2 adopts the four reviewed tagged-Reify construction choices and directs source-grounded construction/conformance for the actual original registry `P_old`; it does not authorize implementation.

The selected-source construction attempt now grants the actual formal registration `reg_f : Reg(beta)` and its Name route, then stops at the missing representation bridge:

```text
reg_f : Reg(beta)
  → k_f : Key_old(P_old), payload_f,
    lookup_old(P_old,k_f) = Found(payload_f),
    decode_old(payload_f) = the same complete reg_f/interface record
```

The inspected selected rules construct and consume registration records, but none connects this actual registration to a key/payload in the same original `P_old`. The adopted `N_arg` and `N_lit` sorts are intentionally distinct and cannot provide that bridge. Exhaustive old-entry coverage and complete old-consumer closure remain separate obligations. The unadopted `c0d304113` `RuleCall_L` extension retains `P_old` and does not fill the gap.

Choose how to proceed if the existing source does not supply this representation certificate. This question does not reopen the full Call contract, select four-port solving, or authorize compiler implementation, `f 1` acceptance, solving, publication or F5 cutover.

## Background and evidence

- The [approved q2 direction](../../../notes/design/2026-10-10-call-reify-construction-direction.md) requires actual `P_old` construction/conformance and keeps all complete Call fields.
- The [frozen attempt](../../../notes/theory/2026-10-10-selected-source-p-old-construction-attempt.md) derives only a conditional `F_form`; its §4 isolates the single-registration lookup/decoder gap, and §5 separates exhaustive entry coverage and consumer closure.
- The focused [selected-source map](../../../notes/progress/2026-10-10-call-reify-actual-registry-manifest.md) confirms that Parameter, `OShared-Register`, IF, SIG and Original-ResultLiteral provide their local records but not the complete original registry bridge.
- The original Call owner definition §§2–3 takes `Reg(beta)` as an input and derives `SharedPositions(reg)`; it does not define the original registry installation/lookup operation.
- The new formal registration in `c0d304113` belongs to its separate `Reg_L`/`P_L` interpretation. That extension remains unadopted and cannot be treated as original registry evidence.
- The compiler-engineering rule classifies facts already known and discarded by an owner as reconstruction debt, but requires actual evidence before claiming that a retained certificate is available. A new original registry rule or key interpretation would be a durable design choice.

## Options and consequences

1. **Keep the original registry meaning fixed and continue searching for its authentic owner evidence.** Require the existing registration phase to produce the typed key/payload/lookup/decoder certificate and then close entry coverage and actual consumer maps. If no such phase exists, leave this Call gate blocked and report the exact missing owner. This avoids adding source semantics, but `f 1` remains unavailable on the complete-contract path until evidence is found.

2. **Open a reviewed design gate for an explicit source-owned original registry constructor.** Define the original key/payload formation, lookup, absence, alias/sharing and complete consumer laws at the owning source-registration phase, preserving existing source behavior and every complete Call field. This may supply the needed evidence naturally, but it adds a durable original-registry rule that needs independent design review before any implementation gate.

3. **Keep `P_old` as an external premise and park this Call path.** Continue independent inference work without expanding the original registry design. The complete Call contract remains unchanged, but this route makes no progress toward ordinary `f 1` inference until an already selected owner supplies `P_old`.

No option authorizes implementation or weakens effects, protection, admission, licensing, images, provider/world fields, pending/future behavior, or principality requirements.

## Affected work

Blocked scope: choosing whether the source language's selected registration boundary already owns the original registry lookup/decoder certificate or whether a new original-registry design gate is needed. The next dependent Call construction cannot claim `P_old` completeness without that answer and source evidence. Independent annotation, solver and other inference gates may continue where their dependencies do not include this registry.

Required answer: select Option 1, 2, or 3, or state another bounded direction. This question bundle remains local, uncommitted and unstaged until its matching answer is explicitly approved and integrated by the questioning primary.
