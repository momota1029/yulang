# Constraint replay deduplication investigation closeout

Date: 2026-07-16

Status: investigation closed as a negative/informative finding. No implementation was done, none
is planned, and the project is not being pursued further at this time.

## 1. Purpose and investigation trigger

Throughout the 2026-07-15/16 session, constraint replay deduplication was repeatedly flagged as
correctness-sensitive and requiring a separate investigation. `ConstraintTiming` reported that
`lower_replay_duplicate` and `upper_replay_duplicate` classified approximately 87% of all replay
inputs as duplicates. For Yumark Markdown, 836,781 of 957,939 total replay inputs were classified
as duplicates, or 87.35%.

The investigation asked whether that rate represented remaining replay work that could be removed
without changing inference semantics.

## 2. Investigation method

A read-only Sol-tier Codex characterization pass covered:

- `crates/infer/src/constraints/timing.rs`;
- `crates/infer/src/constraints/machine/bounds.rs`;
- `crates/infer/src/constraints/machine/entry.rs`;
- `crates/infer/src/constraints/machine/propagate.rs`;
- `crates/infer/src/constraints/directed_weight.rs`.

The pass also freshly re-measured the Markdown, HTML, repository-std-only, and showcase fixtures.
Finally, it activated the existing env-gated evidence-only-skip prototype and tested that prototype
against the current workloads.

## 3. What `duplicate` measures

Here, `duplicate` means that the replay candidate's canonical composed-weight key already exists in
the global `seen` set. That set is populated before work is queued. The counter therefore does not
identify a missing local `(variable, bound)` deduplication check.

## 4. Early rejection is already near-perfect

On Markdown, 836,705 of the 836,781 duplicates, or 99.991%, are caught at the earliest point before
any replay snapshot or queueing. Only 76 are caught later.

Unlike several precheck-ordering fixes made earlier in the same session, this path has no remaining
opportunity to move a cheap precheck earlier.

## 5. Structural cause of the duplicate rate

The high duplicate rate is a structural consequence of transitive closure. Many independent
lower/upper bound pairs legitimately rediscover the same already-known global var-var consequence
through different derivation paths.

A fresh shadow-mode check found zero repeated local bound-frontier keys on Markdown: 219,232 var-var
insertion candidates and 0 repeats. This confirms that the measured duplicates are not
wasted or redundant local work.

## 6. Correctness and end-to-end counterevidence

Activating the existing env-gated evidence-only-skip prototype against the current Markdown
workload changed exported public type schemes. In particular,
`std.control.nondet.nondet.#act-method:guard` lost a callback effect variable and its residual effect
from its public signature. `std.text.str.ref_lines` and other weighted effect schemes also changed.

This is a silent public-API-shape change. It confirms that the earlier correctness-sensitive
concern was correct, not just cautious.

Even ignoring correctness, the prototype produced no end-to-end speedup. Markdown one-shot total
time was 4.945s at baseline and 5.073s with the prototype enabled: slower, not faster.

## 7. Current performance context

Fresh measurement places constraint drain, the replay-related phase, at approximately 6.3% of
Markdown's total compile time: 312.8ms of 4.945s total. It had been a much larger share earlier in
the session. The owner-level dirty scheduling project, completed immediately before this
investigation in commit `1501e96f`, had already reduced overall compile time from approximately
14.36s to approximately 5.37s.

The HTML, repository-std-only, and showcase fixtures still place constraint drain at roughly
30-33% of their much smaller total times.

## 8. Ranked options considered and not pursued

All three options are recorded only for a possible future revisit. None is being pursued now.

1. **NOT pursued now: semantics-preserving weight-composition micro-pass — size S, risk low,
   likely-small payoff.** Only 10 terminal-weight-erased cases were found.
2. **NOT pursued now: interned weight-ID composition cache — size M-L, risk medium-high.** This was
   previously attempted and regressed because hash and clone overhead outweighed the savings.
3. **NOT pursued now: first-class weighted routing/evidence frontier replacing materialized
   transitive bounds — size L-XL, risk very-high.** This is the only route that could meaningfully
   cut the transitive materialization cost, but it requires a from-scratch evidence-representation
   decision touching replay, adjacency, selection, method taint, and generalization. It explicitly
   requires a separate human decision before any implementation and is not a mechanical follow-up.

## 9. Closeout

The ~87%/99.991% numbers are not evidence of remaining waste to eliminate -- they are evidence of
how effectively duplicate work is *already* being rejected before any expensive work happens. The
investigation is closed with no implementation planned; the project is NOT being pursued further
at this time.

Investigation: Codex (gpt-5.6-sol), 2026-07-15/16 session.
