# Declaration companion Gate 3 speculative NUD sink amendment

Status: Authoritative

Approved by the user on 2026-08-31 by selecting option 1: repair the generic speculative NUD
candidate at its owning responsibility, with bounded verification and no companion-local masking.

This amendment is narrow. It changes only the ErrorSink transaction contract of
`expression_nud_candidate_input` and the minimum Gate 3 evidence required to close the discovered
sink leak. Every declaration-companion grammar, CST/AST, recovery, gate-order, and production-
reachability rule not named here remains governed by the existing Authoritative documents.

## 1. Discovered contradiction

Gate 3's isolated braced companion parses `with { first }tail` with `ml_arg(false)`, as required for
a real braced Statement sequence. After accepting `first`, canonical expression parsing probes for
an ML argument. `expression_nud_candidate_input` runs speculative NUD recognition on `}`, restores
input and `ParseLocal`, but does not restore the separate Chasa ErrorSink checkpoint. It therefore
leaks `Unexpected('}')` at the companion-owned close.

A state-equivalent canonical control reproduces the leak. The earlier clean control was invalid
because its test scope used `ml_arg(true)` and bypassed the candidate query. The defect is generic
candidate ownership, not declaration-companion close/trivia logic.

## 2. Owning fix

Authorize exactly this production change:

1. `expression_nud_candidate_input` checkpoints the incoming ErrorSink immediately before its
   speculative NUD recognition;
2. it preserves the existing input and `ParseLocal` checkpoint/rollback;
3. it rolls the ErrorSink back before returning, for both accepted and rejected candidate results;
4. it returns the same boolean and changes no input, local state, AST, CST, recovery record, range,
   or boundary decision.

The rollback removes only expectations created inside this boolean candidate helper. Incoming sink
entries must remain byte-for-byte and order-identical. Committed nested parser expectations and
direct-CST committed recoveries remain owned by their existing parsers and outputs.

## 3. Narrow supersession

For this one helper only, this amendment supersedes:

- the recovery amendment §3 restriction that only its three listed ordinary helper bodies may
  change;
- the Gate 2 performance amendment §§2–3 zero-added-work/protected-helper clauses, solely to permit
  one ErrorSink checkpoint and one ErrorSink rollback on each existing
  `expression_nud_candidate_input` invocation.

No tolerance percentage or general hot-path exception is created. The accepted operation delta is
exactly two sink-transaction operations per existing helper call. All other Gate 2 operation-ledger
rows and protected bodies remain closed and unchanged.

## 4. Forbidden alternatives and expansion

This amendment does not authorize:

- a companion flag, owner branch, runtime mode, or caller-specific sink clearing;
- clearing the sink around a whole Statement or companion form;
- changing `ml_arg`, generic `WithBodyTail`, separator, close, or owner-boundary behavior;
- a duplicated NUD decision table, rescan, allocation, cache, replay, indirect dispatch, or new
  candidate call;
- Gate 4 Derives priority, owner attachment, or any Gate 5–10 production wiring.

Companion-local cleanup is rejected because it can erase legitimate nested canonical expectations.
Changing `ml_arg` is rejected because it changes Statement grammar. Special-casing `}` is rejected
because it duplicates boundary authority and leaves the generic sink leak.

## 5. Verification and budget

Use one table-driven focused group covering:

- rejected `}` candidate with an empty sink;
- rejected and accepted candidates with a pre-seeded sink, proving incoming entries survive exactly;
- state-equivalent ordinary `first }tail` control;
- isolated AST/direct `with { first }tail` with clean sink and unchanged CST/remainder/recovery;
- one nested malformed canonical case proving committed expectations are not erased;
- the already-required Gate 3 introducer/comment, boundary, recovery, state, and direct-child CST rows.

Audit all current `expression_nud_candidate_input` call sites and record that the change adds no
call, branch, recognizer pass, allocation, or rescan. Run the focused group during repair and
`cargo test -p yu-syntax` exactly once on the final closed candidate. Do not run a workspace suite.

Timing is not a default closure condition because the user explicitly selected bounded semantic
accounting. If independent performance review cannot close the exact call-frequency/operation
ledger statically, one representative diagnostic is allowed: at most one warm-up pair plus three
measured pairs, eight processes and ten minutes total, with no extension or Cartesian cases.

## 6. Review and rollback

Mode is M2. Required independent closure roles are:

- `compiler_referee` for ErrorSink transaction semantics, nested expectation preservation, and Gate
  3 recovery ownership;
- `performance_auditor` for the exact two-operation delta and call-site ledger.

Rollback or stop if any incoming sink entry is lost or reordered, any committed nested expectation
disappears, any AST/CST/remainder/recovery/range/boundary changes, work exceeds the two authorized
sink operations per existing helper call, or call-site/static accounting remains inconclusive.
