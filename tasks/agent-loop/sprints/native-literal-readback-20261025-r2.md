# LEAN-NATIVE-LITERAL-READBACK-20261025/r2 — direct ASCII byte observation

Status: **AUTHORIZED by primary after bounded dispatcher consultation.**
R1 remains immutable, SHA
`f476c30b01eb0315a97f23ba59ff21d839e298970695162482af8afa3fb230e1`.
Baseline, original goals, source domain, complete response conclusions, producer
coverage requirement and all remaining parent obligations stay unchanged.

## Observed obstruction and concrete repair

Rows1–6 retain elaboration/diagnostic failures around reduction of the custom
decimal fold equation. Row7 compiles after replacing the identical recursion by
List.foldl and proving its recurrence with explicit List.foldl_cons; row8 compiles
the consumer. Row9 retains a query-only missing DecidableEq literal diagnostic,
repaired by constructor inversion. Rows9–11 reveal that String.toList in the
installed Lean4.35 library itself depends on Classical.choice. Thus successful
elaboration was not acceptance under the strict axiom gate. No target is promoted.
Row11 also prints String.toUTF8, Array.toList and UInt8.toNat with no axioms.

Change only the new unaccepted decoder's integer observation to
`text.toUTF8.data.toList : List UInt8`. AsciiDigit is48..57 on byte.toNat;
splitSign removes at most one initial byte45; the remaining list is nonempty.
The positional base-ten fold and signed Int result are unchanged. String input
and the separate String literal payload remain exact strings. No trimming,
Unicode-digit admission, default integer or machine-size truncation is added.
Accepted still reflects only native role/same-value/kind checks. It does not
gain the decoder's validation condition.

ASCII digit/minus characters have their same single-byte UTF8 encoding; all
non-ASCII bytes fail the digit bounds. Consequently this is the same optional
ASCII minus/nonempty ASCII digit grammar and mathematical positional value.
The native source proof already establishes that exact byte grammar, so this
also removes the unnecessary intermediate scalar observation. Helpers in this
new, unaccepted candidate may change Char parameters to UInt8 accordingly;
no previously accepted theorem statement changes.

## Exact lease amendment, evidence and resources

Primary retains the existing two-source/checker/query/receipt leases. Additional
exact primary paths:
- `tasks/agent-loop/sprints/native-literal-readback-20261025-r2.md`
- `notes/theory/2026-10-25-native-literal-byte-readback.md`

The old source argument stays frozen at
`1f73d0a4e221cb2d2a182876cf9928ebd3cab34edd6d36f4a46bb6bd3ca9a651`.
The new note supersedes only its final Char-observation correspondence with byte
correspondence; its complete producer inventory/loop proof is retained unchanged.
The author handoff remains frozen and explicitly unverified. Earlier source
candidates and diagnostic query text are retained inside the append-only JSONL.
Final acceptance query omits obsolete diagnostic declarations but does not
discard their receipts. Both new modules and the final query must be rechecked
and their actual final axioms inspected, strictly within [propext, Quot.sound].
No new legacy exception or relaxed whitelist is permitted.

The read-only90-second dispatcher consultation is STOPPED and charged; lifetime
consultation budget is870 seconds including prior780. It consumes90 of r1's180
contingency. The final90 contingency seconds transfer to the primary's repair /
source correspondence envelope. Total1800 is unchanged: author300 + primary690
+ Lean120 + reviewer300 + integration120 + dispatcher270, contingency0.
At amendment11 Lean invocations/67.39666158099499 actual seconds are consumed;
remaining21 calls/52.60333841900501 seconds are not reset. All old grants and
failures remain charged; author is STOPPED, reviewer not yet launched. Requested
Astra/medium and observedUNKNOWN remain distinct; three old quarantines persist.

Fresh nonauthor review additionally checks byte/scalar grammar equivalence,
empty/sign-only/double-minus/non-ASCII rejection, leading/negative zero,
unchanged String payloads, exact producer-to-Grammar application and the strict
final axiom set. Source/native whole-trace, operation-instance, callable,
template/view/environment, full arithmetic semantics and inference A/B stay OPEN.
The existing r1 outcome path remains the one final sprint outcome.
