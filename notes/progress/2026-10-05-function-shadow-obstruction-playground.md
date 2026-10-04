# Function shadow entry-path obstruction playground

Date: 2026-10-05
Status: bounded executable characterization of a proof-core witness
Review: one independent compiler_referee found no findings.
Governing result: [certified callback transport and finite constrained uses](../design/2026-10-04-certified-callback-and-constrained-use.md)
§7; [concrete compatibility](../design/2026-10-03-concrete-compatibility-boundary.md)
§3; charter §21 and typed-core §§6, 9.

[`tools/research_function_shadow_obstruction.py`](../../tools/research_function_shadow_obstruction.py)
executes the one-request, constant-Unit, singleton-state witness. The inert
argument exposes request `q` and resumes with Unit. A Value-entry receiver
forces it, so `q` remains visible with the constant body as its pending
continuation. A retained Computation-entry receiver whose body ignores the
carrier returns Unit without exposing `q`.

Both receivers have the same value-only structural shadow `(Unit, Unit)`, while
their complete observations differ:

```text
Value entry:       request q; continuation returns Unit
Computation entry: return Unit
```

The reviewer confirmed that the implementation matches this exact bounded
witness. Its request object stores one response and resumed state; it does not
prove general bind or state-threading behavior. This is executable evidence
against reusing the pure structural comparison after erasing entry/provider
information. It is not a Yulang source-program counterexample, a complete
`A <: B` result, or a production endpoint query. The pure structural theorem
remains valid in its own effect-free domain.

Verification: `python3 tools/research_function_shadow_obstruction.py` passed;
Python source compilation via `compile()` and `git diff --check` passed. No
production compiler code or source fixtures were changed.
