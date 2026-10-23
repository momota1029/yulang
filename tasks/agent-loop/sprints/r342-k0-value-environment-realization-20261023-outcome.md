# R342 outcome — K0 finite-return value/environment realization

**Status:** closed as a bounded research sprint after fresh independent review.
The candidate suppliers `R342-K0-VREAL-FINITE` and
`R342-K0-CAPTURE-ENTRY` are accepted only for authentic K0 finite matching-
return segments and the corresponding actual function body-entry boundary.
They do not assert that a segment returns, close full M, or promote a compiler
or production gate.

Frozen contract rev1 SHA-256:
`deffbf0301cef182a208420856804896a412f51a4adc14d94bafc96621d98b64`.
User audit SHA-256:
`b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`.

## Dispositions

- **`R342-K0-VREAL-FINITE` — bounded PASS.** The proof defines finite source
  values/environments, independent D0 typing and runtime representation before
  execution. Four projection maps invert the complete Function preorder,
  including bounds, finite joins/meets and variance. Function and Bool
  canonical forms follow by inversion of actual `TypedVal₀` introduction;
  they do not assume a Function-shaped expression is callable or that a
  bottom-typed environment is inhabited. Strong induction on the length of an
  actual finite matching-return segment covers literal, parameter Name, Value
  Lambda, Apply, else-complete If, Group, and binding-free Block/StatementBlock.
  The Apply case uses the actual returned handle and exposes strictly shorter
  callee, argument, and body segments. No return existence or termination is
  inferred.
- **`R342-K0-CAPTURE-ENTRY` — bounded PASS.** The actual Lambda allocation
  supplies its handle, formal, body label and saved environment. Exact parameter
  lookup, append-only capture identity, both dictionary branches, the
  same-value argument handle/view through `ValueEntry`, and the resulting body
  environment are related to the independent source objects. Authentic K0
  takes the dictionary-absent branch by the pinned constructor/source census;
  the generic present-branch result is limited to lexical cell and value
  identity and does not assume inert or idempotent dispatch substitution.
  Composition with R340 retains the whole caller-argument Delay, distinguished
  Callee/frame prefix, owner, actual invocation, matching return and exact
  ValueEntry body entry.
- **No compiler defect / no safe code slice.** The source census and referee
  found no reachable authentic typed K0 mismatch. No code or test changes,
  probes or build changes were authorized or made.

## Independent review and frozen evidence

Fresh non-contributor `/root/r342_value_environment_review`
(`compiler_referee`) returned bounded PASS with no BLOCKING, major or minor
finding. The review separately checked the projection/canonical-form rules,
non-circular finite-segment induction, all seven K0 forms, lookup/capture and
dictionary behavior, and R340 composition. It distinguished missing premises
from reachable compiler counterexamples. All 15 supplied artifact/source pins
matched before semantic review and again at cessation. Reviewer stopped at
2026-10-23 07:23:13 UTC; the aggregate 1,200-second review grant was charged,
including the earlier capacity-failed partial turn. The review was read-only;
no tests were run. Existing relevant test bodies were read only as context and
were not treated as proof. No builds, probes, Git operations, writes or
descendants were used.

| R342 artifact | SHA-256 |
| --- | --- |
| Primary source census `notes/theory/2026-10-23-r342-k0-value-environment-source-census.md` | `18a4eef622ee8feacc8db48d4360321fdcbd8d5f330636866705f42b8551b1b5` |
| Proof rev1 `notes/theory/2026-10-23-r342-k0-value-environment-realization.md` | `ab5b86070acbb75639172ce96182a1ea08bdc8fe22f185d691fe542a80fee420` |
| Producer handoff rev1 `tasks/agent-loop/inbox/20261023-r342-k0-value-environment-prover.md` | `fdb61f3c065ea734d4162f4d3b880ac7c87ce2f181d80f20f3bfecec8358ca45` |
| Contract rev1 `tasks/agent-loop/sprints/r342-k0-value-environment-realization-20261023.md` | `deffbf0301cef182a208420856804896a412f51a4adc14d94bafc96621d98b64` |

The proof author `/root/r342_value_environment_prover` stopped writing at
2026-10-23 07:16:07 UTC. Its full 2,400-second reservation was charged
conservatively because exact elapsed time was unavailable. The primary census
grant was charged at 2,100 seconds; independent review was charged at 1,200
seconds. Luna charged the final 300-second integration grant conservatively,
for a full 6,000-second envelope. No carryover is permitted.

## Remaining gates

`R342-M-REST` remains **OPEN**: same-witness native result/future interfaces,
effect/continuation interpretation, whole preservation/progress, and
unavailable-step exclusion remain separate. VREAL outside K0, full N/cache
coverage, W, Z, model existence, principality, broader source completeness,
export transport, original Simple-sub A/B and production remain **OPEN**.
R341's conditional S0 retains exactly its existing four premises and is not
strengthened by this result.

The static `python3 tools/agent_sprint.py check` passed. It is workflow/static
evidence, not mathematical proof or independent review. No unit tests, Cargo,
builds or runtime probes were run.

## Luna integration amendment — revision 2

This appendix changes only the Git integration receipt; the bounded mathematical
disposition above is unchanged. Revision 1's outcome bytes had SHA-256
`0ce866e9a31bd3a34dc833f94e10956980e4379dc1aaa52562b9c07520e99382` and are
preserved in the preceding Git commit.

Luna staged exactly the six approved R342 paths: contract, primary source
census, proof, producer handoff, outcome receipt, and `current.json`. The
user-provided audit document was excluded and remains untracked. Commit
`14de45d21d673cc1beaf718b393e704c9a651fa1` was pushed successfully to
`origin/research/simple-sub-intrusion`; local HEAD and upstream matched that
commit after the push.
