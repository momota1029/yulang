# NPAIR concrete producer correspondence audit

Status: Luna source-owner audit; proposal only, not an independent proof or a new semantic adoption.
Sprint: `npair-native-introduction-correspondence-20261018`, contract rev2.

## Audited construction

The adopted N-Port-Intro and user-approved code contract permit only the internal
nonempty concrete-only producer in `candidate_effect.rs`; source preflight refusal
remains in force. The direct producer path is:

- `candidate_formal_effect_port` allocates one `fresh_effect_at_level(level)`
  for each negative concrete-only row, then creates positive and negative live
  effect terms from that same ordinal.
- It appends a `FormalPermission` copied from that exact row and the recursive
  `Argument`/`Result` path. The descriptor carries parameter, occurrence,
  source owner, scope, source row key and concrete IDs; it intentionally carries
  no solver row ID or consumer authority.
- Recursive Function construction preserves all four children. On the
  negative pair the stored children are argument value, argument effect,
  result effect, result value. The argument and result recursion restore their
  path prefix before propagating an error.
- `candidate_formal_annotation` reserves descriptor state, emits links 43 and
  44 from the completed pair, checks retained nested bytes, then transfers
  Permission records and the negative root value into state. The existing route
  transaction is the rollback boundary.

The top-level annotation effect is not collected as a nested Permission: the
entry point invokes `candidate_formal_value_pair` on the root value. This agrees
with the approved contract's separate formal entry handling.

## Row recovery question for the proof lane

The descriptor does not itself retain a row ordinal. Candidate evidence for a
structural recovery is the `formal_domains[parameter]` negative root term,
`TermView`'s four-child Function observations, and the descriptor's typed
Argument/Result path. A path step selects the matching value child for further
descent and its sibling effect child for the permission port. At the endpoint,
the effect term's `LiveVariableView` exposes its component kind, polarity and
ordinal. The construction above establishes the same ordinal for the two
projections at creation time. This appears to give a unique constructor-time
association and a term-tree recovery algorithm without family equality, but
Sol must check every variance branch, path restoration, retained lookup,
source-row identity and rollback before this is counted as proved.

If descriptor `source_row` cannot be tied to the exact path-selected effect
child, or the paired ordinary links do not retain a root from which this walk
is valid, report that exact gap rather than adding row identity or a registry.

## Candidate regression after Sol STOP

If the source parser/schedule supplies an internal annotation fixture safely,
add one unit test only in `candidate_effect.rs`. Call the internal constructor
inside its route transaction and check the retained Permission's exact
parameter/occurrence/owner/scope/path/source-row/concrete payload; walk the
negative root and both link terms by the stored path; assert the exact effect
ordinal and opposite polarities; verify the result and rollback remove all
Permission/domain/link state. The test must say it is an internal producer test
if it bypasses source preflight. Do not use it as evidence of source acceptance.

No code is changed by this proposal. No source admission, mixed/multiple-symbolic
rows, explicit-empty rows, `At`, provider, transport, consumer, subtraction,
F1/FK1, N-Transport, soundness, principality, termination or parent theorem
claim is added.

## Frozen input pins

| Input | SHA-256 |
|---|---|
| Adopted proposal | `0a73aaf7016e86dd5babbdd5482b05a793764418bc003607207ef0375ee46006` |
| Adoption receipt | `d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa` |
| Adopted construction proof | `6a3c6b5754448b38430ee368feb52d87ebd38c1b7050c3b33652132ead5f0fb2` |
| User-approved code contract | `a6b6f37218408b334922c19ff6065bd8bd607294201ec2b371f1376e800c41ce` |
| User approval receipt | `cd81ea1385b1304da283ef8ee15cdd626b98d1759cf79aa372f672e53c5bab67` |
| `candidate_effect.rs` | `11a1477ff2c35c03dccb70bdc6121d89d3ced9fadb1921cb8cf8cd5c093b07fb` |
| `lib.rs` exact live-row/Function helpers | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` |
| `term.rs` TermView lookup API | `f3a0c3875ba1ba8c80ee48a405faf3dad22b57cba8930394f99181201bc58f60` |
| Existing implementation handoff | `f24ba90278a70edbf4a601818755b7c43ee67ec34aa67bf0456ebbf359287cb5` |
| Compile-only receipt | `addd61f1455ddeb36931253d2c36e2c75f7d460e83e6d3773f54093b2f982775` |

The source-action owners `candidate_source.rs` and `candidate_call.rs` remain
UNKNOWN/quarantined and were not inspected for this audit. No source reachability
or consumer is established. Original parent closure remains zero.
