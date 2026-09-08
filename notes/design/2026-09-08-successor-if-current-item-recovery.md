# If current-Item typed recovery

Status: Authoritative; private O3b construction pending

Date: 2026-09-08

Approved-by: user through the recovery-selection and simplification delegation
in `2026-09-08-successor-recovery-authority-amendment.md`

Scope: raw recovery owned by `expression/if_expr.rs`: a completed condition
without its body introducer, inline If/Elsif body absence or Error retry, and
bare/colon-introduced Else body absence. Condition, indented blocks, CaseLike,
accepted If grammar, outer-tail association and public dispatch are excluded.

Authority: the architecture's If mandatory-slot contract, typed-output
amendment §§3--6, required-operand and indented-statement role contracts, and
recovery-authority amendment §§1--3. Existing roles are sufficient; this
record selects their immediate-owner publication without adding vocabulary.

## Roles and records

| site | role | expected |
| --- | --- | --- |
| completed If/Elsif condition without a body introducer | `IfExpression(BodyIntroducer)` | punctuation Colon |
| initial If/Elsif inline body absence or malformed run | `IfExpression(Body)` | Expression |
| bare or colon-introduced Else inline body absence or malformed run | `IfExpression(ElseBody)` | Expression |

The introducer site publishes exactly one Missing. It does not infer a body
from a following ordinary Item. Each inline Missing uses its mapped role. Each
inline Error uses the arm's mapped Body or ElseBody role, one `Expression`
expectation, and one `OtherCharacter` token fact over the actual nonempty
emitted run. Every record has one `COMMITTED_RECOVERY_RULE` expectation and
primary index zero; Missing is zero-width with no unexpected fact.

## Boundary and continuation

Preserve the current If owner flow. A missing Condition without an accepted
body introducer remains solely the already-typed Condition recovery and
suppresses an additional introducer/body record. Once an actual colon is
accepted, its body remains an independent required slot even when the
Condition is missing: `if :` publishes Condition then Body Missing, and
`if : @` publishes Condition then Body Error. The same applies to an Elsif.
For a completed condition, an ordinary pending Item's remaining leading is
emitted into the arm before BodyIntroducer Missing; an abstract boundary remains
wholly pending. EOF leading already owned by the condition exit is preserved
before the anchor. The returned Item, suffix and line entry are unchanged.

Inline body absence at an abstract boundary emits Missing without its leading.
At an ordinary non-newline boundary, current remaining leading is emitted into
the arm before the Body/ElseBody Missing; an implicit newline keeps its leading
with the protected Item. EOF, separator, active stop, implicit newline and
current-depth `{` remain absence boundaries exactly as today. Do not broaden
that predicate to every unread close or bracket opener.

Before an Error, initial body leading is emitted by the arm. Internal leading
belongs to the one sealed lexical Error; retry and terminal-boundary leading
stays outside Error. Scan one maximal nonempty run through the existing lexical
Expression scanner, stopping before a NUD, an absence boundary above or an
abstract boundary. Error never calls a grammar parser/builder, replays source,
retains a run vector or nests recovery. Retry an admitted NUD outside Error in
the same threshold/ML/stops/line/fence/ambient/sequence context; at a boundary,
return unchanged with no second Missing.

`condition_normalized` retains its shared required-operand boundary flag and
Condition role. `colon_body_normalized` retains the existing
`IfExpression(IndentedStatement)` Statement contract for If, Elsif and Else.
The literal/nested owner selects its own role; child records precede any arm
continuation recovery. No change to keyword probes, flat OperatorChain,
association, ambient/sequence transport or accepted layout follows from this
publication gate.

## Required evidence

Add direct fresh, shifted, frozen and seeded exact records for BodyIntroducer,
Body and ElseBody; bare and colon Else; missing Condition no-cascade; malformed
one/multi-Item runs retrying a literal, prefix and nested If; actual-colon
missing/malformed bodies after missing If/Elsif Conditions; and accepted
recovery-free If controls. Prove comma/active close/Elsif/Else/dedent/brace,
ordinary EOF, LF/CRLF, UTF-8 and quoted-fence boundaries before and after Error
preserve complete pending Items, leading, origin and line entry. Exercise root,
statement and delimited callers without changing source literals or accepted
products.

M2: one implementation pass, compiler/recovery plus regression review, and at
most one repair bundle. Run focused If/expression/indented/output controls,
package check, format and diff. Benchmark use is zero unless material work
uncertainty appears. Synchronize task, ledger and daily record before commit.
