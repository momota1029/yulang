# LeadingEffectTypeHead current-Item recovery

Status: Authoritative; private LeadingEffectTypeHead construction complete

Date: 2026-09-08

Scope: the mandatory Type head after a leading BracketRow, its disabled
second-row recovery, and the now-obsolete dedicated balanced-suffix lexer.
Also corrects only the T7a/T7b witness spelling in the adoption matrix.
Record/forall, embedded/header-full and aggregate O6/public adoption remain
outside this gate.

Approved-by: user through the recovery-selection and simplification delegation
in `2026-09-08-successor-recovery-authority-amendment.md`

Drafted-and-checked-by: primary under the user's no-subagent instruction

## Accepted syntax and supersession

Retain the architecture's BR-G/N/L/H accepted grammar: one leading row followed
by an allowed Type primary, within the same TypeExpression. Preserve its
ordinary/terminal disposition, Type-ML context, attachment and full Type tails.
A second bare leading row remains invalid. No accepted-source control changes.

BR-H's incomplete-head Missing and same-slot Error retry remain the basis.
Replace the speculative balanced raw suffix with one total current-Item run.
This supersedes only BR-H's malformed balanced-unit policy where the following
explicit boundary rule stops before a later matching close, its opaque raw
token representation, and ordinary-unmatched transactional handoff. It also
replaces the private normalized tests' raw-suffix newline/comment ownership.
The normalization addendum's physical-prefix, exact boundary, and one-forward
invariants remain in force; this owner no longer needs a multiline raw suffix.

## Selected rule

Classify the current head once. Abstract fence, EOF, non-continuation newline,
explicit caller stop, contextual outer boundary, separator and closing
delimiter are boundaries before a head attempt. A fresh boundary emits one
Missing `Type(LeadingEffectTypeHead)`, expected TypeExpression. Its anchor is
the inspected abstract boundary coordinate, otherwise the Item's remaining
start. Only EOF continuation trivia may be emitted before this Missing;
other protected Items, including all their leading, stay pending.

If the first row itself returns incomplete, publish the distinct mandatory
head Missing and return its exact exit. Do not parse another head or manufacture
a head Error. Incomplete row-close and required-head slots are distinct at
both EOF and non-EOF handoff.

For malformed content, emit initial leading at the enclosing TypeExpression
and start one total Error run. Each iteration consumes a complete lexical
Item, retaining its native syntax kind. Within a disabled second `[...]`,
track nested `[]`, `()` and `{}` using a recovery-local matching-close stack;
comments remain opaque Item leading. At any depth, abstract/EOF, caller/outer
boundaries and non-continuation newline end the run before the whole Item.
A close matching the local stack is consumed; any other close stays pending.
Comma/semicolon are local only while this stack is nonempty and no explicit
caller stop claims them. Outside the stack they end the run.

With an empty stack, an allowed primary ends the Error and retries the same
head slot. Another bare `[` starts another local balanced unit in the same
run. Thus adjacent malformed bytes/disabled rows produce one Error, not a
sequence of same-slot Errors. EOF/unmatched input consumes its nonempty safe
prefix; no rollback or closing-delimiter lookahead is performed.

The Error and singleton OtherCharacter unexpected fact cover exactly the
emitted run, without initial or retry leading. Intermediate malformed leading
belongs inside Error. A run ending at a boundary produces no head Missing;
continuation EOF trivia is emitted outside Error. All records have one
same-role/range TypeExpression expectation, COMMITTED_RECOVERY_RULE sources
and primary index zero. Missing has no unexpected facts. There is no second
BracketRow or synthetic TypeExpression node for the malformed units.

## Pre-write controls

| source | selected records / continuation |
| --- | --- |
| `[e] T`, `[e] F [io] -> U`, `[e] for 'a: T`, `[e] :{A}` | no recovery; existing attachment and terminality |
| `[e]` / `[e] ` | head Missing at `3` / `4` |
| `F([e] )` | head Missing at `5`; Call owns space and `)` |
| `[e]\nT` | head Missing at `3`; newline/`T` Item pending |
| `[e][f]T` | head Error `3..6`; `T` retries the same primary slot |
| `[e][f` | head Error `3..5`; EOF, no same-slot Missing |
| `[e] @ [f] T` | head Error `4..9`; retry space outside Error |
| `[e][f][g]T` | head Error `3..9`; one contiguous malformed run |
| `[e][f(A,{x})]T` | head Error `3..13`; native nested delimiters in one Error |
| `[e] @ T` / `[e] @ ` | head Error `4..5`; retry/EOF trivia outside Error |
| `[e][bad\nT` | head Error `3..7`; entire newline/`T` Item pending |
| `[e][bad with tail`, active WITH | head Error `3..7`; space/`with` Item pending |
| `[e` | B close Missing at `2`, head Missing at `2` |
| `F([e)` | B close Missing at `4`, head Missing at `4`; native Call `)` |
| `[T(@ ]` / `[T(A,@ ]` | retain Call Error/close records, then newly typed head Missing at `6` / `8` |
| `> > [e] [bad\r\n> > ```\nouter]` | head Error `8..12`; CRLF remains in boundary Item |

Additional controls cover nested brackets and opaque comments, malformed then
balanced then retry, caller words/separators at different depths, foreign
prefixes with deeper continuation, unmatched block-comment leading retained
in a fence Item, LF/CRLF, shifted coordinates, seeded output and fresh/frozen
record identity. Structured PV carriers retain outer-before-inner reservation
order. The four old normalized balanced-head controls are updated for this
chosen rule, including renaming transactional/raw-ownership claims; boundary
coordinate, source conservation and native-prefix assertions are retained.
Existing Call/close routing tests gain only the newly published enclosing
head record; their Call byte ownership and earlier record fields stay fixed.

## T7a/T7b register correction, not certification

The old adoption matrix's quoted `'[@]` and `'[]` are EffectRow types, not
leading bare BracketRows. They cannot witness LeadingEffectTypeHead. Replace
only those two literals and their locators as follows:

| cell | selected embedded witness | primary fact |
| --- | --- | --- |
| T7a | `R({type T = [e] @})` | Type(LeadingEffectTypeHead), span("@"), Error, TypeExpression |
| T7b | `R({type T = [e]})` | Type(LeadingEffectTypeHead), before("}"), Missing, TypeExpression |

The direct Type controls `[e] @` and `[e]` above establish the selected owner
construction only. Actual embedded execution and aggregate fact/header-full
consistency are still required; neither T7 row is certified by this local
gate. T7c retains the separate corrected BracketRowArrow witness from the T4
register correction and 2026-09-08 bracket-arrow successor.

## Verification and cost

M2, primary-only implementation and pre-write contract audit, not independent
review. One scoped implementation/repair pass, focused head and normalized
Type controls, complete Type filter, TypeDeclaration/output/recovery-output
siblings, package check and scoped format/diff checks. Zero benchmark
samples/processes. The removed ordinary speculative scan and separate fenced
raw scanner are replaced by forward lexical Item acquisition. Cost is
O(bytes + structural work), with a stack allocated only for malformed nested
delimiters and O(nesting depth) live space; no cache, replay or CST splitting.
Existing total Error-run output is sufficient; no chasa-recover API is added.

## Construction result

Completed 2026-09-08. All head Missing/Error sites now publish typed records.
One total nested-Item run replaces the two raw head paths and the dedicated
ordinary/fenced balanced-suffix lexer (approximately 240 removed lines).
All accepted-head attachment and terminality controls remain green.

Seven focused head tests pass, including seeded/frozen/shifted output,
caller/fence Items and nested structured reservations. The complete Type
filter passes 159 tests; normalized Type plus ordinary unmatched-head controls
pass 27 tests. TypeDeclaration 39, output 4 and recovery output 25 pass.
Package check, scoped rustfmt and diff checks pass. Initial new-test helper
signature/import mistakes were corrected; the complete Type pass then
identified two older routing controls needing the newly typed parent head
record. Their existing Call extents and close fields were retained.

The T7a/T7b register spellings are corrected above, not certified. M2,
primary-only, no independent review; zero benchmark samples/processes.
Record/forall construction, caller-owned mandatory Type slots and aggregate
embedded/header/public adoption remain open.
