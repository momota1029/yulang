# Ambient statement-owner boundary (ASOB)

## Scope

ASOB resolves two statement-context collisions when a nested local sequence or
continuation lacks its close:

- A physical newline that is strictly shallower than the nearest visible
  statement baseline.
- An exact `else` or `elsif` companion of a visible `IfExpression`.

In either case, the ambient statement owner takes the original gap before a
local item, field, or continuation can consume it. ASOB applies to the
completed or recovered continuation points of the construct families listed in
[ASOB participation and precedence](asob-integration-matrix.md).

It does not resolve ordinary same-indent statement candidates, braced
current-depth statement boundaries, case or catch arm boundaries, or other
contextual introducers such as `if`, `where`, `->`, and `=`.

## Ownership and precedence

At a completed or recovered local continuation gap, the order is:

1. An actual matching own close or an existing caller-owned fixed delimiter stop.
2. A locally allowed explicit separator.
3. An ASOB claim.
4. The construct's existing local continuation, layout, or retry rule.

An ASOB claim requires either strict dedent from the nearest visible statement
baseline or a visible `IfExpression` companion. A braced statement body hides
an outer statement baseline and outer If companion while parsing inside those
braces. An inner If companion remains visible within that braced body.

An If expression consumes a companion only when that companion belongs to the
same If expression. A nested If expression must return an outer companion
unchanged.

## Source order in the Rowan CST

ASOB adds no source syntax, token, or Rowan node. When it claims a gap, the
local construct leaves the original trivia and boundary text unconsumed. The
ambient owner then retains those existing source-bearing leaves in source
order.

ASOB also creates no separator for a rejected implicit boundary. It preserves
the recovery shape already assigned to each construct's close and item slots.

## Recovery and handoff

For a bare implicit candidate vetoed by ASOB, the local owner opens no next
item or field slot. It therefore adds no missing item or field. Each accepted
unclosed delimiter still realizes the existing zero-width `Missing` for its
own close slot.

After an explicit separator, or after a local implicit separator has already
been committed, the ordinary local next-slot recovery still applies. An ASOB
claim at the following boundary does not erase that committed local recovery.

The local owner must test ASOB before consuming an implicit-newline gap. It
must not consume the newline and then test ownership again from the following
position.

## Examples

| Source | Result |
| --- | --- |
| `if condition:\n  struct S { x: Int\nelse: 0` | The Struct leaves the dedent and `else` to the If expression, retains one missing `}`, and adds no missing field. |
| `if condition: f(x else: 0` | The call leaves `else: 0` to the If expression, retains one missing `)`, and adds no missing argument. |
| `if condition:\n  { else: 0 }\nelse: 1` | The braced body does not expose the outer companion inside its braces. The outer `else: 1` remains the If companion. |
| `if condition:\n  my [x\nelse: 0` | The ListPattern leaves the companion to the outer If expression, retains one missing `]`, and adds no missing pattern item. |
| `struct S { x: Int,` | The explicit comma keeps local authority. Existing missing-field and missing-close recovery apply. |

## Composition and limits

ASOB is a caller-boundary layer. It does not replace the local newline test in
[layout-aware separator authority](layout-aware-separator-authority.md),
malformed TypeExpression newline ownership in [TMN](tmn-malformed-newline-owner-policy.md),
or construct-specific close rules. Future extension to another caller-boundary
class requires separate authority for its priority over local syntax.

The governing source is the Authoritative *ambient statement-owner boundary
and layout-delimited implicit-newline collision authority* in
`notes/design/2026-08-20-yu-syntax-chasa-architecture.md`,
lines 18358–19160.
