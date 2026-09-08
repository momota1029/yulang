# VirtualStatementBlock current-Item typed recovery

Status: Authoritative; private O3b construction pending

Date: 2026-09-08

Approved-by: user through the recovery-selection and simplification delegation
in `2026-09-08-successor-recovery-authority-amendment.md`

Scope: the three raw recovery publication sites owned by
`virtual_statement_block.rs`: required Statement after leading/repeated
separators, missing separator between admitted statements, and maximal malformed
Statement runs. The StringLiteral interpolation parent, Yumark production
convergence, accepted grammar, AST products and public dispatch are excluded.

Authority: the typed-output amendment §§3--6, the literal-cone Virtual
topology, StringLiteral current-Item recovery, and recovery-authority
amendment §§1--3. Virtual is a distinct root-style `Statement*` sequence, not
Root or a braced block. The existing role vocabulary is sufficient; this record
selects its bounded use rather than adding a role.

## Selected slots and records

The finite mapping is:

| Virtual site | role | expectation |
| --- | --- | --- |
| initial/after-separator comma or semicolon requiring a Statement | `Statement(Starter)` | `Statement` |
| admitted Statement followed by another admitted Statement without a separator | `Statement(Separator)` | `StatementSeparator` |
| maximal malformed Statement run, including post-Statement retry | `Statement(Starter)` | `Statement` |

This reuses `Starter` for Virtual's required root-style Statement position and
`Separator` for its required inter-Statement separator only. It does not claim
that Virtual is Root, broaden either role outside this owner, or reuse Root's
keyword policy. Every Missing has the mapped role, a zero-width site and
expectation at the current remaining-start, no unexpected facts, one
`COMMITTED_RECOVERY_RULE` expectation, and primary index zero. Every Error has
`Statement(Starter)`, one `Statement` expectation, and one `OtherCharacter`
token fact over its actual nonempty emitted run.

## Boundary, extent and continuation

Preserve current Virtual behavior. At initial/after-separator positions,
comma/semicolon publishes one Starter Missing without consuming that Item; the
existing separator phase then emits it. A separate admitted Statement after an
admitted Statement publishes one Separator Missing and retries that exact Item
in the after-separator phase.

The malformed-run owner emits its initial remaining leading directly inside its
one Error, as it does today. Internal run leading belongs to Error; retry and
terminal-boundary leading remains pending. Leading already emitted by an
explicit separator is never reconstructed. Scan one maximal nonempty lexical
run, stopping before an admitted Statement, comma, semicolon, ordinary newline,
EOF, borrowed `}`, or abstract fence. The Error scanner is sealed lexical-only:
no grammar parser, nested builder, source replay or retained run vector.

After Error, retry an admitted Statement outside Error in the existing phase,
or return the terminal Item unchanged with no same-cause Missing. EOF, ordinary
newline, borrowed `}`, and fence terminate as before. Virtual has no close
site: interpolation owns the borrowed `}` and its Missing close. Its leading
stays outside the Virtual body. Virtual records precede interpolation-close,
then StringTerminator, then any enclosing Yumark recovery. Nested admitted
Statement/declaration recovery selects its own role.

The operation remains one-forward `O(bytes + structural work)`, with no
recovery allocation on accepted paths and no new scan/allocation/capability.

## Required evidence

Add direct fresh, shifted, frozen and seeded exact-record controls for all
three sites; leading/repeated/trailing comma and semicolon; malformed one- and
multi-Item runs that retry expressions, declarations and literals; and accepted
empty/mixed root-style sequences. Prove complete untouched Items and leading at
newline, CRLF, borrowed `}`, EOF and active-prefix fence boundaries, UTF-8 and
foreign-prefix Error extents, and effect-free optional Statement/string-opener
rejection.

Retain all source literals. In `"%{,`, add the Virtual Starter Missing before
the existing interpolation-close and StringTerminator records: at source offset
3, then parent records at offset 4. Preserve its existing three-node CST
topology and parent anchors. Exercise Expression, Pattern and Rule string
callers; no production Yumark test is evidence for this private owner gate.

M2: one implementation pass, one compiler/recovery and one regression review,
at most one repair bundle. Run focused Virtual/String/Pattern/Rule/output
tests, package check, format and diff. No workspace rerun or benchmark unless
material cost uncertainty is discovered. Synchronize task, ledger and daily
record before commit. Yumark convergence remains blocked on the reachable
typed-owner closure and its separately unresolved AST-product decision.
