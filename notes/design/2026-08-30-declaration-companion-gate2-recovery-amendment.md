# Declaration companion Gate 2 canonical recovery amendment

Status: Authoritative

Scope: the single canonical Statement malformed-run scanner shared by ordinary and declaration-
companion sequences during declaration companion Gate 2.

Approved-by: user

Approved-at: 2026-08-30

Drafted-by: primary agent from the `architect` adjudication

Reviewed-by: independent `compiler_referee` and `architect`; performance and regression closure
remain mandatory implementation gates

Implementation-order clarification: `architect` adjudication on 2026-08-30 corrected the
candidate-before-comment false premise described in §2. This clarification implements the user's
approved comment-atomic scanner decision; it does not expand the amendment scope.

Supersedes: only the comment-input byte/range-identical recovery requirement in
`2026-08-30-declaration-companion-with-addendum.md` §§9, 13 Gate 2, and 14. Every other grammar,
recovery, performance, and rollback decision remains authoritative.

## 1. Contradiction and decision

Gate 2 exposed a false premise in the original rollback contract. The existing ordinary
`statement_sequence_error_retry` scans raw characters. It can stop on a delimiter inside a block
comment or retry an identifier inside a line comment. A companion-only corrected scanner would
duplicate canonical recovery authority, while sharing the corrected scanner changes observable
ordinary malformed-comment recovery and therefore violates the original byte-identical clause.

The user selected option 1: correct the pre-existing ordinary malformed-comment behavior at its
owning canonical Statement recovery responsibility and share that one scanner with the declaration
companion. This is a bounded recovery correction, not permission for broader ordinary grammar or
range changes.

## 2. Canonical scanner contract

Add one sink-free canonical Statement invalid-run scanner in `grammar/expression.rs`. Ordinary
statement-sequence recovery and declaration-companion recovery call the same scanner and retain
their own typed recovery roles and emitters.

The scanner order is fixed:

1. if the current bytes begin `//` or `/*`, consume exactly one `scan_comment` lexical unit, update
   the malformed range end, and continue. A legal `/` prefix or nullfix operator must never claim a
   comment opener;
2. otherwise, after a non-empty malformed prefix, test the shared canonical Statement candidate at
   the current position;
3. test EOF or a top-level newline, `)`, `]`, `}`, comma, or semicolon boundary and leave that
   boundary unconsumed;
4. otherwise consume one Unicode scalar, update line state, and repeat.

`scan_trivia` must not replace `scan_comment` in step 1 because it may consume a line comment's
terminating newline and steal sequence-boundary ownership.

Required examples:

- `@ /* } */ first}` owns one Error range ending immediately before `first`; the `}` inside the
  comment is opaque, `first` is retried, and the actual final `}` remains for its close owner.
- `@ // noise\nfirst` treats the line comment atomically, leaves the newline as the sequence
  separator, and parses `first` as the next item rather than retrying `noise` inside the comment.
- nested and unterminated block comments remain one lexical unit and never expose internal
  identifiers, separators, or close spellings.
- when `/` is registered as a prefix or nullfix operator, comment openers remain atomic while a
  later real `/` candidate and a normal `/` Statement retain ordinary operator behavior.

## 3. Shared decision ownership

Gate 2 retains duplicated companion AST/direct loop shells, but it must not duplicate canonical
decision tables.

- One shared declaration-intro predicate serves both direct and input-only canonical Statement
  candidate queries.
- Companion-only wrappers call the existing separator recognizers, separator representation and
  emitters, indented terminal-boundary judge, matching-brace-close judge, and braced missing-
  separator decision. Declaration code does not construct or own an ordinary
  `StatementSequencePolicy`.
- Gate 2 uses a sink-free neutral absent-item-slot probe for EOF or any fixed close `)`, `]`, or `}`
  after trivia. The probe always rolls back trivia and punctuation. It emits no Item recovery and
  does not classify matching versus mismatched closes; Gate 3 alone owns close consumption and
  `ClosingDelimiter` recovery.
- Normal companion items call `parse_canonical_statement` or `commit_canonical_statement`
  directly. The candidate query is recovery-only: malformed retry and missing-separator
  synchronization may use it after normal canonical acceptance has failed.

The protected canonical parse/commit and ordinary loop bodies remain unchanged. The following
ordinary helper bodies may change only to delegate to the shared sink-free decisions and must be
remeasured:

- `direct_canonical_statement_candidate`;
- `braced_next_statement_leading`;
- `statement_sequence_error_retry`.

No runtime companion mode, ordinary-path owner branch, closure dispatch, allocation, Derives probe,
CST replay, cache, side vector, or complete-Statement speculative parse is authorized.

## 4. Observable compatibility and rollback

Valid ordinary AST/CST behavior and every non-comment ordinary recovery kind, role, range, token,
and retained boundary remain byte-identical. The only authorized ordinary recovery difference is
lexically atomic malformed-comment ownership through the shared scanner.

Rollback or stop if implementation changes:

- any valid ordinary behavior;
- any non-comment ordinary recovery range or source ownership;
- ordinary Statement node/token order;
- canonical candidate priority;
- separator, newline, close, or caller-boundary ownership;
- ordinary wall time or peak RSS outside the approved zero-effect repeated-run protocol.

## 5. Gate 2 verification

Before Gate 2 may close:

- pin exact ordinary before/after fixtures for every non-comment malformed recovery family;
- add ordinary and companion AST/direct fixtures for line, nested block, unterminated block, and
  comment-contained identifier/separator/all-close-spelling cases;
- preserve the historical ordinary AST sequence contract: it does not run malformed-item recovery
  and its existing cardinality/remainder remain unchanged. Ordinary paired fixtures assert that AST
  result separately from the corrected direct-CST recovery range and shape; they do not require
  ordinary AST/direct equality. The new declaration-companion AST/direct adapters do require parity
  because both intentionally use the shared scanner;
- assert full Statement/separator CST node and token order, exact recovery kind/role/range/
  expectation/source order, AST/direct cardinality, remainder, and losslessness;
- add cfg(test)-only full `ParseLocal` value snapshots and seed non-default multi-frame state across
  normal, Missing, Error, retry, rejection, separator, retained-boundary, and nested-Statement exits;
- prove valid companion sequences do not call the recovery candidate helper;
- run focused tests, `cargo test -p yu-syntax`, independent compiler/spec/regression/performance
  review, fixed 1k/10k ordinary measurements, companion-heavy measurements, and malformed-comment
  stress measurements.

Gate 3 remains unauthorized until these conditions and the original Gate 2 conditions all pass.
