# yu-syntax Gate 4–6 dependency-SCC and operator-evidence amendment

Status: Authoritative

Scope: This amendment resolves only the execution ordering and acceptance
evidence needed to implement the Authoritative recursive-descent rewrite plan's
Gates 4–6. It preserves the plan's parser-language, AST, CST, diagnostic,
recovery, streaming, and no-production-cutover contracts. It introduces no
production dispatch, legacy/new crossing, Yumark production bridge, replay,
token vector, or public syntax change. It makes the single scoped
dynamic-operator resource-accounting exception stated in §4.3.

Approved-by: user

Approved-at: 2026-09-03

Drafted-by: primary agent

Reviewed-by: independent compiler/referee, specification, regression, and
scoped compiler/specification/performance delta review

Decision recorded while drafting: on 2026-09-03 the user selected a greedy,
capability-filtered trie for the operator branch of successor value-start
evidence. That decision eliminates successor-run partitioning and the proposed
root-local raw-run memo from this amendment. The user then explicitly rejected
retained scanner state for the ordinary scanner's overlap fallback and selected
the Yulang2-compatible, source-only scanner with the parametric accounting in
§4.3: a pathological overlapping operator definition may be slow and is a
definition-quality concern, not a reason to introduce retained parser state.

Narrowly amends on approval:

- `2026-09-02-yu-syntax-recursive-descent-rewrite-plan.md` only in the
  construction ordering of Gates 4–6 and, for dynamic operator scanning only,
  §2(7)'s static resource target and §7's corresponding non-linear-rescan stop
  condition; their ledger ownership and other certification requirements remain
  unchanged;
- `2026-08-20-yu-syntax-chasa-architecture.md` only its performance-constraint
  sentence requiring operator lookup to avoid re-walking an operator run, and
  only for the pre-Item all-spelling candidate fallback and filtered value-start
  traversal accounted in §4.3. Its immutable-table, no-token-vector,
  same-run-rollback, sink-free speculation, and all non-operator constraints
  remain unchanged;
- `2026-09-02-yumark-gate3b-recovery-adoption-matrix.md` only to correct the
  incomplete E12 finite register from `E12a–E12i` to `E12a–E12k`; and
- the expression-tail handoff addendum only where its one-current-Item rule
  needs the successor-evidence capability defined below.

## 1. Reason for the amendment

Three facts make the original sequential reading of Gates 4, 5, and 6
impossible to implement without violating an existing hard constraint.

1. An expression reaches canonical Statement through braced primary,
   colon-application, `with`, `if`, `case`, and `catch` bodies. Statement in
   turn reaches declarations, and declarations and Pattern reach Expression.
   Those owners form one mutually recursive SCC. TypeExpression and
   polymorphic variants are instead an acyclic prerequisite: they recurse into
   themselves and feed Pattern/declarations, but do not call Expression in a
   production grammar path.
2. The recovery matrix defines E12a–E12i, while its normative control table and
   the rewrite coverage ledger require E12a–E12k. The two missing cells cannot
   be guessed during implementation.
3. Dynamic operator fixity depends on whether a following value can start. The
   legacy scanner observes trailing trivia and probes that source. The new
   protocol assigns the trivia to the following Item and may not complete,
   retain, or re-scan that Item merely to choose operator fixity. The needed
   operator-start observation is a greedy query of the already-merged
   Prefix-and-Nullfix capability trie, not an operator-run partition. The
   sole permitted re-observation is the source-only token probe defined in
   §4.3; it neither completes nor re-scans an Item.

Calling a legacy Pattern, TypeExpression, Statement, or declaration parser
would be an old/new crossing. A private expression-only copy of any of those
owners would make its later migration diverge. Neither is allowed.

## 2. E12 correction

The current matrix labels its E12 aggregate table historical, although its
ledger requires an exact finite E12a–E12k register. On approval this section
is the normative E12 register. Every row has the §5b schema: ID, embedded
literal, exact locator, role/kind/primary tuple, ordinary control, and rollback
layer. `R(p)` has the matrix's existing `+5` payload-range shift.

| cell | embedded literal and exact locator | recovery tuple | ordinary control | rollback |
| --- | --- | --- | --- | --- |
| E12a | `R(case : 1 -> a)`, `before(":")` | `CaseLike(Scrutinee)`, Missing, Expression | `expression::tests::{case_like_recovery_marks_missing_mandatory_slots_once, gate3b_ordinary_primary_control_expression_projection_and_case}["case : 1 -> a"]` | RB-E |
| E12b | `R(case x)`, `before(")")` | `CaseLike(Block)`, Missing, punctuation `:` | `expression::tests::{case_like_recovery_marks_missing_mandatory_slots_once, gate3b_ordinary_primary_control_expression_projection_and_case}["case x"]` | RB-E |
| E12c | `R(case x: -> a)`, `before("->")` | `CaseLike(Pattern)`, Missing, Pattern | `expression::tests::{case_like_recovery_marks_missing_mandatory_slots_once, gate3b_ordinary_primary_control_expression_projection_and_case}["case x: -> a"]` | RB-E, RB-P |
| E12d | `R(catch action: err, -> recover)`, `before("->")` | `CaseLike(Handler)`, Missing, Pattern | `expression::tests::{case_like_recovery_marks_missing_mandatory_slots_once, gate3b_ordinary_primary_control_expression_projection_and_case}["catch action: err, -> recover"]` | RB-E, RB-P |
| E12e | `R(case x: n if -> yes)`, `before("->")` | `CaseLike(Guard)`, Missing, Expression | `expression::tests::{case_like_recovery_marks_missing_mandatory_slots_once, gate3b_ordinary_primary_control_expression_projection_and_case}["case x: n if -> yes"]` | RB-E |
| E12f | `R(case x: n yes)`, `before("yes")` | `CaseLike(Arrow)`, Missing, Expression | `expression::tests::{case_like_missing_arrow_retries_the_body_from_the_same_position, gate3b_ordinary_primary_control_expression_projection_and_case}["case x: n yes"]` | RB-E |
| E12g | `R(case x: n ->)`, `before(")")` | `CaseLike(Body)`, Missing, Expression | `expression::tests::{case_like_recovery_marks_missing_mandatory_slots_once, gate3b_ordinary_primary_control_expression_projection_and_case}["case x: n ->"]` | RB-E |
| E12h | `R(catch action { err -> recover`), `eof` | `CaseLike(Block)`, Missing, punctuation `}` | `expression::tests::{case_like_recovery_marks_missing_mandatory_slots_once, gate3b_ordinary_primary_control_expression_projection_and_case}["catch action { err -> recover"]` | RB-E |
| E12i | `R(case x: 1 -> a 2 -> b)`, `before(second arm "2")` | `CaseLike(Separator)`, Missing, punctuation `,` | `expression::tests::{case_like_missing_arm_comma_retries_the_next_pattern, gate3b_ordinary_primary_control_expression_projection_and_case}["case x: 1 -> a 2 -> b"]` | RB-E, RB-P |
| E12j | `R(case x: n @, _ -> b)`, `.1 before("@")`, `.2 span("@")` | `.1` `CaseLike(Arrow)`, Missing, Expression; `.2` `CaseLike(Arrow)`, Error, Expression | `expression::tests::{case_like_invalid_arrow_run_recovers_to_the_next_comma_arm, gate3b_ordinary_primary_control_expression_projection_and_case}["case x: n @, _ -> b"]` | RB-E, RB-P |
| E12k | direct-only: `my value = case x:\\nnext`, `before("\\n")` | `CaseLike(Arm)`, Missing, Pattern at `18..18` | `expression::tests::{case_like_same_indent_boundaries_stay_with_the_outer_owner, gate3b_ordinary_primary_control_expression_projection_and_case}["my value = case x:\\nnext"]` | RB-E; following RB-S remains Gate 6 |

E12j's embedded ranges are therefore `15..15` and `15..16`; its Error has
`UnexpectedCategory::OperatorLike`. Its ordinary ranges remain `10..10` and
`10..11`. The comma stays available and the next arm is parsed. Before its
adoption, the named ordinary controls gain only assertions of their existing
primary expectation and unexpected-evidence fields; literals, records, output,
and recovery behavior do not change.

E12k has no valid `R` or `A` embedding: those owners accept an expression
argument followed by their own close and cannot expose a same-indented
following canonical Statement. This is an exact embedded-harness-unreachable
proof, not an omitted E12 cell. Its direct production edge is
`parse_direct_root_candidate` → binding RHS Expression → CaseBlock → outer
canonical Statement. The direct control asserts the complete ordered pair:
the E12k CaseLike record above, followed by `Statement(Starter)`, Error,
`19..23`, primary keyword `use`. The second record, its full unexpected and
expectation data, and the newline's outer ownership are an RB-S continuation
witness; Gate 6 alone certifies that rollback layer.

The matrix's E12 owner row and every coverage-ledger reference are read as
`E12a–E12k` after approval. This correction adds no recovery vocabulary, parser
behavior, or expected-output change.

## 3. Gate 4–6 SCC construction

Gates 4–6 retain their existing ownership and completion assignments:

- Gate 4 certifies E1–E14 and RB-E;
- Gate 5 certifies P, T, PV, RB-P, RB-T, and RB-PV; and
- Gate 6 certifies S, D, V, NV, RB-S, RB-D, RB-DRV, and RB-CMP.

They no longer imply that every callee first becomes a separately complete
owner. TypeExpression/PV is built as an acyclic prerequisite. The remaining
Expression, Pattern, canonical Statement, declaration, and body owners are
then constructed together inside one isolated SCC. A procedure may be
introduced only as a callee until its own ledger checkpoint is certified. No
intermediate construction slice claims that its owner, or an earlier numbered
gate, is complete.

The construction and certification checkpoints are:

1. **G4a — dynamic item and operator kernel.** Replace the pilot's fixed
   atom/operator subset with source-backed word, literal, and operator
   recognition; prefix, nullfix, infix, suffix, ML handoff; and base
   MissingOperand/Error recovery. The private operational binding threshold
   comes from the immutable OperatorTable and controls handoff only. It never
   constructs an association tree. It applies §4's explicit parametric work
   accounting rather than claiming an aggregate-linear dynamic-operator bound.
   It then closes E8 and operator-related RB-E probes, including a
   binding-power-only table variation that leaves flat, source-order AST/CST
   products unchanged.
2. **G4b — expression-local delimited and fixed owners.** Add one private,
   owner-parameterized Item/Separator/Close loop for parenthesized groups,
   call arguments, index, tuple projection, and record projection. It directly
   emits from the accepted owner; it is neither an action buffer nor a generic
   materializer. This establishes construction/control evidence for E1–E7,
   including Gate 3's E2/E3 controls, complete call sequence ownership, and
   E7a–E7h. Every successful sequence continuation must advance the source
   cursor, consume/replace the pending Item, or advance a finite owner phase.
   Re-entering the same `(cursor, Item identity, owner phase)` is a fail-fast
   contract violation, including Missing, separator, close, and retry paths.
3. **Prerequisite and SCC construction.** Build TypeExpression/PV first, then
   the mutually recursive Pattern, canonical Statement, declaration,
   braced/indented body, colon/with, if, and case/catch procedures under the
   new driver. No procedure calls a legacy parser, and no expression-private
   substitute for a later owner is permitted.
4. **Owner-side checkpoints.** Record E9–E14 and corrected E12a–E12k as
   Expression-side evidence, P/T/PV as Pattern/Type-side evidence, and S/D/V/NV
   as Statement/declaration-side evidence. This is not yet any gate's complete
   acceptance template where a row names another rollback layer.
5. **Joint certification barrier.** Certify every assigned rollback layer
   before declaring a gate complete: E10 requires RB-E and RB-S; E12 requires
   RB-E and RB-P; E13/E14 require RB-S. Gate 5 owns RB-P and Gate 6 owns RB-S;
   Gate 4 may use those paths as construction controls but cannot claim their
   rollback closure. After the three owner checkpoints jointly satisfy every
   row's full template, record Gate 4, Gate 5, and Gate 6 completion according
   to their unchanged ledger assignments.

`as`, type annotation, and assignment continuation are not added merely
because Gate 4 mentions them. Before certification, each must either be
implemented when reachable from the current Expression owner or receive an
exact direct-owner-unreachable proof naming its source recognizer and the
excluded reachability edge. The possibility that `=` remains a declared
dynamic operator requires a direct reachability check before any proof.

## 4. Successor evidence for dynamic operators

The accepting dynamic-operator scanner may use a private
`successor_evidence` procedure. It is neither Item completion nor lookahead
state. Its input is exactly `(OperatorSite, candidate spelling endpoint,
candidate fixity set, leading-trivia presence, root-pointer cursor, layout
baseline, active stop set)`. It first verifies the live root-pointer/cursor and
frame, then returns only the following finite raw evidence:

```text
Trailing = None | Space | Newline { indentation }
AfterTrivia = Eof | ActiveStop | CallOrColonWithoutTrivia | ValueStart(kind) | Other
ValueStart(kind) = QuoteOpenOrBackslash | Sigil | Xid | Decimal | Dot
                 | OperatorWithPrefixAndNullfix
```

### 4.1 Merged value-start trie

`OperatorTable` remains the one immutable parse-session owner. Alongside its
canonical all-spelling trie, it owns a private `value_start_trie`. The latter
contains exactly those final, merged entry indices whose capability set contains
both Prefix and Nullfix. It has no entry, fixity, diagnostic-site, source, or
session-state copy of its own. The builder inserts into it only after all local
and imported declarations for that spelling have merged: Prefix and Nullfix may
have arrived from different accepted declarations, so filtering an unmerged
declaration is incorrect. The two tries freeze together before full parsing;
neither changes during parsing.

For `OperatorWithPrefixAndNullfix`, `successor_evidence` greedily traverses
only `value_start_trie` from the successor cursor. It returns true exactly when
there is a longest boundary-valid qualifying spelling. An identifier-like
qualifying spelling applies the existing `operator_boundary`; if the longest
qualifying spelling fails that boundary, the traversal considers the next
shorter qualifying terminal. This is ordinary longest-match boundary handling,
not a decomposition of the following run. It returns only the finite enum
case, never the spelling, an operator Item, a token, or an ownership claim over
the successor bytes.

Filtering is extensionally equal to the existing full-trie query followed by
the exact `contains(Prefix | Nullfix)` predicate: ineligible entries disappear,
but every qualifying entry and every path required to reach it remains. The
operator branch is non-recursive. A Prefix-and-Nullfix spelling is itself a
valid value-start witness; this evidence does not predict, scan, or complete a
right-hand operand. Thus the query needs no global/root-local memo, no retained
raw run, and no partition result.

`Trailing` is observationally equivalent to the existing maximal ordinary
trivia scan: spaces, LF/CRLF, line comments, nested block comments, and an
unterminated block-comment remainder are all classified from raw source with
the same resulting newline/indentation facts. `ActiveStop` covers only the
current frame's comma, semicolon, and matching close stop. Newline
`ValueStart` is true only when the explicit baseline is strictly less than its
indentation. `QuoteOpenOrBackslash` is exactly `"`, `(`, `[`, `{`, `$`, or
`\\`. `OperatorWithPrefixAndNullfix` requires the exact existing OperatorKindSet
predicate containing both Prefix and Nullfix, not either one.

The procedure borrows raw bytes only while it observes them. It allocates no
Item, advances no live cursor, mutates neither R nor S, records no
identity/diagnostic/recovery, and retains neither a source slice nor a
lookahead cache. The following leading trivia and payload remain wholly owned
by the next Item scanner, which alone assigns Item identity, extent, logical
position, and trivia span. A completed Item is never passed to, reconstructed
by, or re-scanned through this procedure.

The judge applies the existing finite `judge_nud`/`judge_led` table extensionally:
`post_whitespace` is true exactly for nonempty Trailing, Eof, or ActiveStop;
CallOrColonWithoutTrivia rejects only the §4.2 call-or-path-sensitive
candidate; and `ValueStart` supplies the existing value-start boolean. Thus for
identical site, spelling boundary, fixities, leading trivia, and frame, the new
evidence selects the same accepted/rejected fixity as the existing scanner,
without calling that scanner as a bridge.

### 4.2 The ordinary scanner remains site-aware

The all-spelling trie still owns actual operator acceptance. It tries longer
candidate spellings first; for each one it applies the existing boundary,
trivia/layout, no-trivia call-or-colon exclusion, successor-evidence, and
`judge_nud`/`judge_led` checks. Rejection restores the source cursor and every
recoverable scanner/layout/expectation fact to the shorter candidate endpoint;
only an accepted candidate becomes the current Item payload. The all-spelling
trie must not be replaced by unconditional raw-longest matching.

The frozen table with infix-only `+!`, prefix `+`, and prefix-plus-nullfix `!`
is the required witness: NUD `+!a` accepts short `+` and then NUD `!`, whereas
LED `a+!b` accepts long infix `+!`. A site-filtered NUD or LED trie may be an
implementation-local pruning index, but it cannot replace this fallback:
candidate acceptance can still depend on successor evidence and whitespace.

The call-or-colon exclusion is exactly the current
`is_call_or_path_sensitive` predicate, not a general prefix/nullfix rule: the
candidate capability set contains both Prefix and Nullfix and contains neither
Infix nor Suffix; its trailing evidence is None; and the immediately following
raw character is `(` or `:`. Only that conjunction rejects the candidate before
the judge. A spelling with Infix or Suffix capability remains eligible under
the normal judge path.

Focused controls cover each ValueStart family; line/nested/unterminated-comment
trivia; CRLF and baseline-allowed/refused newline; EOF and each active stop;
no-trivia `(` and `:`; a successor operator that has both Prefix and Nullfix;
merged Prefix/Nullfix capability supplied by distinct declarations; a shorter
qualifying spelling under a longer ineligible spelling; and identifier-like
boundary fallback, including a multibyte spelling. They pin the selected
fixity, current Item non-creation, pointer/frame equality, and unchanged R/S.

### 4.3 Selected parametric resource accounting

The user explicitly selects the Yulang2-compatible source-only scanner and
rejects `OperatorRunEvidence`, every other retained raw-run summary, a spelling
or overlap cap, and a new retained/stateful cross-Item matcher or failure
automaton. Arbitrarily overlapping operator definitions remain legal. Their
pathological worst case is accepted as a definition-quality/readability cost,
not a parser-state design trigger.

The parent plan's dynamic-operator-only resource contract is therefore:

```text
O(bytes + structural work
  + (T_all + T_value) * log(max(2, D))
  + C + H)
```

Here `T_all` is the total all-spelling-trie child-map `step` attempts by
ordinary NUD/LED candidate traversal and recovery retry-head probes, including
the final unsuccessful step of each traversal; `T_value` is the corresponding
total for `value_start_trie`; and `D` is the maximum child-map degree of either
trie. `C` is the number of terminal candidate callbacks in ordinary NUD/LED
acceptance traversal, and `H` is the total decoded raw-trivia characters
observed by those acceptance callbacks. `H` includes the transient `TriviaRun`
parts and allocation churn: that work is `O(H + C)` and creates no retained
state. A retry-head terminal callback performs no trivia analysis and only
constant work already dominated by its `T_all` traversal. The BTreeMap
transition representation supplies the `log(max(2, D))` term. Boundary, stop,
and judge work are constant per acceptance callback. The unchanged
`bytes + structural work` terms include accepted Item work, BindingPower
clones, committed trivia, output, and all non-operator owners.

Let `K_all` and `K_value` be the maximum matching spelling depths reached by
the two recursive trie traversals during one scanner call. Their additional
peak auxiliary stack is `O(K_all + K_value)`; it is deliberately parametric
under this decision and has no retained cross-Item component. The cold
`value_start_trie` build runs after final spelling-level merge, costs
`O(L_value * log(max(2, D)))` for `L_value` qualifying spelling characters, and
adds `O(N_value + E_value)` persistent nodes/edges plus terminal entry indices.
It reuses existing entry, fixity, and diagnostic-site storage. This cold table
cost is charged to the existing header/table construction phase, not to full
parse scanner work.

On approval this replaces only the final target-bound sentence of rewrite-plan
§2(7) for dynamic operator scanning. It also narrows only the final rewrite-plan
§7 stop bullet: non-linear rescanning remains a stop condition except for the
source-only all-spelling candidate fallback and filtered value-start traversal
accounted above. Whole-file tokenization, retained checkpoints, all other
non-linear rescanning, and every other stop condition remain forbidden.

The sole permitted re-observation is a source-only **token probe**. It observes
only a candidate token spelling or prospective following leading-trivia/
boundary bytes before an Item exists, produces no Item identity or extent, and
does not assign trivia, logical position, CST, diagnostic, or recovery
ownership. A token probe may be repeated by pre-Item candidate/successor
judgment, so a raw byte may contribute to `T_all`, `T_value`, or `H` more than
once. This includes raw trailing trivia after an eventually accepted operator:
the probe assigns it nothing, and the next Item scanner later owns and consumes
it. No other reread is allowed: a grammar owner, completed logical Item,
assigned leading trivia, CST token, diagnostic, or recovery record remains
non-retainable and non-rescannable.

There is no global token storage, replay, shadow parse, table mutation,
retained source slice, or source-specific raw-run summary/cache after one
`scan_operator` invocation returns or across Item boundaries. Within one
longer-to-shorter candidate traversal, the trie recursion state, callback
stack, live cursor, R checkpoint, and rollback-owned layout/expectation state
remain required. Every rejected callback restores input, R, frame, expectation
sink, diagnostic allocator, persistent recovery state, and IsCut to its
candidate checkpoint, leaves S and committed output unchanged, and then permits
the shorter candidate. The filtered value-start trie removes recursive
*ordinary-scanner* invocation, but the outer candidate fallback remains
source-only.

Yulang2 is the required reference for trie traversal and longer-to-shorter
candidate-fallback topology. The current approved Yulang3 capability judge,
including its exact call-or-colon predicate in §4.2, is the semantic
compatibility oracle; Yulang2 spelling-specific loop-control branches are not
silently imported. The frozen Yulang3 `+!a` NUD / `a+!b` LED controls and the
current scanner-control suite pin that distinction.

A benchmark cannot decide this declared trade-off and is not a G4a
precondition. G4a statically accounts for the named terms in any focused
dynamic-operator test added by its gate; it adds no runtime counter or retained
scanner state and does not claim a stronger aggregate bound. A later request to
add a retained/stateful cross-Item matcher or failure automaton, restrict
operator definitions, or restore the unqualified linear target is a new
architecture decision.

## 5. Acceptance, rollback, and stop conditions

The following is non-exhaustive. Every ledger row retains every requirement in
the rewrite plan §5 and matrix §§1/5b: its ordinary frozen control and exact
embedded/direct witness; AST/direct product and CST hierarchy; lossless
bytes/consumed range/remainder; ParseLocal snapshot or full mapped dependency
cone; recovery role/kind/range/unexpected/expectation union/primary/diagnostic
identity/continuation/source order; Item identity/trivia/extent/logical
position; frame-pop/following-owner cleanup; and no replay or Item re-scan.

For RB-E, every rejected OperatorChain, NUD, Item, or slot probe restores the
input/remainder, recoverable state, expectation sink, diagnostic allocator,
persistent recovery state, explicit frames, pending Item, and IsCut. It leaves
the committed sink/output checkpoint and published fact stream unchanged.
Accepted owners publish Rowan and recovery directly and continue totally.

Return to design immediately if a procedure needs a legacy callee, a rejected
path would undo committed output, E12j/k needs a different tuple than the
ordinary control above, successor evidence completes another Item, an accepted
loop repeats the same `(cursor, Item identity, owner phase)`, or a proposed
expression-only Statement subset omits reachable declaration behavior.

## 6. Review and verification record

This was an M3 architecture amendment. Before Authority status:

- independent compiler/referee review checks SCC ownership, handoff, rollback,
  E12 tuples, and successor-evidence safety;
- independent specification review checks the amendment against the rewrite
  plan, tail handoff addendum, recovery matrix, and frozen controls; and
- independent regression review checks all direct call sites, legacy test
  identities, public-dispatch isolation, and the Gate 4–6 boundary.

One initial review round and at most two scoped repair/review rounds are
budgeted. The initial review and scoped architecture/performance investigation
established that a filtered value-start trie removes successor partitioning but
not ordinary candidate-fallback reinspection. The user selected §4.3's
parametric resource accounting instead of retained scanner state or a language
restriction. Compiler, specification, and performance delta reviews then
checked that exact exception; their direct authority, value-start vocabulary,
rollback-lifetime, and accounting repairs are incorporated above. The M3 review
budget is consumed. The user approved this scope and its token-probe-only
reread rule on 2026-09-03, making this document Authoritative. This status
transition changes documentation only, so no compiler test suite is run before
the later implementation gate.
