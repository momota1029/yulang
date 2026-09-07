# Successor ambient-claim context prerequisite amendment

Status: Authoritative; ordinary-only construction/proof pass complete

Date: 2026-09-07

Drafted-by: primary after the PV payload-admission capability re-entry

Scope: a private, immutable context carrier for the legacy
`any_ambient_owner_claims` decision.  This Draft authorizes no source, CST,
AST, recovery, scalar-observation, or public behavior change.  In particular,
it does not authorize the conditional PV payload-admission construction that
motivated it.

Depends-on:

- `2026-09-07-successor-pv-payload-admission-capability-amendment.md` §§2–4;
- `2026-09-05-direct-literal-cone-addendum.md` LC-9; and
- direct legacy `session::any_ambient_owner_claims` and its scope/If tests.

## 1. Problem and owned responsibility

The rejected PV payload-admission route needs one fact that its Type stop set
cannot represent: whether an ambient statement owner claims the live
trivia-plus-retry-primary position.  In direct grammar that fact is owned by
`session::any_ambient_owner_claims`, not by a delimiter, Type-ML mode, payload
loop, recovery record, or lexer Item.

The direct function checkpoints, derives three position facts, makes a pure
decision, then rolls back:

1. whether the prospective trivia contains a physical newline;
2. the following physical-line indentation; and
3. the following word, if any.

It claims a gap for either a strict dedent below the nearest visible statement
baseline or a visible If-companion frame whose exact word and indentation
match.  Braced owners hide both the outer baseline and outer companions.  This
Draft separates that pure context decision from the later source observation:
the future lexical owner may derive the three facts, while this carrier only
answers from facts already supplied.

No current rewrite `Stops` value may be overloaded to represent this result.
No current `Item` may retain it, and no output/recovery operation may infer it
after an Item has been emitted.

## 2. Candidate data model and exact query

The recommended candidate is a by-value, call-stack-only view:

```rust
struct AmbientClaimView<'frame> {
    statement_baseline: Option<usize>,
    companions: Option<&'frame AmbientIfCompanion<'frame>>,
}

struct AmbientIfCompanion<'frame> {
    parent: Option<&'frame AmbientIfCompanion<'frame>>,
    baseline: usize,
    exact_words: &'static [&'static str],
}

struct AmbientPositionEvidence<'word> {
    has_physical_newline: bool,
    following_line_indent: usize,
    following_word: Option<&'word str>,
}
```

All values are `Copy` except that an `AmbientIfCompanion` is a stack local
borrowed only during its owner's initial/`elsif` arms and continuation
recognition.  Recognizing the owning `else` retires that frame before the Else
body starts; every completed If also restores the caller view before its outer
tail starts.  The view may hold no source slice, token, trivia, Item, output
builder, recovery state, cursor, offset, cache, collection, boxed value, or
mutable reference.
`exact_words` is a static existing spelling set; the proposed If frame uses
`["elsif", "else"]`.

`AmbientClaimView::claims(evidence)` is the following total pure decision:

```text
strict_dedent = evidence.has_physical_newline
             && statement_baseline is Some(b)
             && evidence.following_line_indent < b

companion_claim = first frame from innermost to outermost for which
    evidence.following_word is an exact frame word
    && (!evidence.has_physical_newline
        || evidence.following_line_indent >= frame.baseline)

claims = strict_dedent || companion_claim
```

The walk continues past an indentation-ineligible inner frame, so an eligible
outer frame may still claim the word.  This is the direct
`if_continuation_owner_from_evidence` ordering.  The query does not scan,
advance, checkpoint, allocate, emit, or mutate; its caller owns all source
observation.  An absent word can never satisfy a companion frame.

## 3. Visibility transitions and propagation boundary

The candidate has exactly four ordinary transformations.  They are expressed
as values, not mutable parser-local scope state.

| owner transition | `Some(view)` result / `None` result | direct provenance |
| --- | --- | --- |
| root statement or an indented statement sequence | replace `statement_baseline`; preserve visible companions / preserve `None` | `RootStatement` / `IndentedStatement` scopes |
| inline canonical statement | forward unchanged / preserve `None` | `InlineCanonicalStatement` does not hide an owner |
| braced statement owner | empty baseline and empty companion chain / preserve `None` | `BracedBarrier` hides both |
| active If initial/`elsif` arms and continuation recognition | prepend one stack-local companion / preserve `None` | `IfExpressionCompanionScope` lifetime |
| accepted Else body and completed If outer tail | restore the caller view before entry / preserve `None` | direct `pop_if_expression_companion_scope` before `parse_else_arm` |

Root and indented replacement deliberately preserve a visible outer If chain:
the legacy scope stack replaces the nearest baseline but has no companion
visibility floor until a braced barrier appears.  An ordinary Type delimiter,
named record, effect row, nested PV, Call, Parenthesized group, and suffix
continues the same view; none may reseed or clear it.

The transformations above are `Option::map` operations.  Only an explicitly
ordinary top-level ingress may seed `Some(AmbientClaimView::root_statement(..))`;
once a caller supplies `None`, no nested statement, indented sequence, braced
owner, inline owner, or If may manufacture `Some`.  Thus an unavailable
virtual/Yumark carrier remains unavailable even when its virtual statement
reaches an otherwise ordinary declaration body or braced sequence.

The future construction pass must thread this view through only the existing
private normalized call graph.  Its entry and boundary inventory is fixed
before writing:

1. `statement_normalized`, `statement_from_item_normalized`, and canonical
   statement sequence owners establish or replace the ordinary baseline;
2. `indented_statement_block_normalized` and declaration-owned indented
   sequences replace it with their accepted block indentation;
3. the inline Statement paths in `tails.rs`, `mod_decl.rs`, `impl_decl.rs`,
   `role_decl.rs`, and `act_decl.rs` forward it unchanged;
4. `braced_statement_block_normalized`, braced declaration companions, and
   catch-braced statement sequences pass an empty view to their inner
   statement sequence;
5. `if_nud_normalized` constructs an augmented view only for the initial and
   `elsif` arms and continuation selection.  It passes the caller view to
   `else_arm_normalized` immediately after accepting its own `ElseKw`, and
   passes that same caller view to `continue_normalized_tail` on every exit;
6. `type_expr.rs`'s public-to-rewrite Type entry, required-Type helpers,
   primary/tail helpers, and lexical Item producers forward the caller view;
7. recursive Type owners `type_expr/delimited.rs`, `type_expr/record.rs`,
   `type_expr/forall.rs`, and `type_expr/variants.rs` forward it through every
   Type/PV primary, field, payload, recovery-run, and tail entrance; and
8. non-statement Type entrances in `pattern.rs` (annotations), `derives.rs`,
   `type_decl.rs`, `cast_decl.rs`, `struct_decl.rs`, `declaration_variant.rs`,
   `impl_decl.rs`, `role_decl.rs`, and `act_decl.rs` forward their caller view
   through their required-Type helper before returning to their existing owner.

The carrier must not be added ad hoc to only the PV payload loop, to a stop
helper, or to an `Item`.  The numbered inventory is the complete construction
map; a pre-write `rg` inventory of the named Type APIs must be attached to the
implementation record and may not reveal a new unclassified caller.  Existing
non-boundary Items must remain intact and cannot be retrospectively split or
annotated.

## 4. Virtual statements and Yumark are explicitly unavailable in the first gate

`VirtualStatementBlock` is Authoritative root-style `Statement*`, but direct
legacy interpolation parsing is opaque at its internal Type/PV decisions.
Therefore its visibility transition is not proven by the direct braced-owner
tests.  The current rewrite Yumark cell witness likewise calls an isolated
statement entry at `(0, 0)`; it is not a production embedded-Yulang ingress.

The first carrier gate has one concrete deferred boundary rather than an
implicit empty/root/braced policy.  Its signatures carry
`Option<AmbientClaimView>`: an explicitly ordinary top-level ingress seeds
`Some(view)` and every nested transformation preserves an incoming `None`,
while `virtual_statement_block_normalized`, its
`literal::string_literal_with_virtual_statements_normalized` caller, and the
interpolation callback path pass and preserve `None`.  An If reached under
`None` preserves `None`; it may not manufacture an available companion.  The
current `yumark_cell::yulang_code_cell_witness` also receives `None`, so it
remains an isolated lexical/CST witness rather than an ambient-policy seam.

A later, separately reviewed virtual/Yumark gate may ask the user to select
the following recommended option:

> A virtual statement block seeds `statement_baseline = Some(0)` and an empty
> companion chain.  A nested virtual block seeds again.  A surrounding Yumark
> fence applies no additional reset, and the current cell witness remains only
> a root-seed test seam.  A future production cell bridge is outside this gate.

This option treats virtual statements as their documented root-style owner,
permits an If created *inside* the virtual block to be visible to its own
children, and never inherits an outer ordinary If companion.  Return from the
virtual call restores its caller's view by ordinary stack lifetime.

Until that later gate, `None` is capability unavailability, not a claim result:
a future ambient-sensitive scalar observer must decline its new admission when
the view is absent and must not call `claims`.  This blocks the new behavior
beneath interpolation without treating virtual as braced, inheriting outer
companions, or creating a synthetic test-only policy.  The first gate changes
no payload behavior because it introduces no observer.

Before the later virtual-root selection can become Authoritative, the evidence
package must map the following transitions against direct legacy or record an
explicit user decision that supersedes the unavailable observation:

1. normal and heredoc interpolation below an enclosing baseline/If companion,
   with outer-view restoration after return;
2. an If companion created inside a virtual block;
3. nested and fence-terminated interpolation restoration; and
4. a distinct future production Yulang-cell bridge.

The dependent PV capability amendment remains a Draft until this later mapping
or decision closes.  Its ambient prerequisite must not be marked Reviewed from
the ordinary-only carrier gate.  No current source may classify virtual
statements as braced, let them inherit outer companions, or turn the test
witness into production policy.

## 5. Construction, invariants, and cost

If the user approves the ordinary-only first gate after review, construction
creates the carrier, propagates it to the fixed owner inventory, and preserves
the explicit virtual/Yumark `None` boundary.  It does not call `claims` from a
PV payload judge and does not change output.  It may add focused internal
carrier/lifetime tests; it may not modify legacy grammar, grammar
fixtures/goldens, public dispatch, O6, AST/HIR, or any expected parser output.

The construction must prove all of the following:

1. every `AmbientIfCompanion` borrow ends before its owning If call returns,
   and its view is retired before an accepted own Else body and every outer
   tail; early boundary, recovery, `elsif`, own-Else, and no-Else exits restore
   the correct caller/outer frame chain;
2. braced views cannot reveal a parent baseline or companion, while inline
   paths cannot erase one;
3. root/indented baseline replacement and companion selection reproduce the
   direct query for same-line, equal-indent, strict-dedent, nested-frame,
   inner-ineligible/outer-eligible, own-Else-retirement, and outer-tail
   restoration positions;
4. no mutable state is added to `Recover`, `RewriteIn`, `Item`, output, or a
   global/thread-local side channel; and
5. the carrier has no heap allocation, clone, source retention, cursor probe,
   scan, recovery record, or CST/AST operation.  Passing a `Copy` view is the
   only added work in this gate; `claims` remains unused until a separately
   approved scalar-observation gate; and
6. `None` propagates unchanged through normal/heredoc/nested virtual
   interpolation and the Yumark witness, including `None → indented/braced
   owner → Type/PV` controls.  The tests establish only this unavailable
   capability boundary, not a virtual ambient policy.

The prospective `claims` query is O(active If depth), exactly like direct's
innermost-to-outermost frame search.  It is not an inner-loop operation of the
carrier gate, because no caller invokes it there.  The later scalar gate must
account for every query together with its malformed-run work bound.  This gate
has zero timing-process budget: static lifetime and allocation inspection must
first establish an implementation whose timing could affect a decision.

## 6. Review and decision gates

This is a new private recovery/context decision and uses M3.  Required order:

```text
architectural Draft
→ compiler/recovery and specification review
→ one batched Draft repair if needed
→ user selection of the ordinary-only §5 carrier gate
→ Authoritative ordinary-only context-carrier gate
→ one implementer pass and independent implementation review
```

Performance review is required before construction only if the concrete
signature propagation or query placement introduces a new traversal, allocation,
or aggregate hot-path work not discharged by §5's static proof.  No benchmark
is authorized in this Draft.

### 6.1 M3 review closure

The initial independent compiler/recovery review found two major defects: the
candidate held an If companion past its direct Else-retirement boundary and
omitted reachable non-statement Type entrances.  The initial specification
review additionally found that virtual deferral was not an executable boundary
and that its approval ordering contradicted the parent capability Draft.

The repaired Draft:

1. retires the own If frame before its Else body and outer tail while preserving
   enclosing frames;
2. inventories Type roots, required-Type helpers, recursive Type owners,
   pattern annotations, derives, and declaration Type entrances;
3. defines virtual/Yumark deferral as an explicit unavailable
   `Option<AmbientClaimView>`; and
4. aligns the parent Draft so ordinary-only propagation does not certify a
   virtual/Yumark policy.

Specification delta review was clean.  Compiler/recovery delta review then
found one final `None` propagation hole through ordinary owners nested below a
virtual statement; the `Option::map` rule and the required
`None → indented/braced → Type/PV` controls close it.  A fresh focused
compiler/recovery closure review is clean.  The reviewers inspected no source
implementation because none is authorized yet.  Existing direct ambient tests
for empty state, baseline/barrier visibility, and nested If rollback passed;
there is no timing process and no new performance review trigger in this
document-only phase.

### 6.2 User decision

The new durable decision is limited to the following alternatives:

1. **Authorize the ordinary-only carrier gate (recommended).** Implement the
   immutable carrier and its complete propagation map, seed it only at explicit
   ordinary top-level ingress, preserve `None` through virtual/Yumark paths,
   and add only the internal lifetime/unavailable-boundary controls in §5.  No
   `claims` caller, PV output change, scalar observer, virtual ambient policy,
   production Yumark bridge, or public adoption is authorized.
2. **Defer the carrier.** Leave this Draft unimplemented.  Conditional PV
   payload admission, including the already blocked wrong-kind primary policy,
   remains blocked and no rewrite source changes in this area occur.

Option 1 is recommended because it resolves the independently owned ambient
context prerequisite without preselecting the currently unobservable virtual
semantics.  A later scalar-observation or virtual/Yumark gate still needs its
own Reviewed design and user decision.

User decision: option 1 selected on 2026-09-07.  This authorizes exactly one
private ordinary-only construction/proof pass under §5.  The implementation
must preserve virtual/Yumark `None`, keep `claims` unused, and make no PV
payload/output, scalar-observer, virtual-policy, production-cell, public, or
legacy-grammar change.

### 6.3 Construction/proof completion

The authorized private pass completed at `b85c32f3` on 2026-09-07.  It adds a
by-value `AmbientClaimContext` that is transparent around exactly the logical
`Option<AmbientClaimView>` in non-test builds; its test-only immutable function
pointer is a source-free proof hook and is not parser state.  The fixed §3
inventory now threads the context through Statement, declaration, Type, and
recursive Type/PV owners.  Ordinary ingress creates `Some`, all nested
transitions use the stipulated map behavior, braced owners clear a present
view, and virtual interpolation/Yumark enter with `None`.

Actual-entrance controls prove unavailable virtual Type/PV paths, recursive
ordinary Type/PV forwarding, and own-Else/outer-tail retirement.  They catch a
private sentinel only after observing the received carrier, so dropped hooks or
wrong `Some`/`None`/frame chains cannot pass merely through unchanged output.
`claims` remains unused outside carrier unit tests; no PV output/admission,
scalar observer, recovery/output/Item state, source retention, allocation, or
public behavior was added.

The first implementation review found that output-only controls could not prove
actual propagation.  One bounded proof-control repair followed, and fresh M3
compiler/recovery, specification, and regression delta reviews were clean.
The staged carrier-only tree passed format, non-test package check, and all 12
carrier controls.  Its full `yu-syntax` library run had 1300 pass, 9 fail, and
2 ignored; the unmodified `HEAD` comparison had the same 9 failures (1288
pass, 9 fail, 2 ignored), so the pass adds no failure.  The failures are the
existing nested-delimiter residual, not this carrier.  The unrelated dirty
horizontal-delimiter candidate and `tests/type_expr.rs` remain excluded.

The later pre-Item scalar observer remains separately blocked by the PV
payload-admission capability amendment: it needs a finite raw scalar grammar,
direct evidence for each named retry class, exact Error-span ownership,
fresh/frozen proof, and aggregate `W <= c * M` work accounting.  Approval of
this ordinary-only carrier would not approve that observer, virtual/Yumark
participation, or the withdrawn suffix route.
