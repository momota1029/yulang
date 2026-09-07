# Successor PV scalar-frontier evidence plan

Status: Reviewed; evidence-only preflight, no construction authority

Date: 2026-09-07

Drafted-by: primary after the ambient-carrier completion and the blocked
shared-delimiter implementation review

Reviewed-by: independent compiler/recovery and specification review; one
bounded Draft repair followed by clean compiler/recovery delta review

Scope: execution-pin the remaining direct legacy facts required before a
replacement private, ordinary-context pre-Item scalar-frontier capability
design can be reviewed.  This plan authorizes no rewrite-source change, no
payload-admission behavior, no `AmbientClaimView::claims` caller, no virtual or
Yumark policy, no primary-completion retry, and no change to the blocked shared
delimiter candidate.

Depends-on:

- `2026-09-07-successor-pv-payload-admission-capability-amendment.md` §§1--5;
- `2026-09-07-successor-pv-wrong-kind-primary-completion-amendment.md` §6;
- `2026-09-07-successor-ambient-claim-context-prerequisite-amendment.md`
  §§3--6, completed at `b85c32f3`; and
- direct legacy evidence in `crates/yu-syntax/src/grammar/type_expr.rs`.

## 1. Confirmed boundary and reason for this plan

The completed ordinary-only carrier resolves only call-stack provenance.  It
deliberately leaves `claims` unused and gives virtual interpolation/Yumark an
unavailable `None` value.  It does not make an Item already built by the
rewrite lexer splittable.

The reverted wrong-kind primary route exposed the remaining causal boundary.
For `:{123::{B}}`, legacy emits the malformed payload boundary up to, but
excluding, the colon which starts the nested PV and retries that nested PV
there.  The current
rewrite instead constructs `::` as a `PathSeparator` Item before its payload
judge runs.  A suffix observation therefore starts after the required split
and cannot recover it without forbidden replay, retained source/run state, or
an Item reconstruction.

The shared PV payload judge owns conditional admission for valid and wrong-kind
heads.  Any eventual observation must happen before Item construction at the
scalar frontier, while `current_item` retains lexical construction and
transaction ownership and accepted grammar owners retain output-emission
ownership.  This plan records evidence only; it does not choose an observation
algorithm or claim that the existing candidate-token permission is broad enough
for one.

## 2. Evidence already execution-pinned

The following direct controls are retained rather than rewritten:

| family | current direct control | confirmed fact |
| --- | --- | --- |
| conditional payload admission | `legacy_polymorphic_variant_conditional_payload_admission_is_execution_pinned` | valid/wrong-head `::` and `->` retry, dangling `::`, visible no-stop `else` decline, spaced valid-name boundary, repeated payload, newline, native close, and EOF |
| colon overlap | `legacy_polymorphic_variant_payload_colon_overlap_is_execution_pinned` | valid/wrong-head `::{B}` and `:::{B}` split at the retry colon |
| scalar ownership | `legacy_polymorphic_variant_payload_scalar_run_boundaries_are_execution_pinned` | valid-name `->`, `+`, `@@`, atomic `::/*c*/`, and CRLF boundary ownership |
| primary and reservation boundary | `legacy_polymorphic_variant_primary_completion_preflight` | non-atomic primary external/internal tails, selected `::Next`, numeric apparent Call, prefix, and recursive PV ownership |
| P and E carriers | `legacy_polymorphic_variant_structured_parenthesized_gap_extents_are_execution_pinned` and `legacy_polymorphic_variant_effect_and_call_gap_carriers_are_execution_pinned` | P/E ordinary-gap extent facts, E rows, numeric apparent-Call distinction, prefix/nested cells, and `::Next` continuations |
| ambient continuation | direct polymorphic-variant `it3`/`nt5`, strict-dedent initial and recovery-continuation, nested-If initial/recovery-continuation, and actual-If accepted-own-Else initial-PV controls, plus conditional-payload controls | root visible/no-stop initial same-line/newline `else` and retry `:{A::else: 0}`, strict-dedent initial `:{A\nelse: 0}` and recovery-continuation `:{123\nelse: 0}` under baseline 2, nested outer(0)/inner(5) same-line initial `:{A else: 0}` and recovery-continuation `:{A::else: 0}` selecting inner, plus `if condition:\n  type T = :{A\nelse: value` whose PV missing brace precedes the accepted own Else and retires the internal companion; frames must balance |

These controls do not prove a general retry grammar.  In particular, their
valid-name scalar examples do not characterize equivalent wrong-head, fence,
or virtual rows.

The current direct PV ambient coverage is deliberately narrower than the
ordinary provenance matrix: it installs a root scope with one visible
companion.  Query-level `ParseLocal` indented/dedent and nested-companion tests
are not PV AST/CST/recovery evidence.  The actual-If accepted-own-Else initial
PV cell below is now direct evidence; post-completed-If outer-tail restoration
remains unpinned.

## 3. Required direct evidence matrix

Before a replacement capability Draft may be reviewed, add only direct legacy
observations that fill the following cells.  Each row records source, ordinary
entry/context, initial ambient claim, scalar frontier, retry classification and
claim, AST/CST/recovery facts, emitted-byte owner, actual close/remainder, and
whether the current rewrite has an analogous entry.  A row may be marked
unavailable only with a concrete reason and without inferring a policy from it.

| gap family | minimum unpinned rows |
| --- | --- |
| wrong-head scalar runs | `+`, `@@`, `::/*c*/`, and CRLF after a wrong head; admitted nested-PV retry, decline, native-close, and EOF counterparts where legacy exposes them |
| spacing and no-retry | wrong-head spaced malformed surface; each named multi-token/comment spelling whose no-retry result would be used by a future classifier |
| fence-qualified scalar rows | valid and wrong heads at inline retry/decline and CRLF/fence termination, or an explicit direct unavailability result for each |
| ordinary ambient provenance | root visible/no-stop initial and retry, indented strict-dedent initial/recovery-continuation, nested-If initial/recovery-continuation, and accepted-own-Else after an initial PV prefix are already pinned; add recovery-continuation under own Else and initial/recovery-continuation under outer-tail restoration; retain the no-stop `else` distinction rather than encoding it in stops |
| retry primary vocabulary | adjacent and spaced forms for every primary class proposed for admission, with leading BracketRow explicitly classified rather than silently inherited |
| retained structural siblings | numeric apparent Call, non-atomic external/internal tails, repeated payload, prefix and recursive reservation, and every authorized P/E extent row remain exact fresh/frozen controls |
| unavailable callers | virtual normal/heredoc/nested/fence and Yumark production-cell rows remain unavailable until a separate policy/evidence decision; a future observer must decline under carrier `None` |

The first bounded wrong-head slice is complete in
`legacy_polymorphic_variant_payload_scalar_run_boundaries_are_execution_pinned`:
`:{123+:{B}}`, `:{123@@:{B}}`, and `:{123::/*c*/:{B}}` pin their complete
wrong-kind name recovery, scalar payload-boundary recovery, and inline nested
PV retry; `:{123::\r\n:{B}}` separately pins its three tag-loop recoveries.
All four rows pin AST, full CST preorder/ranges, ordered recoveries, native
close/full consumption, and AST/direct episode-frame balance.  This leaves the
other unpinned wrong-head dispositions and every other matrix family open.

The second bounded slice pins the spaced wrong-head no-retry forms
`:{123 +}` / `:{123 +` and `:{123 @@}` / `:{123 @@`.  In all four, the space
is the complete payload boundary and the scalar run is a payload-owned
TypeExpression recovery; the EOF rows additionally pin the missing outer-brace
record.

The third bounded slice pins the distinct spaced `::/*c*/` path.  With native
`}` the comment is PV-local close trivia after the payload's `::` error; with
EOF it remains the actual prefix remainder after the outer missing brace at
offset 8.  The row pins both AST/direct frame balance, native/full CST and
recovery, plus prefix CST/recovery/remainder.  It establishes no generalized
comment, fence, or successor policy.

The fourth bounded slice pins unspaced wrong-head `+`/`@@` native/EOF forms.
The empty-trivia payload judge declines the run without a payload, then the
outer PV tag loop owns the second malformed tag.  The EOF rows pin the missing
outer-brace record.  This establishes no disposition for other spellings,
ambient contexts, fences, or successor behavior.

The fifth bounded slice pins the initial indented strict-dedent provenance
cell.  Under a root scope plus indented statement baseline 2, with no If
companion or stop frame, `:{A\nelse: 0}` begins with no ambient claim and has
one at byte 3 when the PV prefix stops before the newline.  The row pins the
AST, direct prefix CST and sole outer-brace Missing record, source
reconstruction with the exact `\nelse: 0` remainder, and LIFO scope/frame
balance.  It does not establish an If/Else claim or a successor policy.

The sixth bounded slice pins strict-dedent after a recovered tag continuation.
Under the same root-plus-baseline-2, no-If/no-stop context,
`:{123\nelse: 0` begins with no ambient claim and has one at byte 5 after the
wrong-kind tag-name recovery.  Its AST/direct prefix ends at byte 5, leaves the
exact `\nelse: 0` remainder, and records the tag-name Error before the outer
brace Missing recovery.  This is neither an If/Else claim nor a general retry
or successor-policy rule.

The seventh bounded slice pins nested-If same-line owner identity.  Under a
root scope, visible outer companion baseline 0, visible inner companion
baseline 5, and no active stop frame, `:{A else: 0` begins with no claim and
selects the captured inner companion at byte 3.  The direct/AST prefix ends
before the exact ` else: 0` remainder and has only the PV outer-brace Missing
record.  Repeated probes pin rollback-stable inner identity; this does not
retire an accepted Else frame or restore an outer tail.

The eighth bounded slice pins nested-If identity after scalar recovery.  Under
the same root, outer(0), inner(5), no-stop context, `:{A::else: 0` has no claim
at byte 3 before `::` is consumed, then selects the captured inner companion
at byte 5.  Its prefix has one complete `A` tag, one recovered `::` tag slot,
then the outer-brace Missing record; the exact `else: 0` remainder stays
unconsumed.  It neither retires an Else frame nor restores an outer tail.

The ninth bounded slice pins accepted-own-Else retirement after an initial PV
prefix.  Under a root scope with a preexisting outer companion, no stop frame,
and the actual If entry, `if condition:\n  type T = :{A\nelse: value` consumes
through byte 40.  Its Type RHS PV spans `25..28`, has complete tag `A`, and
records only its Missing outer brace at `28..28`; the actual `ElseArm` is
accepted at `29..40`.  The internal companion intentionally has no test hook:
the observable proof is restoration to depth 1 with the preexisting outer ID.
AST and direct CST/recovery facts are exact, and AST emits the same missing
close as `Recovered::Incomplete` while its sink remains empty by contract.
This establishes neither an own-Else recovery continuation nor an outer tail.

Every new direct assertion follows the existing exact AST, full CST preorder and
token range, ordered recovery/evidence, actual-close, remainder, and
ambient-balance style.  It must not update a rewrite expectation or treat a
current successor result as the direct contract.

## 4. Architectural proof inventory to attach after evidence

The later replacement Draft must name, not assume:

1. every ingress and recurrence of the shared payload loop: valid-name entry
   through `type_polymorphic_variant_tag_payloads_normalized`, wrong-kind entry
   through `type_polymorphic_variant_tag_payloads_after_head_normalized`, and
   every next-Item acquisition/handoff after a completed payload or a malformed
   tag run;
2. the exact pre-`current_item` and sealed Error-run transaction boundaries
   available at each route, and why a declined observation preserves input,
   diagnostic cursor, recovery slots, Item ownership, leading frontier, and
   output unchanged before a reservation is committed;
3. the distinct committed frozen-mismatch contract: existing output is
   invalidated/discarded without rollback or reusable-result claims, while
   recovery ordering, diagnostic cursor, and Item ownership retain their
   existing frozen-reconciliation responsibilities;
4. how `::{B}` and `:::{B}` are classified before `scan_punctuation` creates a
   `PathSeparator`, without moving ownership into PathSegment recovery;
5. which finite bytes the observation can inspect, whether its authority fits
   the SCC candidate-token/prospective-trivia rule, and any separate extension
   needed if it does not;
6. the prohibition on Item/Token/trivia/source/offset/run/cache/recovery/output
   retention, live-cursor advance, replay, allocation, cloning, or post-hoc
   CST splitting; and
7. aggregate work accounting for malformed bytes `M`, witness bytes `W`,
   admission/decline attempts `A`, and retry classifications `C`, including a
   fixed-constant `W <= c * M` proof and unchanged valid-input work.

The future Draft must preserve `None` as capability unavailability.  It cannot
choose a virtual-root policy, use the test-only Yumark cell witness as a
production ingress, or call `claims` before its separate approval.

## 5. Evidence-only execution and review boundary

This Draft has no semantic construction.  Its only prospective code changes
are direct legacy evidence tests after a pre-write specification audit confirms
that each expected fact is observed rather than selected by successor output.
The existing shared delimiter candidate may retain its uncommitted P/E proof
work, but neither its helper nor candidate-dependent expectations may be
staged while the numeric Call/PV admission contradiction remains open.

After the matrix and architectural inventory are complete, a replacement
capability Draft is M3: compiler/recovery, specification, and performance
review must assess the concrete frontier, retention/rollback proof, and hot
path work before a fresh user decision.  No recommendation delegation applies
to that payload-admission or virtual-policy decision.
