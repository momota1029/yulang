# Authoritative: Yumark Gate 3 embedded-Yulang bridge and committed state allocation

Status: Authoritative

Approved-by: user

Approved-at: 2026-09-01

Scope: only the Gate 3 / Gate 4 allocation of the shared embedded-Yulang
delimiter bridge and its first clients, plus the Gate-3-owned committed Yumark
source/`LineState` advancement needed by that isolated structural grammar.

User decision: select the Gate 3 bridge allocation. Gate 3 completes the
already selected argument-bearing inline reference/apply syntax through the
single neutral bridge; Gate 4 reuses it for command and special-form payloads.

Supersedes: only the Gate 3 and Gate 4 allocation sentences in §11 of
`notes/design/2026-09-01-doc-comment-yumark-addendum.md`.

Supplements: §4 of that document only to allocate committed Yumark
source/`LineState` advancement. Its probe-checkpoint, frame, recovery, and
single-pass requirements remain unchanged.

## 1. Allocation contradiction

Section 5.4 makes these complete selected inline forms:

```text
\ident
\ident;
\ident(args)
[doc]:ident
[doc]:ident(args)
```

Their argument-bearing forms require the shared embedded-Yulang delimiter
bridge: canonical call-argument parsing under the inherited operator table,
Yumark ownership of the outer `(` / `)`, a delimiter floor, parent-boundary
return, and one outer Missing-close recovery without a duplicate canonical
record. Gate 3 owns the isolated inline grammar and its local recovery/state/
CST table, while the original Gate 4 wording also reserves Yulang ownership.

Deferring those inline tails to Gate 4 would leave Gate 3's named inline
surface incomplete and require Gate 4 to reopen the same AST/direct parser
topology. Creating a Gate-3-specific mini-parser or a second bridge would
violate the one-authority and no-reparse requirements.

## 2. Replacement allocation

Gate 3 owns one neutral shared embedded-Yulang delimiter bridge and its first
two adapters:

| adapter home | canonical payload |
| --- | --- |
| `YmYulangArgs` under `YmInlineRef` | call arguments |
| `YmInlineApplyArgs` under `YmInlineApply` | call arguments |

The bridge owns the Yumark outer opener, borrowed outer delimiter frame,
canonical payload invocation, return at an outer close or Yumark hard boundary,
Yumark consumption or one Yumark-owned Missing close, exact frame teardown,
and the common AST/direct outcome facts. It has one shared AST/direct ownership
decision with thin output adapters; no source slice is reparsed and no public
root/Statement parser is called.

Gate 4 reuses that same bridge for the isolated general/special command grammar:
general-command arguments, `\my` Pattern head and expression body, `\use`
`UseTree`, and `\if` / `\elsif` conditions. Gate 4 owns command classification,
body composition, `do`, if-chain layout, and their form-specific recovery. It
may add payload policies but may not add a second bridge or an inline-tail
parser.

## 3. Committed line-state ownership at its cause

Gate 3 adds one committed shared Yumark advancement primitive. It updates
`LineState` exactly once for every Yumark-owned consumed byte, including
LF/CRLF, horizontal indentation, text, structural markers, raw-fence bytes,
and quote/fence close-line suffixes owned by the enclosing `YmDoc`. It does not
advance canonical payload bytes consumed by the bridge's canonical parser, nor
the block-doc close suffix or line-doc newline, which remain their existing
outer statement-sequence owner's bytes. Rejected probes restore the complete
input/local/ErrorSink/output/cut transaction, and hard parent boundaries remain
unconsumed.

This corrects the Gate 2 judge/committed-consume split before the isolated
structural grammar relies on layout facts. Gate 5 observes the resulting state;
it does not reconstruct or patch it.

## 4. Invariants unchanged

This amendment changes neither the selected Yumark surface grammar, AST/CST
vocabulary, typed recovery roles, dispatch timing, raw-fence rule, frame
storage bound, complexity bound, nor Gates 5–7. It retains one forward path,
no opaque full-body scan, no public recursion, no CST replay, and exact
AST/direct state/recovery/range parity.

## 5. Normative gate replacement

Replace only Gate 3 and Gate 4 in §11 with:

```text
3. Add isolated inline/paragraph/section/list/quote/raw-fence grammar,
   including the shared embedded-Yulang delimiter bridge and its
   InlineReference/InlineApply call-argument adapters, with exact local
   recovery/state/CST tables.
4. Reuse that bridge for isolated general/special command grammar; add command
   arguments, My Pattern/expression, UseTree, If/Elsif condition ownership,
   do/if-chain layout, and nested recovery tables. No second embedded-delimiter
   bridge or inline-tail parser is allowed.
```

Gate 3's focused table must cover bare and semicolon references, valid
reference/apply arguments, nested canonical delimiters, missing outer close at
each Yumark hard boundary, malformed canonical payloads without duplicate outer
recovery, AST/direct child order, exact range/remainder, full ParseLocal
restoration, and absence of public Root/Statement recursion. It also asserts:

- exact accepted `LineState` transitions for Yumark-owned LF/CRLF, indentation,
  text, raw-fence bytes, and quote/fence close-line suffixes;
- that a canonical payload advances its own bytes once, with no Yumark
  double-advance;
- full input/ParseLocal/ErrorSink/output/cut rollback for each rejected bridge
  probe; and
- inherited immutable operator-table use by both inline argument adapters.
