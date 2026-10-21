# R280 — Yulang2 qualified constructor patterns

Status: checkpointed syntax-only continuation under Authoritative R149. This addendum does not implement role lookup, tuple typing, semantic pattern matching or runtime evaluation.

## Source form

The exact pinned `std::core::fmt` source uses constructor paths followed by a same-line payload pattern, for example `opt::just fill`, `std::data::list::list_view::leaf item`, and `result::ok inner`. The case-arm arrow follows the payload. The current parser admits Pattern ML application through GML classification; a plain `f x` already constructs an application node. The pinned qualified path plus same-line payload still fails because it is not recognized as a completed constructor receiver.

## Parser boundary

A completed `::`-qualified constructor path may admit its immediately following same-line Pattern argument as one `PatternMlApplicationTail`. Keep the arrow and arm guard as caller-owned boundaries. Do not generalize this to unqualified same-line `f x`; that source distinction is required to preserve existing recovery and application semantics. Parenthesized constructor payloads and nullary qualified paths continue through their current productions.

The shared design's Tuple/pattern stage requires preserving ordered Pattern children across downstream traversals. This syntax repair only exposes the source shape; it proves no downstream traversal or R149 sample result. The proof companion likewise keeps general pattern/effect handling separate from narrow supported constructors.

## Result

The case-arm owner contributes PATTERN_STOP_ITEM to preserve a caller-owned ordinary item. R280 narrowly permits that item to become a Pattern argument when the current receiver is a completed ::-qualified constructor and the argument is on the same line. The argument is represented by the existing PatternMlApplicationTail; arrow ownership remains with CaseArm. The exact pinned census drops from 32 to 2 diagnostics without changing source bytes.
