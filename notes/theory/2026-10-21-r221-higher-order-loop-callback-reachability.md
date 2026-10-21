# R221 — Higher-order loop callback reachability

Status: bounded candidate-only source/native outcome C for this exact source.
The original computation-forwarding theorem and global R71/R72 remain OPEN;
no independent review is claimed.

## Source and actual callback consumer

The exact source preserves R72's `loop`, `direct`, and `helper` definitions,
then declares `repeat (f:[io] int -> int) (z:[io] int)` with two `f z` calls,
and evaluates `repeat loop q`. Parsing/lowering had no structural recovery.
Public ordinary `CandidateInference::solve(hir)` returned no solver errors and
no candidate conflicts.

The two callback body Applies are source occurrences 19 and 22. The actual
`f z` source Call at occurrence 19 resolves `f` as its registered formal and
`z` as its parameter. It owns production Work::Bound extrusion 24 through
processing relation 146. The complete lineage record identifies relation 146
as a source-origin at occurrence 19. Its raw lookup is
`BoundKey(Effect(EffectRow(21)), Positive, Effect(EffectRow(31)))`; the
production copy transports that bound to owner `Effect(46)` while retaining
item `Effect(31)`. The other production Work::Bound lookups are the earlier
direct `loop x` and helper-body `loop y` calls.

The actual `repeat loop` source Call at occurrence 26 has callee `repeat` and
argument `loop`. Its retained Local route maps the callback formal item row
`Effect(31)` to `Effect(57)`. The source Call observer exposes no
`formal_registration` for this provider application, so it does not establish
the full provider-lineage bridge from the actual `loop` function into that
callback formal.

## The loop slot-4 path stays distinct

The loop Lambda slot-4 source admission is
`BoundKey(Effect(EffectRow(5)), Negative, Effect(EffectRow(41)))`, physically
owned by `Effect(5)` in `EffectUpperRow[0]`. Its exact loop Local route maps it
by a checked FreshUse witness to
`BoundKey(Effect(EffectRow(73)), Negative, Effect(EffectRow(69)))`.
The source relation has 11 lineage records and includes that exact
source-to-image FreshUse edge.

The complete intrusion forest event log replays exactly to the final snapshots
(48 Effect rows). Throughout the history, callback formal item `Effect(31)` and
loop slot-4 item `Effect(41)` retain distinct roots; no parent write attaches
either item. The production trace selects neither source item `Effect(41)` nor
Local image item `Effect(69)`. The callback's actual Work::Bound selects the
formal's separate raw item `Effect(31)`, which its Local route maps to
`Effect(57)`. Thus the source does produce a later Work::Bound consumer, but
the complete bounded trace does not produce the requested slot-4 alias-changing
merge followed by a Work::Bound copy of that item's lineage. This is outcome C
for this source, not a general impossibility claim.

The remaining premise is now precise: an accepted source must establish a
source-qualified relation between an actual retained provider's item lineage,
an alias-changing merge, and a later Work::Bound selected copy, with its
independently justified consumer. In this source, the callback Work::Bound is
authentic but its provider formal lineage is not shown to originate from the
slot-4 row, and the two item representatives never merge.

## Checks and limits

- Focused R221 test: passed (1 test).
- `RUSTC_WRAPPER= cargo test -q -p yu-playground`: passed.
- No compiler semantics, production code, sample, or expected output changed.
- This result closes only the exact candidate source case. Arbitrary prefixes,
  global R71/R72, the original theorem, semantic approval, and production gates
  remain OPEN.
