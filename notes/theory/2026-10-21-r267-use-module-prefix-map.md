# R267 — direct use bases resolve to pinned module prefixes

The R267 probe reused R266's exact 40-file blob checks and source-preserving
direct `UseDeclaration` CST locator. Each declaration's first `UsePath` is
the base route; grouped selected-item paths remain subsequent path nodes. Of
112 declarations, 108 bases begin with `std::`. Every one resolves by longest
existing module prefix to one of the 40 pinned module paths; none is unresolved.
The remaining four are non-`std` routes declared and re-exported within the
same source file, not additional file edges:

- `time.yu`: `pub host act clock` and `pub use clock::*`.
- `io/console.yu`: `pub host act warn` / `die`, then `pub use warn::warn` and
  `pub use die::die`.
- `io/file.yu`: `pub host act file`, then `pub use file::*`.

The CST has 21 additional selected-item path nodes in grouped forms. The
longest-prefix result is a source locator over exact pinned bytes; it does not
prove Y2 resolution, item selection, visibility/re-export behavior, module
registration, declaration identity or runtime publication. It gives a
concrete candidate import graph for the next source-order/closure check. The
temporary probe was removed and made no retained code/test changes. See R267
contract.
