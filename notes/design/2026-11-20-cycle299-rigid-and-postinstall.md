# Two concrete regressions, different boundaries

- C277 post-parent mixed source is reached by the existing actual raw
  install. The read table contains the selected parent and the real generated
  child. Root rank=1 and child rank=0. Root local evidence uses the scoped
  existing `EvidenceAt`; child local evidence uses the actual current effect
  and validity of that same source snapshot. No second raw install is needed
  or possible in this fixture.
- The existing rigid caller-scope regression in
  `RoleDictionaries.Examples.all_nested_children_use_caller_scope` is a real
  depth-2 selected nested Display dictionary: `list(list int)` →
  `list int` → `int`. It shares implementation key 0 across the first two
  *different* demands. The compiled key tree preserves both occurrences and
  matches the actual elaborator result. This is the older rigid elaborator,
  not a new M1-final raw source trace and not a constructor-output-depth test.
- Store or resolve row indices by demand, not by implementation identity.
  Test a partial reference map and a malformed cycle explicitly. A lookup
  failure or exhausted fuel remains unknown, never a B4 semantic rejection.
