# R159 untracked search boundary incident

While locating the original App definitions, a broad `rg` search traversed
`notes/theory/lean/YulangClosure` and returned one matching line from the
untracked `SourceLogicalOccurrencesR103.lean` file. That artifact was outside
the approved read set. The single match and any inference from it are excluded
from all subsequent reasoning. The file was not opened separately, modified,
hashed, or staged. No other untracked match from that search is used.

The exact governing App inventory and missing law are taken only from the
tracked R158 handoff and tracked `OriginalSourceGeneration.lean`,
`OriginalSourceEnvironment.lean`, and `OriginalSourceInterpretation.lean`.
Future searches use those exact files and exclude untracked artifacts.
