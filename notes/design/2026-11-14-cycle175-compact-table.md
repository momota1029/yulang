# Compact table: bounded next optimization

Verified exact source and 9 named-theorem audit, both trust=0/exit0. Remove duplicate role entries, leave original fuel
and final all-edge check unchanged. New generalized tableOn takes an explicit
inventory once and carries it through all recursion levels. Its invariant is
computedHeight equality at all declared role nodes, assuming only coverage by
the inventory. eraseDups supplies coverage; order/duplicate identities do not
enter semantics. Existing modules are not edited.

This avoids per-round eraseDups or roleNodes reconstruction. With V unique
roles there are F*V entries rather than F*N, E child fold steps per round
rather than M, and table lookups of lengthV rather than N. Naive eraseDups is a
one-time preprocessing cost; no asymptotic or runtime claim is Lean-proved.
The user-visible certificate returns the same Bool for all registries/fuel,
including cycles and syntactically invalid registries. Smaller fuel V is not
used. A bounded paired measurement is recorded below; no general runtime guarantee
is inferred from it.


## Validation and bounded measurement

Source and imported audit: Lean4.35.0, `-j1 --trust=0`, timeout180 each,
both exit0. No failure/retry. Only propext/Classical.choice/Quot.sound.

Benchmark: `BenchCompactTable175.lean`, one process with timeout60, exit0.
At each of the two previously used sizes12/20, one warmup and three paired
measured samples compare table and compact on the same duplicated-edge chain.
All Boolean answers true. Synthetic registries are NOT asserted Checked.
Monotonic nanosecond timings include printing the result, as in the prior
harness. No change to runtime compilation mode or checker fuel.

- length12: 36 original entries,13 compact entries per nonzero round.
  Table samples(ms):13.433126,12.114089,13.005937;
  median13.005937, range12.114089–13.433126.
  Compact samples(ms):3.024835,3.133176,3.068526;
  median3.068526, range3.024835–3.133176.
- length20:60 original entries,21 compact entries.
  Table samples(ms):52.440135,51.637066,52.955242;
  median52.440135, range51.637066–52.955242.
  Compact samples(ms):11.938545,12.756633,11.696688;
  median11.938545, range11.696688–12.756633.

This bounded run detected an improvement in both tested fixtures (median
ratios approximately4.24 and4.39), not a universal speedup or asymptotic
measurement. The general Boolean equivalence is proved separately.
Total benchmark process count for this helper cycle is3 (one initial failed
import, one original/table comparison, one table/compact comparison), well
below8 and10minutes. No additional benchmark runs are pending.

The table no longer repeats equal roles, but still scans declarations per
unique role and uses linear table lookup. With V unique roles, rough round
work is O(V*D+E*V+V), plus one-time inventory deduplication; this cost analysis
is informal, not a Lean theorem. Array indexing/adjacency caching remain later
independent candidates.
