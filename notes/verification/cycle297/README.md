# Cycle 297 B4 witness compiler checks

The raw model universe is not assumed finite. A reached source state gives
finitely many questions. Each install's accepted sign has one joint prior
model; its rejected sign has one prior counterexample to both obligations
being simultaneously true. The negative merge question is also about
one prior model. Head-specific witnesses are not required to be prior
models. The provided list and comparison bits need independent coverage and
reflection; the classical existence theorem is not a runtime solver.

For a locally built C296 cache, set the first argument to the previous work
pin, or to a local commit with the identical previous tree. From the root:

```sh
bash notes/verification/cycle297/verify-focused.sh <C296-commit> <prior-olean-root>
```

This excludes all C297 objects from a shadow cache, rebuilds only added
modules in barrel order, audits each C297 file separately, rechecks
specific previous suites, then runs and compares the three executable
controls. It does not use the full Lake target. Shell commands reuse the
existing Lean 4.35.0 toolchain, in one thread.

- `depth-observer.txt`: actual registered root and candidates of the
  252/271 nested-output example, with one strict projected proposal.
- `merge-observer.txt`: two comparisons (the second site of each need not
  be registered), and the registered actual step of the earlier explicit
  merge stress state. Source reachability of the stress state is not asserted.
- `signed-polarities.txt`: raw finite-table control, including intentionally
  incomplete tables, no semantic absence asserted for those.
- `theorem-index.md`: exact statements audited, including 239/240 sharp raw
  prefix witness lower bounds and the certified pre-install refresh.
