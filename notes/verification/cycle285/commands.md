# Cycle 285 verification record

Lean version and the full focused stdout are in [focused](focused.txt). The exact tested Lean snapshot was local commit `fcf7968c4587991a84f52ef88120ff48a34c5cc6`. The later commits only record checks, heartbeat and handoff notes.

From the checkout root, with Lean 4.35.0 selected, the focused sequence was:

```sh
# Resolve the previous publicly completed snapshot or use its identical local tree.
base=c2c00fa3e
cd lean
modules=$(git diff --diff-filter=A --name-only "$base" HEAD -- Yulang |
  sed 's|.*/||;s|\.lean$||')
for name in $(sed -n 's/^import Yulang\.//p' Yulang.lean); do
  if printf '%s\n' "$modules" | grep -qx "$name"; then
    lake env lean --trust=0 -M 3200 -DwarningAsError=true -R . \
      -o ".lake/build/lib/lean/Yulang/$name.olean" "Yulang/$name.lean" || exit
  fi
done
for target in Audit/Cycle285*.lean; do
  lake env lean --trust=0 -M 3200 -DwarningAsError=true "$target" || exit
done
```

This uses already-built dependencies from the existing verified workspace. New dependencies were rebuilt in barrel order. The example audit contains 10 typed applications, not executable IO. The independent audit files print 139 distinct declaration axiom summaries; the only axioms printed are `propext`, `Classical.choice` and `Quot.sound`. No full project build or CI was run.

For older regression names and exit codes, see [legacy](legacy.txt). Each used `timeout 100s lake env lean --trust=0 -M 3200 -DwarningAsError=true Audit/<name>.lean`. See [static](static-summary.txt) for diff-only gates against the previous cycle and the current integration baseline; additional repetitive success lines that enumerate unchanged audit modules are omitted in that summary. These invocations skip the whole-project gate.

## Additional immutable snapshot

At local commit `3c29e8f2b12dbe9d6a2500ffe9077319e93041a1`, the only additional Lean paths since the above snapshot are the append-only barrel entry, `Yulang/GeneralRebaseTowerEndpoint285.lean` and `Audit/Cycle285Tower.lean`. The added module and standalone audit both exited 0 under the same trust level and warning policy; audit output is in [tower](tower.txt). The diff-only checks at this later snapshot again exited 0 against both baselines; no frozen paths changed. Cumulative totals: 30 focused modules, 15 independent audits, 143 distinct checked axiom declarations and 11 typed applications.
