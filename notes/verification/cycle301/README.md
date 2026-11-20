# Cycle 301 independent checks

Start with the existing Lean cache for the preceding work tree. This script
links only prior modules into a fresh directory, excludes all current-cycle
module names, then recompiles current modules in appended barrel order. We
check every theorem in standalone audit files under Lean's kernel trust 0 and
warnings-as-errors. Only propext, Classical.choice and Quot.sound are allowed.
The index lists the exact formal statements by namespace. The runnable fixtures
inspect actual stored state data and reader results; no test is presented as
execution of a noncomputable Prop judgment or a Rust implementation.

```sh
bash notes/verification/cycle301/verify-focused.sh <prior-commit> <prior-olean-root>
sha256sum --check notes/verification/cycle301/source-sha256.txt
```

For the publisher's local check, the preceding published tree's identical
local commit is an acceptable first argument. In addition the two
`tools/verify-lean.sh --no-build` transcripts (previous work and exact
integration) are preserved under `static/`. Whole-tree Lake, CI, Rust, and
Yulang2 execution are not performed here.
