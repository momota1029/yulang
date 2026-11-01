# R157 dispatcher boundary incident

The R157 sprint-end dispatcher `/root/next_action_after_r128` issued this
read-only command despite the explicit packet boundary:

```text
git show 9be8ffc3e:tools/inference-playground/src/runtime/machine.rs
```

That immutable blob belongs to the quarantined UNKNOWN_WRITER runtime path and
was not an authorized read. The dispatcher reports that the output was wholly
truncated and was not analyzed or used. Exclude all output from this read from
subsequent decisions. No working-tree files, Git refs/index, caches, or
environments were changed; no repository artifact was produced by the
dispatcher. Mark that worker STOPPED and do not reuse its recommendation. A new
dispatcher may use only the frozen R157 contract, reviewed R157 artifacts and
their receipts; it must not inspect runtime paths, including immutable blobs.
