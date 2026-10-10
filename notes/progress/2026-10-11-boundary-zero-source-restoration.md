# Boundary-zero source capture and target restoration

Status: reviewed bounded executable source characterization; the failure-state
construction remains open. This records a genuine capture and successful child
replay control, not an absent-child counterexample or an impossibility theorem.

## Source and result

The ordinary program is the established distinct-tail witness followed by one
top-level reference:

```yulang
act E
my left (f:int -> ['r] int) g = { my bridge (consume:(int -> [E, 't] int) -> ['x] int) = ({ my cb z = { my old = f 1; consume cb }; my feed = g bridge; consume cb } as [
    E
    'x
] int); bridge }

my later = left
```

Parser structural recoveries were empty; ordinary `execute_candidate_graph_plan`
returned `Ok(())` with `errors=[]`. The extra top-level reference changes the
selected rows to S50, C56, R44, X30, T26 and T'67.

Boundary-zero capture contains the exact target bound:

```text
BoundKey(E50, Positive, E44)        relation186
BoundKey(E44, Negative, Allowance1) relation175
```

The later module reference captures that bound, then freshens/restores its
per-use image as `BoundKey(E96, Positive, E102)`, relation452. This is genuine
fresh-use transport, not unchanged-owner restoration or canonical equality.
The actual ordered fiber is `(452,453)`, where relation453 is the corresponding
negative self-bound. Replay emits relation452 and the typed worklist dequeues
it. Thus this source constructs the target-bound capture/restoration state, but
the observed child is present and consumed; this run is not a restoration
failure.

The local `bridge` reference at boundary1 still does not capture the target
positive bound. The owning constructor explains the distinction: positive
captured bounds are enumerated only for rows with `level > boundary` and not
marked non-generic. Boundary1 excludes level1 S; boundary0 includes it, after
which freshening allocates E96. This is a conditional constructor explanation,
not a universal source-impossibility proof.

## Review and evidence boundary

An independent compiler-referee review accepted the artifact as a bounded
capture/fresh-restoration control and independently confirmed target capture,
fresh owner E50→E96, ordered input `(452,453)`, and child452 emission/dequeue.
The review found no correctness issue within those limited claims. It also
confirmed that unchanged-owner restoration and an absent or unrescued child
remain unestablished.

One standalone compile and one authentic source execution were run on a pinned
private copy. The compile used one CPU, a 1.5 GiB address-space limit and a
120-second timeout; it completed in 5.14 seconds with 485052 KiB peak RSS.
The source run completed in 0.216 seconds with 11680 KiB peak RSS. It recorded
257 restores, 892 replay-input events, 333 restore child events, 538 post-merge
dequeues, 14 merges, 60 action checkpoints and five full captures. These are
execution coverage counts, not a source enumeration. Cached parser/HIR
artifacts' exact source provenance is unknown; the compiler execution is not
an independent semantic oracle.

The exact source, private observer, build/run scripts, dependency hashes and
full logs are retained in `/tmp/yulang-source-state-construction-20261011/`;
the producer's complete frozen report is `/tmp/yulang-source-state-construction-20261011.md`.

## Remaining question

No independently justified missing ordered fiber `omega` has been found, and
no child has been shown absent after replay, canonical transport, intrusion,
Value memo and diagnostic consumers. A second source continuation was not run:
a second top-level reference repeats fresh-use capture, while local references
retain the boundary1 exclusion; neither provided a new discriminating fiber.
This finite result neither proves universal rescue nor proves source
impossibility. Next work must identify a source-owned unchanged-owner route or
a justified nontrivial `omega` before another source probe. Keep recursive
context admission and concrete negative formal rows gated under the approved
design.
