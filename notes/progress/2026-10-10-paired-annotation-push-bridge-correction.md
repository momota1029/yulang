# Correction: paired annotation callback source coordinates

Date: 2026-10-10
Claim class: source-trace correction / bounded Oracle observation
Baseline: Yulang research branch `8921c33380b1bd66622b35c2b40bb8b2cedc726f`
Oracle source baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Supersedes: the source-attribution claim in
[`paired-annotation-push-bridge.md`](2026-10-10-paired-annotation-push-bridge.md)
only; its conditional algebraic construction remains conditional

## Correction

The previously recorded table

```text
t <: e    left PUSH_i[{io}]
e <: t    identity after filter registration
h <: e    left POP_i
e <: h    identity
```

was attributed to the wrong source interfaces. It is a conditional paired
constructor derivation if the original `[io]` callback and the reannotation
share one formal value coordinate. The source used for the trace does not
establish that premise.

The observed input is `/tmp/yulang-oracle-queue-probe/witness-row-tail.yu`,
SHA-256 `87cca79d83b1a6927fe69387dcc1f4cc39f7a8a295ea2baefbc5a8d7e016b5b1`:

```yulang
type io
my loop(x: ((int -> [io] (int -> [; 'h] 'c)), int)) =
  \(f, _) -> {
    my a: int -> [; 'e] (int -> [; 'e] 'u) = f;
    my b: int -> [; 'd] (int -> [; 'd] 'v) = f;
    (f 1) 2;
    (loop x) x
  }
```

The original callback annotation is in the tuple argument `x`; local
annotations `a` and `b` apply to `f`, a component of the separate anonymous
lambda tuple parameter. The typed arena dump at
`row-tail-run.log:5818` labels the owners `d1:x` and `d2:f`. The raw HIR
references for `a` and `b` target `d2:f`. Therefore the one-formal table does
not describe the source constructor graph.

The actual recursive application `(loop x) x` connects the coordinates
through function application and tuple projection. In the logged path:

- The anonymous lambda's tuple projection supplies `f` at `Pos29/Neg30`.
- The recursive application projects `x`'s original callback into that tuple
  argument.
- The original outer-effect `PUSH_i[{io}]` meets inherited right `POP_i` and
  normalizes to identity at `Pos6/TV6 -> Neg33/TV20`.
- The inner effect comparison reaches `TV20` under right `POP_i²`.
- The claimed reverse edges `e <: t` and `e <: h` were not found in the
  observed trace.

This is an observed source derivation for this trace only. It is not the
four-edge bridge previously asserted, does not prove the callback target, and
does not settle whether another authentic source construction can realize a
same-formal PUSH bridge.

## Admission observations

The checked source and traces are:

| Artifact | SHA-256 |
|---|---|
| `row-tail-run.log` | `b594b3b1459ba0a2d0cc31daff387e9f3f30f7f5c08489eb3aee41781882dfc4` |
| `row-tail-run-raw.log` | `553531a8f430d3091b6768e1934eb100e0d79ae5d5e47aa400fdf4628d148085` |
| instrumented `harness/src/main.rs` | `4caaef5b6a5d1dfb02d363979ee7566cb336a73869668ec7608ac8869eb50d35` |
| `target/debug/oracle-queue-probe` | `6de62e3e091f6786be380243f0a798ccfacd02423bb336c4e617d7d566f29f3e` |

The existing run record reports parse bytes 205, zero parser issues, zero
lowering errors, and return code 0. The source/audit lane did not rerun the
compiler and did not independently establish binary-to-source provenance.
Another bounded analysis of the existing normalized log counted 831 bound
dispositions, 1,538 replay offers, 373 replay enqueue attempts, and 478
semantic enqueues. Only one semantic enqueue carries positive PUSH count; it
is CR8, the original annotation's self-comparison. No logged bound disposition
or replay offer carries positive PUSH count. These counts apply to the logged
normalized events; they do not exclude an unlogged transient composition.

The observed POP alias suppressions happen during bound admission:

- The earliest reported slot is lower owner TV43, endpoint Pos23/TV12. POP2
  derivation CR225 is subsumed by prior POP1 bound B109 at the same slot.
- At lower owner TV50, Pos33/TV20, POP1 is inserted before POP2 and POP2 is
  subsumed.
- At lower owner TV50, Pos4/TV5, right POP2 is inserted before right POP3;
  POP3 is subsumed.

These admissions do not establish that TV50 is the source row named `E`.
The logs lack the occurrence-to-variable map and complete extrusion/freshening
provenance needed for that identification.

An independent compiler-referee review confirmed the distinct source owners,
the recursive application context, the normalized PUSH/POP trace, and the
admission dispositions. No semantic soundness or successor-correspondence
claim follows from this review.

## Next evidence

Instrument the pinned source so the recursive-use projection and subsequent
bound/freshening records retain source occurrence, original annotation
coordinate, local annotation coordinate, endpoint owner, and replay parent.
Then determine whether an actual admitted source route transports the same
attachment through a concrete consumer, rather than assuming the coordinates
are identical from local monomorphism alone.

Separately, the pinned source snapshot has no `run_io` definition/import for
the user's exact example. Running
`my f(cb: (int -> [io] 'c)): 'c = run_io: cb 1` in the current queue-probe
harness parses but lowering reports `UnresolvedName { name: "run_io" }`.
Therefore that harness cannot verify the user's exact expected scheme.
