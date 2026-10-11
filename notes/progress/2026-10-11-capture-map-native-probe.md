# Capture-map rollback: Oracle-valid constructor observation

Date: 2026-10-11
Status: unreviewed, non-authoritative executable observation. A parsed,
Oracle-valid function binding reaches an occupied-tail rollback replacement
that requests backing allocation in six of eight sampled sessions. Retained
Local correspondence, W/A3 and production adoption remain OPEN.
Producer: primary, integrating a bounded research probe.
Baseline: `0eb24ff4b01852071970dfbabb8ad94bf1451650`; working changes are
confined to `candidate_effect.rs` and this note.

## Source correction and authority

This probe follows the user's correction about value restriction. It does not
use an expansive binding such as `my ans: [E] int`. Its source root is a
syntactic function binding with an annotated function parameter:

```text
pub act tick:
    pub ping: () -> ()
my bridge(consume:((int -> [tick, 'e0] ()) -> (int -> [tick, 'e0] ()) -> ())) = consume
```

Yulang2 Oracle at frozen commit
`a58eefc31e22141574b6f20c6a5748151c6d79f1` accepts this form and its 28-port
variant under `--no-prelude --no-cache dump ... --poly`. The dump keeps
`bridge` as a function binding and displays quantified effect variables in
the public scheme. This confirms that the test uses Oracle-valid function
generalization; it does not claim that an expansive annotated value is valid.
The 28-tail dump emits `my d2:bridge:` with a quantified scheme containing
effect variables such as `['a#0[tick]]` and paired returned positions such as
`[tick; 'a]`; its body is printed as `fn p0:d3:consume -> ...`. This is the
Oracle evidence for the function-binding and quantified-row claim.
Exact command for the 28-tail source:

```text
/tmp/yulang2-oracle-read/target/debug/yulang --no-prelude --no-cache dump /tmp/yulang2-oracle-capture-28.yu --poly
```

Yulang3's parser requires a space between `bridge` and its parameter list, so
the test uses the equivalent Yulang3 spelling `my bridge (consume:...)`.
The Oracle run establishes acceptance and function generalization in Yulang2.
The Yulang3 run establishes parsing, HIR lowering, scheduled formal-annotation
selection and direct constructor execution only; it does not exercise Yulang3
binding generalization or scheme publication. These are evidence for their
respective bounded seams, not a proof of full cross-version correspondence.

Governing implementation authority is the approved
[private suspension contract](../design/2026-10-11-private-candidate-suspension-contract.md)
§6: reserve before mutation and restore route-owned state on failure. This
observation changes no language meaning, source envelope or production code.
The parent W/A3 rollback theorem remains OPEN.

## Probe path

The ignored test
`candidate_effect::tests::capture_map_native_admission_inverse_observation`
parses source, lowers HIR, selects its scheduled `FormalAnnotation`, and calls
the production `candidate_formal_annotation` constructor inside the actual
route transaction. For each source size T in `[28,56]`, it gives every one of
T distinct row variables two parameter positions, with the declared `tick`
effect in each row. Four fresh sessions per size use actual row IDs, the
production `HashMap` and default `RandomState`; no seed, key substitution, raw
table assumptions or direct map admissions are used.

A test-only failure hook fires after a successful incoming-route resource
sample when a new tail admission reaches a full public `(len, capacity)` pair
after the preceding admission logged an occupied bucket. It injects
`IdentityExhausted` before a following reserve. The test requires either this
target or complete construction, so an unrelated earlier failure cannot be
reported as a hit. The actual transaction then replays its reverse log.

During each inverse `HashMap::insert` for a saved `Some` bucket, a cfg(test)
global allocator wrapper delegates to `System` and counts same-thread
`alloc`, `alloc_zeroed` and `realloc` calls only around that insertion. The
interval excludes TLS initialization, event recording, printing, snapshot
clones and observer-vector growth. No allocation failure is injected. The
wrapper changes the test binary's global allocator entrypoint and needs
independent review; all probe hooks are cfg(test), with no production-path
change.

Public `HashMap::capacity()` is recorded only as an observable, not treated as
raw growth credit. A scoped allocator request establishes that this inverse
insertion requested allocation. Zero requests would not prove absence of an
in-place rehash. The probe does not inspect raw control bytes or directly
observe rehash.

## Result

Focused command:

```text
CARGO_BUILD_JOBS=1 timeout 120s cargo test -p yu-solver --features shadow-apply-candidate candidate_effect::tests::capture_map_native_admission_inverse_observation -- --exact --ignored --nocapture --test-threads=1
```

One ignored test passed over eight fresh sessions: T=28 and T=56, four each.
All eight reached the injected full-new-tail target. Six sessions made one
scoped allocator request during an inverse `Some` insertion. In the first
sampled session, the suffix was:

| Operation | Row | Saved bucket | Before `(len, capacity)` | After `(len, capacity)` | Scoped requests |
| --- | ---: | --- | --- | --- | ---: |
| Admit occupied incidence on A | 185 | Some | (27,28) | (27,28) | 0 |
| Admit new tail B; inject failure after sample | 192 | None | (27,28) | (28,28) | 0 |
| Inverse B: remove | 192 | None | (28,28) | (27,27) | 0 |
| Inverse A: restore saved bucket | 185 | Some | (27,27) | (27,56) | **1** |

Earlier admissions in the same transaction built the 27 live tails. The
inverse allocation occurred on an existing key, after removing B, in the
actual reverse sequence. The full event trace also shows the earlier
reservation boundaries; the sample's first two admissions are a completed
native constructor prefix.

Every session compared the pre-transaction incidence map, record vector and
key set with the post-rollback values; all matched. This is evidence of a
constructor-qualified failure prefix with an inverse allocation request.
It refutes universal allocation-free inversion for these
`FormalAnnotation` constructor prefixes in the sampled runtime. It is not a
retained Local counterexample, does not prove the prefix occurs inside the
retained Local failure domain, does not inject allocator failure, and does not
refute W/A3 as a whole. Other owners, failed-route accounting, transaction
reachability and linked-runtime applicability remain separate.

## Limits and next owner

The eight runs use uncontrolled RandomState seeds; their indices are not
reproducible seeds. The observed 6/8 allocation incidence is finite evidence,
not a probability claim or a required hit rate. The Oracle validation confirms
the value-restricted function-binding form and its effect-variable scheme; it
does not validate Yulang3's scheduler or transaction lifecycle. Yulang3 used
the parser-required spacing and the corresponding declared effect operation.

Next: independently review the frozen test-only instrumentation and the
Oracle/source claim. Then establish whether an authentic retained Local
constructor/failure route reaches the same suffix, or continue with the
separate authorized storage repair route. Keep native allocation-free
rollback, original W/A3, complete Simple-sub inference, effect hygiene,
soundness/principality and F5 cutover OPEN.

No broad suite or benchmark was run. The focused test used one Cargo process,
one test binary, eight source sessions, no seed sweep, and no performance
measurement table. The ignored test remains research scaffolding; this note
does not certify it or grant implementation authority.
