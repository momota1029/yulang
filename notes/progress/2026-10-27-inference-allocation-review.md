# Independent review: inference allocation chronology

Date: 2026-10-27. Reviewer: `principality`, independent of the producer.

**ACCEPT for the local allocation-chronology construction and its qualified
note. No blocking defect found in that scope. Original inference termination,
full native NQ, and original source/native correspondence remain OPEN.**

## Frozen targets and review scope

| Target | SHA-256, checked before and after review |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalInferenceTerminationResolution.lean` | `a89a316ea72e472b0e2c09effc144730dc4c683228008caf42a433d0a969a6dd` |
| `notes/theory/2026-10-27-original-inference-termination-resolution.md` | `7dc8f790d64717b76711df9a932ee49c5deab959ce2c3e77d9e820e0b48b0f00` |

Read all 549 Lean lines and all 242 note lines. Compared the definitions and
proofs with NQ §5.3 and its allocation/Function argument, `Contracts`' original
`InferenceTermination`, the imported native Request/Bound/Key/interner
definitions, and their Rust owners. Every dependency hash listed in the note
matches the current file. Additional Rust owners inspected were
`term.rs` (SHA-256
`d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`)
and `candidate_source.rs` (SHA-256
`96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`).

## Findings and acceptance boundary

1. **The chronology premise is local producer formation, not a completed
   inference result.** `Step.cell` requires a fresh immutable raw cell, available
   direct row leaves, existing term children, and no structural endpoint hidden
   as a Value leaf. `Step.relation` and `Step.replay` require available pair
   endpoints. Induction derives `history_valid`; `term_uses_before` uses child
   existence and immutable readback to rule out an old term acquiring a new
   reference through a formerly absent child. There is no finite future universe,
   successful drain, copy successor, or global termination premise.

   These obligations are not established for all Rust producers here.
   `term.rs::live_variable` (1205ff) interns the given ordinal without checking
   row allocation. `positive_function`/`negative_function` and
   `require_function_children` check child existence, lineage, kind and polarity;
   they do not establish the row-vector ownership invariant. The note correctly
   marks this distinction. `lib.rs::fresh_value_at_level`/`fresh_effect_at_level`
   (10456ff/10487ff) use the current bounds-vector length and append both bounds
   and levels. Relating those vectors, initial terms, all producer calls and
   previous merges to this empty-origin `History` is still an extraction proof.

2. **The raw relation identity bridge retains the complete native key.**
   `call` invokes `NativeRelationInterner.Native.call`; admissions store its
   returned ID with the same Key. `history_native_readback` constructs native
   history and derives persistent full readback, rather than assuming cache
   coherence or picking a replacement ID. `earlier_replay_id_excludes_later_row`
   uses same-ID/full-Key uniqueness. `earlier_replay_cannot_read_fresh_request`
   uses the actual `NativeValueStructure.Request.key`: pair, context, optional
   source index, transformer, and all five deferred-demand fields remain present.
   The `[] []` arguments in the readback proof are unused auxiliary Arena
   context/transformer lists in the imported theorem; they do not replace any
   stored Key field. No source-set quotient or reduced-key equality is used.

3. **Replay data is preserved; Replay behavior remains unproved.** The new
   `Replay` retains child/lower/upper admissions and both native Bound kinds,
   including owners, polarity and endpoints. This matches the fields compared
   by Rust `Dependency::Replay`. Its constructor does not establish that a given
   Rust dependency was produced, that its input bounds have the specified
   relation fibers, or that the child was enqueued. Those are separate operational
   obligations. `candidate_context_begin_replay` (3992ff) constructs head-delta
   products, complete scoped child keys, dependency deduplication and a retained
   operation; `candidate_apply_value` (1115ff) and the drive loop supply the
   missing operational connection. The note leaves this connection open.

   Consequently the theorem can exclude a previously published outer product
   **after** a concrete native history and later allocation are supplied. It
   cannot yet identify the remaining owner, establish a complete queue loop,
   or derive NQ's successor/maximality contradiction. The two fresh-row/Function
   corollaries preserve the four Function ports and require actual readback of
   the new argument; they do not manufacture a fresh Function or request.

4. **Errors and inventory are not silently converted into success.** The
   imported `Native.call` preserves the Rust guard order, scoped-flow reuse,
   checked work charge, reservation failures and partial flow allocation before
   a relation failure (`candidate_context.rs`, 3062ff). The new `call` stores
   the resulting native state even on failure; no admission is added for an
   error. `failure_has_no_step` follows from each constructor's running premise.
   `contextAssertion` remains the distinct projection of an assertion failure,
   not a successful availability result.

   `Step.inventory` models successful other-caller charges with both the
   checked-arithmetic bound and 65,536 work bound. This agrees with
   `ScopeInventory::charge` (`candidate_source.rs`, 217ff), which writes only
   after both checks. It does not model every other caller's failing operation.
   `rowFailure` abstracts possible failure without deriving an allocation
   failure condition. Term-allocation failures are also outside the full
   operational model, as the note says. Terminal failure is a property of
   this forward projection; transaction rollback/recovery is not modeled.

5. **The original target is unchanged and unsolved.** Raw reference traversal
   covers Value structures and direct Effect rows; it does not inspect Effect
   view interiors or references hidden in contexts/demand metadata. Level-only
   steps preserve counts but do not implement merge. There is no rollback step,
   source initialization, executable extrusion machine, drain progress proof,
   or concrete original `inferInitial`/`inferStep` instance. Neither this theorem
   nor the manually reviewed NQ argument is an `Acc` proof or an original-source
   refutation. The frozen note states these boundaries adequately.

## Independent verification

Pinned Lake: `/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`.
Observed Lake `5.0.0-src+eb6cafb`, Lean `4.35.0`, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. From `notes/theory/lean`, both final
checks used `timeout 120 env LEAN_NUM_THREADS=1`, that executable, and
`env lean -j1 -M1024`:

- Direct exact-source check of
  `YulangClosure/OriginalInferenceTerminationResolution.lean`: exit 0, no diagnostics.
- Imported-module audit at
  `/tmp/yulang-principality-inference-allocation-review/AuditImported.lean`,
  with `--root=/tmp/yulang-principality-inference-allocation-review`: exit 0,
  no errors or warnings. Module ownership selected every declaration, including
  generated/private constants; every type and transitive axiom list was printed.
  All 157 theorem types were inspected. The census found 404 declarations:
  183 definitions, 157 theorem constants (25 authored, 132 generated/private),
  34 constructors, 15 recursors and 15 inductives. There are no project axioms
  or opaque declarations. An executable audit rejects any dependency outside
  `propext`, `Classical.choice`, `Quot.sound`; none was found.

The 25 authored theorems' axiom sets exactly match the frozen note:

| Complete set | Authored count | All theorem constants |
| --- | ---: | ---: |
| `[]` | 1 | 62 |
| `[propext]` | 10 | 81 |
| `[propext, Classical.choice]` | 2 | 2 |
| `[propext, Quot.sound]` | 6 | 6 |
| `[propext, Classical.choice, Quot.sound]` | 6 | 6 |

The initial combined source-plus-meta-audit exceeded the unchanged 1 GiB limit
and exited 134 with `lean::memory_exception`. Its source/log remain in the
same scratch directory as `Audit.lean`/`Audit.log`; this was a resource failure,
not a proof failure. Separating the exact source check from the imported census
resolved it without increasing limits or changing either target.

Successful audit source SHA-256:
`363c612a9e46fe8b565f21cb6bf4be751880b3ed1e07aeced96e3f5011f2e8e2`.
Complete successful audit log SHA-256:
`55f06e1f93bff6c6aef9f4732ec783a80f9d82b7dc5824c975881463421f5ff1`.
Failed combined audit log SHA-256:
`48bc2200174632932b9ea98fd0a0c30e6dc353ce535531045f1c7efc7b79940a`.
Additional scratch files are `SourceCheck.log`, `authored-theorems.txt`,
`Theorems.txt` and `GeneratedTheorems.txt` in that directory.

Only this review file and the named `/tmp` scratch were written. No proof/note
edit, Git operation, native compiler/test execution, child, shared-status update, Lake build
or `.olean` output. All review-owned checker processes have exited; writes stopped.
