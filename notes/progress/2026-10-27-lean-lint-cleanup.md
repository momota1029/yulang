# Bounded Lean lint cleanup

Date: 2026-10-27. Producer: `/root/soundness_hygiene`.
Scope: the nine explicitly leased proof modules below.

**Result: all 668 reported warnings are removed.** Every modified source
passed its first direct pinned Lean check with no diagnostics. The parent's
fresh focused build also passed all 40 jobs without diagnostics. Authored
declarations and their interfaces retain their types; the full before/after
census separately records compiler-generated proof-helper changes.

This packet changes proof presentation and local proof-variable names. It
does not establish any new original Yulang theorem or close the remaining
soundness, Effect hygiene, principality or inference-termination obligations.
The parent owns independent diff review and integration.

## Changes and per-file results

The starting warnings came from
`/tmp/yulang-full-integration-20261027.log`.

| Module | Original warnings | Final direct warnings | Direct result |
| --- | ---: | ---: | --- |
| `PaperExecutionSyntax` | 23 | 0 | exit 0 |
| `PaperExecutionBinderLaws` | 235 | 0 | exit 0 |
| `ControlComposition` | 3 | 0 | exit 0 |
| `PaperTermSubstitution` | 96 | 0 | exit 0 |
| `PaperCoreStep` | 4 | 0 | exit 0 |
| `PaperTypeBetaExecution` | 276 | 0 | exit 0 |
| `PaperTupleSplitExecution` | 22 | 0 | exit 0 |
| `PaperPerformLetExecution` | 2 | 0 | exit 0 |
| `NativeIntegerComparison` | 7 | 0 | exit 0 |
| **Total** | **668** | **0** | **9/9 passed** |

Unused simp arguments were removed from their exact reported list positions,
preserving their uses in other invocations and the order of retained arguments.
The scratch edit manifest records each original position, removed arguments
and retained arguments. In particular, the large `all_goals`/`first` proofs
were checked through every branch after these edits; none needed a repair or
a restored premise. This was not a global deletion of a lemma name.

`PaperExecutionSyntax` consistently renames the local termination-evidence
identifiers `hmem`, `hsmall` and `hdefault` to underscore-prefixed names.
Their evidence and uses remain. `PaperTermSubstitution` similarly renames the
local `hv` witnesses inside recursive definitions and their termination
proofs. Its public theorem parameters named `hv` remain unchanged. The parent
independently confirmed the Syntax diff is exactly these local renamings.

Remaining deprecated `if_pos`/`if_neg` uses become the pinned library's
canonical `ite_eq_left`/`ite_eq_right`. One already unused `if_pos rfl` argument
was removed with its unused-argument warning.

No source constructor, algorithm branch, declaration statement, premise,
conclusion, instance order, linter configuration or checker setting was
weakened or replaced. No authored proof was deleted. No `sorry`, project axiom,
admission, native trust or checker bypass was introduced.

## Declaration types and axioms

Before editing, an independent census imported the parent's fresh original
artifacts and selected every constant originating in the nine modules. The
same unchanged census script ran again after the parent's successful rebuild.
Both runs printed full `Lean.Expr` types and transitive axioms, rejected
unapproved axioms, and included private and compiler-generated constants.

The exact counts are:

| Comparison | Count |
| --- | ---: |
| Before originating declarations | 2,699 |
| After originating declarations | 2,683 |
| Common names with byte-identical type representations | 2,410 |
| Common names differing only in bound-variable display names | 117 |
| Common names with other type differences, all generated proof helpers | 125 |
| Removed generated proof-helper names | 47 |
| New generated proof-helper names | 31 |
| Axiom-set changes among all common declarations | 0 |

All names in the last three helper categories end in compiler-generated
`_proof_*` or `_simp_*` suffixes. Removing unused simp arguments changes which
auxiliary proofs the elaborator creates and their numbering. Those artifacts
are not authored theorem/interface declarations. The complete helper changes
are retained in `type-comparison.json`; this report does not claim all 2,699
original internal names remain identical.

Every authored declaration and every non-helper interface declaration is
retained with the same type, allowing alpha-equivalent bound-variable names.
The 117 alpha comparisons retain de Bruijn indices, binder kinds, universes,
constants and expression structure; only binder display names and formatting
are ignored. This includes the expected equation/matcher types affected by
renaming local proof binders. No non-helper type difference remains.

Every original and new declaration, including the 31 newly generated helpers,
passed the transitive axiom audit. The union remains `propext`,
`Classical.choice` and `Quot.sound`. No extra axiom appears in the post-build
environment.

The first Python-only comparison used inefficient repeated string assembly.
It was stopped after approximately one minute and rerun with equivalent
linear string assembly. The original script and an explanation are retained.
The equality criterion did not change; no Lean invocation failed and no proof
file changed during that repair.

## Actual checks and finite budget

Pinned toolchain: Lean 4.35.0,
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Lake
`5.0.0-src+eb6cafb`, at:

```text
/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake
```

Each proof was checked from `notes/theory/lean` with:

```text
timeout 120 <pinned-lake> env lean -j1 -M1024 YulangClosure/<Module>.lean
```

The two census invocations used the same `-j1 -M1024` and 120-second bound,
with `--root=/tmp/yulang-lint-20261027` and `Baseline.lean` in that directory.
All **11 of the 12 permitted checker invocations** exited 0. Nine were direct
source checks; two were the before/after census. All nine direct diagnostic
logs are empty. No repair invocation, larger memory cap or timeout was needed.

The parent-owned focused build receipt is
`/tmp/yulang-lint-focused-build.log`, ending in successful completion of
40 jobs. It was read after the parent signaled completion. This leaf did not
run a build or write compiled output.

## Frozen files and evidence

All proof paths below are under `notes/theory/lean/YulangClosure/`:

| File | Final SHA-256 |
| --- | --- |
| `PaperExecutionSyntax.lean` | `d0dc9871c382ca945059167b8b9e05f8f672170208a994f081e29760a207b87d` |
| `PaperExecutionBinderLaws.lean` | `5f7c9058bafdf7ac083709714b5f978942bbe0442b4b289fe93e0df92dd2e8a8` |
| `ControlComposition.lean` | `10e3801e00fa279b16d1cc98e50775b9372d114fbcc648d3cd052f35ba4da7b2` |
| `PaperTermSubstitution.lean` | `baeae84bc7d063152b6c0cb6a3f9ec650f291010edbe065e044099daa94b4495` |
| `PaperCoreStep.lean` | `e1ccb094a8aa7a08a16f9da565240c62c79b7094aa5f2e6f27ab604aee49f662` |
| `PaperTypeBetaExecution.lean` | `a4f471ec1d3f02ebd1fb3efb0597e0df33c49280a3b3aefc4772d68d2328f352` |
| `PaperTupleSplitExecution.lean` | `1a3424f10108f1c563f7c44888255e9f30fb9895fcfd433b1664701eb36b7e5d` |
| `PaperPerformLetExecution.lean` | `6a2bae07df66483bbd1cef5d761c29ab3cc7f89a0b043ed03ad3907b04ddc928` |
| `NativeIntegerComparison.lean` | `fbd98d89898d58b529add810787538df8b69d9172bdc86206418fb2dd74c588b` |

Evidence is in `/tmp/yulang-lint-20261027/`: exact `before/` source copies,
before/after hash manifests, original warning inventory, exact edit manifest,
per-file diffs and checks, full before/after type/axiom records, compact type
hashes, comparison script and results.

| Compact evidence | SHA-256 |
| --- | --- |
| `after-manifest.json` | `f57c57144efb503d42595ed88200122da112fee7e9394fe575556d793e1467c1` |
| `baseline-type-hashes.json` | `2fc4dc28e820cd105aee70a0af001d9c4eefbeb5e75a46cb61a7ff0cf9122077` |
| `after-type-hashes.json` | `ecff27f212c9660be35b567f570151064f816c5cd902857d146b27c89a812bba` |
| `type-comparison.json` | `0fab61c601848c1f895f54b2cbeef92bede84936522d719768e58de205f3278d` |
| `comparison-summary.json` | `1a7b380768473c60d1141b3155e985f3d0c5b0496b8c8e534a163a06b3a98af9` |
| `checks.json` | `cf58587f084ecd4d8d4cf73bcfed361b184df533d3f0aa9f8b2e16d71fb7aa49` |

There is no remaining lint blocker within this packet. Original semantic
obligations remain outside this cleanup. All proof and audit processes have
exited; writes stop with this note and the scratch freeze receipt. The only
repository writes were the nine leased sources and this note. No other proof,
note, review, shared status, import root, configuration, Git state, build cache
or compiled artifact was changed by this leaf, and no child agent was spawned.
