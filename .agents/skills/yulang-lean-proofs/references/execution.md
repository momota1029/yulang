# Execute and debug the pinned Lean project

## Environment and ownership

Start in `notes/theory/lean` and inspect `lean-toolchain`. For elan, resolve the
already-installed toolchain before invoking any proxy. In a POSIX shell:

```sh
yulang_lake_bin="$(elan which lake)" || exit 1
"$yulang_lake_bin" --version
"$yulang_lake_bin" env lean --version
```

`elan which lake` is a read-only lookup. If it fails, return installation to the
primary under existing permissions; do not invoke the unresolved proxy. For a
verified official distribution instead, set `yulang_lake_bin` to its absolute
native `bin/lake` and run the two version commands. Verify release
and checksum; preserve real execution failures. On restricted Linux containers,
extract archives with `tar --no-same-owner`. Do not change global defaults,
the repository pin, lockfile or packages as a proof repair.

One owner controls Lake's build/cache. Preserve existing `.lake` files: this
branch contains historical tracked probes as well as ignored outputs. Do not
blanket-delete it or build concurrently against changing inputs. Isolated copies
still share CPU and memory. The helper bounds total elapsed time, terminates its
process group on POSIX timeout, and sets `LEAN_NUM_THREADS=1`; project `-j1` and
`-M1024` constrain individual Lean invocations, not total OS-level memory.

## Focused build and manual audit

From the project directory, build the actual module and its imports first:

```sh
"$yulang_lake_bin" build +YulangClosure.PaperTypeSubstitution
"$yulang_lake_bin" env lean -j1 -M1024 YulangClosure/PaperTypeSubstitution.lean
```

`lake env` does not refresh imports. Include actual changed modules even when
the default root does not import them. At integration, check intended imports
and run the existing target once:

```sh
"$yulang_lake_bin" build
"$yulang_lake_bin" env lean -j1 -M1024 YulangClosure.lean
```

For a manual audit, create a uniquely owned temporary `LeanProofAudit.lean`
(ordinary module name, without hyphens) outside tracked sources. Insert the
actual imports and every delivered theorem, for example:

```lean
import YulangClosure.PaperTypeSubstitution

#check @YulangClosure.PaperTypes.subst_id
#print axioms YulangClosure.PaperTypes.subst_id
#check @YulangClosure.PaperTypes.subst_comp
#print axioms YulangClosure.PaperTypes.subst_comp
```

Run `"$yulang_lake_bin" env lean -j1 -M1024`, with an explicit `--root` for a temporary
directory outside the package when needed. Keep every complete result. Unknown
imports/names, nonzero exits, timeouts and absent output are failures. Use fully
qualified names. Since `#check` also accepts a named `Prop`, confirm declaration
kind: the helper requires a theorem rather than a definition or axiom.

## Repair from actual diagnostics

| Symptom | Next action |
| --- | --- |
| Missing executable or wrong version | Inspect PATH, distribution and elan selection. Separate environment failure from proof validity. |
| Missing/stale imported `.olean` | Check module path/case and build it with the same toolchain. Do not install unrelated libraries. |
| Unknown constant/tactic | Search pinned sources/imports, then `#check` the exact name. Mathlib examples do not imply Mathlib is installed. |
| Type mismatch or implicit arguments | Use `#check @name`, `#print`, `trace_state`, or local `set_option pp.explicit true in` / `pp.all` on a minimal example. |
| `rw` cannot find its pattern | Inspect equality direction, definitional equality, coercions and dependent indices; try `change`, targeted `simpa only [...]`, or an intermediate equality. |
| Weak induction hypothesis | Generalize changing environment/substitution/index/accumulator; inspect recursors and every constructor for indexed/mutual relations. |
| Unhelpful/looping `simp` | Restrict to `simp only [...]` and inspect the resulting goal. Avoid global simp changes solely for one proof. |
| Heartbeats/recursion/memory exhausted | Reduce elaboration/search, reuse a focused lemma and locate the expensive step. Explain any bounded local limit increase; do not disable limits globally. |
| `sorryAx` or project axiom dependency | Trace and finish/remove the hole. Report incomplete proof; a clean grep does not suffice. |
| Stronger premise or smaller language needed | Return the actual obstruction/counterexample to the primary; do not rewrite the original goal silently. |

Use temporary `example`s for reproductions. Delete only your disposable outputs;
preserve useful unfinished work and record its status.

## Evidence and limits

Record input revision, toolchain/actual versions, commands/exits, checked module
coverage, theorem types, full axiom lists and material failed attempts. Hypotheses
are not kernel axioms: an empty list does not prove a supplied `LocalLaws`.

The helper allows `propext`, `Classical.choice`, `Quot.sound`; it rejects `sorryAx`,
project axioms and native-evaluation assumptions. Report the actual list. An
intentional extra-axiom study needs a clearly conditional manual audit and primary
adjudication, not a weakened helper. Builds and audits do not certify mathematical
meaning, full source coverage, Rust correspondence or hostile metaprograms. Use
the official validation reference for stronger checks when a concrete task calls
for them; do not introduce another proof framework incidentally.
