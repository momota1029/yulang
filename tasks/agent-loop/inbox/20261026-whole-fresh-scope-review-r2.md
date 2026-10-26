# WHOLE-FRESH-SCOPE-20261026 / independent review r2

Verdict: **ACCEPT at the stated successful ID-allocation/content-algebra scope.**
No blocking or major finding. Original full Effect hygiene and whole-language
soundness/principality/termination remain **OPEN**.

Reviewer: `/root/principality_source_r2`, a nonauthor of all four reviewed
allocation-lane artifacts. The separately authored source-principality packet
was frozen before this review began. Root remains sole author/integrator of
the allocation lane. This receipt does not review or certify the reviewer's
own source-principality packet.

## Frozen inputs and authority

Reviewed the exact root-assigned proof, audit, paired note and producer
handoff, the sole local mathematical import, and the actual native producer
and consumers. Read `.codex/agents/lean-prover.toml`, the relevant proof-skill
instructions and governing review rules. Root granted only this receipt path
as a repository write lease. No reviewed source, note, handoff, compiler file,
configuration, shared status or root import was edited.

| Reviewed input | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/NativeFreshScopeTransport.lean` | `1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5` |
| `notes/theory/lean/AuditFreshScopeTransport.lean` | `44e6618a59bba54411d4f5b9c75bca5458ae364914c410d5bd357315da3d9e80` |
| `notes/theory/2026-10-26-native-fresh-scope-transport.md` | `75e0a1e999cb23ff0cd8380f6cc7d1a175b6b76b8f0bec7bb81d7ea63c2aa831` |
| `tasks/agent-loop/inbox/20261026-whole-fresh-scope-r2.md` | `698ef44525d5e38b60e2ca8dd407f5fbcd1b3dfd339ae5aff4b3e84a840e5cb5` |
| `notes/theory/lean/YulangClosure/NativeScopeTransformer.lean` | `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6` |
| `crates/yu-solver/src/candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/candidate_scope.rs` | `9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `e62c909702ea210955e7d4b1c5d19991a1997a96990f70eb398f3044a479b56d` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |

All eleven hashes were independently rechecked after the three checker
commands and remained unchanged. The disjoint concurrent `ff12ce504`
integration does not enter this dependency component.

## Mathematical and native review

The result removes a real premise from the existing renaming theorem. It
constructs the native fresh map's injection on every old inventory ID instead
of asking a caller to supply global injection or collision freedom. The
output is actual evaluation commutation for those maps, with derived validity
at the enlarged inventory counts.

`ScopeInventory::fresh` reads each old scope/input key, allocates the current
respective vector length, appends a new slot and uses `HashMap::insert` for the
old key. Thus the projected recurrence is exactly `allocate`: increment the
counter and overwrite that key's image. `candidate_scheme.rs` consumes the
maps through `.get(&id).copied().unwrap_or(id)`. Initial identity plus the
ordered overwrite recurrence matches this successful ID projection. Scope
and input-route inventories are independent counters. Region-parent edges,
origin payloads, allocation failures, integer conversions and execution of
the Rust loops are explicitly outside the Lean projection.

Repeated enumeration is represented rather than ruled out by `Nodup`.
`fresh 2 [0,0]` has final count 4 and images `0 -> 3`, `1 -> 1`. The invariant
survives both overwrites. The proof also permits keys outside the old domain;
this strengthens the mathematical statement but is not represented as an
assertion that an invalid native inventory can execute successfully.

The constructed global injection is a proof-only extension. At each update,
composing the old extension with the transposition of `p(key)` and the fresh
counter preserves injection. On an old key distinct from the updated key,
old-domain injection excludes `p(key)` and the established upper bound excludes
the fresh counter. Agreement with the actual overwrite map therefore holds
through every prefix. The proof never replaces native lookup-or-identity
semantics outside the old domain. The checked explicit counterexample
`native_map_not_globally_injective` correctly records that copying 0 at count
2 maps both 0 and the out-of-inventory number 2 to 2.

The premises of `fresh_evaluate` are materially adequate and explicit:
`TransformerValid` covers every scope key, stamped tag and missing-guard tag;
`StateValid` covers every incoming protection and input tag. They refer to the
complete old inventories, including external names absent from the copied
support. `evaluate_valid` derives the corresponding output bounds, so all
three uses of native/ghost map agreement (transformer, incoming state and
evaluated state) have a proved support justification. Applying the imported
`evaluate_rename` and rewriting those three equalities proves the advertised
commutation under the actual native maps. There is no hidden supplied
commutation, injection or output-safety premise.

`fresh_evaluate_and_reuse` additionally supplies validity for the renamed
transformer and evaluated renamed state at the enlarged counts. This enables
another application when its next inputs are available; it is not a theorem
about whole inference termination or existence of all future source witnesses.
The external-protection example is relevant: releasing copied local scope 0
does not remove uncopied old protection 1. Native `ScopeTransformer::remap`
checks collision freedom on its collected finite support; this theorem's
coverage of incoming old state is the additional fact needed for content
naturality. Neither finite-support checking alone nor equality of sorted byte
representations is silently substituted for that fact.

## Independent checker and complete theorem audit

Created `/workspace/scratch/e3678bef96db/fresh-scope-review-r2` from the exact
two Lean modules, committed audit and three configuration files, with a new
isolated `.lake` cache. No producer/shared generated artifacts were copied.
Used installed pinned Lake
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`, Lean
4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), Lake
`5.0.0-src+eb6cafb`. Commands ran serially with `LEAN_NUM_THREADS=1`, project
`moreLeanArgs = ["-j1", "-M1024"]`, and a 120-second bound per invocation.

| Independent command | Result |
| --- | --- |
| `lake build +YulangClosure.NativeScopeTransformer` | Exit 0; dependency rebuilt, 2 jobs. |
| `lake build +YulangClosure.NativeFreshScopeTransport` | Exit 0; target rebuilt, 3 jobs. |
| `lake env lean -j1 -M1024 AuditFreshScopeTransport.lean` | Exit 0; all 50 originating theorem constants audited. |

The audit's selection is by originating module, not a public-name list. It
includes private/generated theorem constants, rejects originating project
axioms, prints each complete type and axiom list, and requires ten named
public roots. I independently parsed the resulting output and verified 50
unique, balanced begin/end blocks in matching order, 50 axiom records, all
standard axiom sets, no errors/warnings and no `sorryAx`. The audit includes
two private theorem names and generated equation/injectivity helpers. Exact
axiom distribution:

| Complete axiom set | Theorem count |
| --- | ---: |
| empty | 17 |
| `propext` | 13 |
| `propext`, `Quot.sound` | 16 |
| `propext`, `Classical.choice`, `Quot.sound` | 4 |

Full independently reproduced types and axiom lists are retained in
`evidence/03-audit.log`; `evidence/independent-census.json` preserves each
name, exact type/axiom output and parsed axiom list. The committed audit is
the durable reproducer. These are fresh checks of the frozen bytes, not an
acceptance of the author's reported output alone.

| Independent scratch evidence, relative to review directory | SHA-256 |
| --- | --- |
| `evidence/input-hashes.json` | `8392391379774199bc6826d59e6c82734d9a6aa73bfa2e6e203c5eea6c5f4d0b` |
| `evidence/01-dependency.log` | `a5ee07efd563df4211cd8fd9000b6d3a70d5398baada660125d55a7de735a738` |
| `evidence/02-module.log` | `71d6763904c9791cf0482385ed963b587e2a53503344127dfef4bc9c621ea5e1` |
| `evidence/03-audit.log` | `6f8943b4703760c4d79880927ff5a817dbc5dbba167e4217bde43ca84bbf16e1` |
| `evidence/independent-census.json` | `9b32c3b9900ba136e6f2f5a72577d5dc4d8967b3b44790e1898b9a557d9b7aaa` |

## Parent application and stopping boundary

Accept the construction of actual allocation maps, old-domain injection,
copied/fixed separation, content-evaluation commutation and next-use validity
under the two explicit support-validity premises. This is a useful original
fresh-name obligation discharged by concrete construction.

The first additional parent owner is the source/native inventory invariant:
derive `TransformerValid` and `StateValid` for every relevant original source
route at the actual old counts, with the same native enumeration and map.
Authenticated region ownership, source-origin payload transport, receiver and
receipt authority, and successful fallible Rust execution still require
their separate constructions. Full original Effect semantics and the
original whole theorems are not closed by this receipt. The frozen proof,
note and producer handoff state these limits consistently.

Review used three of six permitted focused checks, one Lean process at a
time, within the twelve-minute packet. No additional broad tests, children,
Git operations or shared-cache changes. All review processes have exited.
Only this review receipt and the isolated scratch evidence were written;
**review writes stopped**.
