# R106: exact method/role source entry

Status: CANDIDATE, revision 1. Primary: Luna `/root`.

## Fixed finite outcome

Advance the unchanged R100 method/role source obligation by observing that the
exact R100 source reaches the published `RoleDeclaration` and
`ImplDeclaration` occurrences in one authentic `ParsedFile` and one retained
`ShadowArtifact`. Bind those declarations and the implementation member's
ordered syntax occurrences to the original parse keys and retained source
positions, then apply this finite source-entry evidence to R100's reviewed
constructor/consumer analysis to name the first missing executable binder
premise.

The exact source bytes are 148 bytes, SHA-256
`fb54857e70924c178842692d7cce1a9c35b7c2a55bceab78710889b913d7dfcb`; there is
no final LF:

```yu
role SecondInt {
    my second: int -> int -> int
}
impl int: SecondInt {
    my second self selected = selected
}
my answer = SecondInt::second 1 2
```

Add one test-only case named
`exact_role_impl_member_source_reaches_original_occurrences` to
`crates/yu-hir/src/tests/shadow_method_role_source.rs`. It must use one parsed
value for source-key lookup, retention and association. Establish the exact
RoleDeclaration/ImplDeclaration roots, the implementation member's `second`,
ordered `self` and `selected` pattern occurrences, and the distinct body
`selected` occurrence. Each checked node/key/position must belong to this same
parse and source; preserve exact source ranges and parent/child ownership where
the public test APIs expose them. Keep all existing assertions. No production
file changes.

This closes only the former exact-source-entry premise for this fixture. It
does not claim executable HirParameterIds, lexical binder resolution, body
checking, member selection, dispatch, ordinary Apply generation, candidate or
runtime admission, or evaluation result `2`. R100 P2/P3/P4 and the original
Simple-sub/evaluator theorem remain OPEN. R85 remains Draft and unadopted.

## Parent application and falsifier

R100 conditionally derives the nested implementation BindingStatement and its
ordered syntax pattern/body occurrences from the relevant syntax constructors,
but leaves `R100-ENTRY` open because it did not inspect/observe the exact root
dispatcher and published root. R106 supplies one observed exact-source entry
and same-parse retained-position/key correspondence. Apply that observation to
the R100 owner-local case analysis: the first missing executable-member
materialization remains at the HIR `plan_root`/`lower_plan` to LocalSource
boundary. R106 does not promote the constructor analysis into a universal
parser-completeness theorem.

Falsifiers: the exact source fails or publishes different declaration roots;
the association pairs roots from another parse; a checked pattern/body
occurrence has a different source spelling, range, parent order or parse key;
or a current complete consumer already emits the exact executable member
binding and body environment identified by R100.

## Exact output leases

Proof, Sol/high, 600 seconds:

- `notes/theory/2026-10-19-r106-method-source-entry.md`
- `tasks/agent-loop/inbox/20261019-r106-proof.md`

Test-only implementation, Luna/high, 360 seconds:

- `crates/yu-hir/src/tests/shadow_method_role_source.rs`
- `tasks/agent-loop/inbox/20261019-r106-implementation.md`

Fresh pre-edit spec review: `tasks/agent-loop/inbox/20261019-r106-spec-review.md`.
Fresh post-output spec review: same reviewer role, frozen result recorded at
`tasks/agent-loop/inbox/20261019-r106-post-spec-review.md`.
Fresh post-output compiler/source review:
`tasks/agent-loop/inbox/20261019-r106-compiler-review.md`.
Luna closeout: `notes/progress/2026-10-19-r106-method-source-entry.md`.

Reviewers have read-only access to the exact pins and frozen output paths. Each
producer may inspect only the exact pins. No test/build/compiler/runtime/CLI,
formatter, Git or generated/scratch file is authorized for a worker. Only Luna
may run the single command below after both post-output reviews are CLEAN.

## Frozen direct inputs

| Input | SHA-256 |
|---|---|
| R100 proof note | `84a2aad8a63cad8673e2862e343eff27664c3daf003e97015a0289ba9569a971` |
| R100 proof handoff | `1a692cb7f3c31e83bf60ee90763216ef3253f2c357747c9258eff16e2f8cec19` |
| R100 closeout | `6fefb70bf9c211e7cdb5a37a9d09706b8530f5aa7a3fa80575af6ea74ef3516b` |
| R95 closeout | `dfdf5272569db6c41e5b19f817b0f1cb39b35dac185fa2459edc7844d4b8cdf1` |
| `crates/yu-hir/src/lib.rs` | `8f6e2b688418dbdb4e2c551cbd9b7b58c809623d492f2da6f7d29cc64189d8d8` |
| `crates/yu-hir/src/tests/shadow_method_role_source.rs` (pre-edit) | `6d5c3fec7b4ca0d4618f4ad378f0ad5e8e0689b4897d406ab90d175ba78e6135` |
| `crates/yu-hir/src/shadow.rs` | `9f7a80055076a01cbd99a3eb9c5bc8c3f0db512f2e84032a53af0eacdad2375b` |
| `crates/yu-hir/src/source_identity.rs` | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` |
| `crates/yu-hir/src/module.rs` | `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a` |
| `crates/yu-hir/src/module/local_source.rs` | `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786` |
| `crates/yu-syntax/src/full_parse.rs` | `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8` |
| `crates/yu-syntax/src/declaration/impl_decl.rs` | `026edcb3e6d3c9f2214be8b9fa9fd510378b64152de55673c18cb93373f62066` |
| `crates/yu-syntax/src/declaration/impl_tail.rs` | `085fd4d0aac3735d9ac61a75a0a7b363a83b2a4bd0e78954a6908144e8853c24` |
| `crates/yu-syntax/src/declaration/role_decl.rs` | `0ec972a3acc036764a9d1407e292a4c676a24beb4cd0b5c3348c093cf3cf8634` |
| `crates/yu-syntax/src/declaration/binding.rs` | `eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544` |
| `crates/yu-syntax/src/pattern/mod.rs` | `1b608422c93ce0f6947125a9b1ea88314a48b3a5e45030ed23e5154492ad7883` |
| `crates/yu-syntax/src/statement.rs` | `fe8ba4e144b0c3ea5c8f451dddea42f718e9c3087aa77bb81447c61a9d213797` |
| `crates/yu-syntax/src/syntax_kind.rs` | `26d2a0ddbe1862c95c503420ded0b0d35217bee5ba9f350be9163c065c6b488d` |

R100's pinned `ShadowArtifact`/association owners and R95's reviewed bounded
source bridge are sufficient dependencies. Do not make full parser static
completeness or discovery of another parser dispatcher owner an execution
prerequisite; the direct source-entry observation is the scoped outcome. Any
new required owner beyond this list is a stop condition, not permission to
expand pins.

## One Luna-owned command

After frozen outputs and fresh CLEAN post-output spec/compiler-source reviews,
Luna may execute exactly once, without retry:

```sh
CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-hir --lib tests::shadow_method_role_source::exact_role_impl_member_source_reaches_original_occurrences -- --exact --nocapture
```

The command observes only this test. A failure ends the packet without repair.

## Resources, reviews and stop conditions

- Pre-edit spec review: 180 seconds.
- Proof: 600 seconds; R105's exhausted proof allocation is not transferable.
- Test-only implementation: 360 seconds.
- Fresh post-output spec review: included in the 180-second review allocation.
- Fresh compiler/source review: 240 seconds.
- Luna command: 120 seconds, exactly once.
- Closeout and integration: 300 seconds.
- Total cap: 1,800 seconds; Astra 0.

Preserve three inherited UNKNOWN worker identities, the quarantined board
lease, and legacy slot reservation. At most two producers run concurrently.
Stop on input hash drift, a source mismatch, missing owner beyond the pins,
review BLOCKING/MAJOR, command failure, budget exhaustion, or unknown writer.
Do not edit production source, alter expected output, adopt R85 semantics, or
claim method/role runtime execution.

## Breadth boundary

This sprint reduces one method/role source-entry premise while retaining the
six separate effect-hygiene fronts and the early runnable ordinary/effectful
surface in the parent goal. It does not reorder those fronts into an effect-only
sequence or treat this one proof as method/role closure. At R106 closeout,
choose the next bounded evidence slice across effect hygiene, method/role proof,
and runnable source execution according to the remaining parent obstruction.
