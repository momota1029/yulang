# R100: exact method/role member body to source consumer

Status: ACTIVE, revision 5; revision-1 pre-edit spec review CLEAN; revision-2 lifecycle and revision-4 wording delta reviews CLEAN; this revision adds delegated syntax-parser owners and the authoritative R85 P1–P4 locator after source inspection found those inputs necessary.
Primary: Luna `/root`.

Revision 5 adds exact read-only input pins for the delegated BindingStatement/Pattern/expression parser owners and the frozen R85 P1–P4 locator. Revision 4 remains preserved at `tasks/agent-loop/sprints/method-body-source-consumer-20261019-r100-rev4.md`; prior revisions remain preserved in the adjacent versioned files. Source fixture, semantic scope, outputs, budget and stop conditions are unchanged. Pre-edit review receipt: `tasks/agent-loop/inbox/20261019-r100-spec-review.md`; revision-2 delta receipt: `tasks/agent-loop/inbox/20261019-r100-spec-delta-review.md`; revision-4 delta receipt: `tasks/agent-loop/inbox/20261019-r100-spec-rev4-review.md`. The proof lane may inspect these added pins only after a CLEAN delta review of this revision.

## Fixed finite outcome

Advance the user's method/role proof direction by tracing this exact source
through authentic parser/source constructors and current consumers:

```yu
role SecondInt {
    my second: int -> int -> int
}
impl int: SecondInt {
    my second self selected = selected
}
my answer = SecondInt::second 1 2
```

Constructively establish which original declaration, member body, ordered
formal/binder occurrences, body name occurrence, and source positions are
retained; then identify the first consumer that does or does not create an
executable member binding/environment and ordinary receiver-first Apply path.
Apply useful results to R85 P2/P3/P4 and name the exact remaining premise.

This is source-constructor/consumer evidence only. R85's positive role-call
contract remains Draft and unadopted. Do not select method lookup, dispatch,
RoleId, diagnostics, typing, body checking, or runtime member semantics. Do not
claim `SecondInt::second 1 2` evaluates to `2`; do not use a standalone
same-spelled binding as a substitute for the exact implementation member.
Original Simple-sub/evaluator claims, quantifiers, A/B, F1/FK1, R50 and R85
adoption gates remain unchanged.

## Proof obligation

Trace the exact `RoleDeclaration` and `ImplDeclaration` source occurrences
through parser constructors, retained source positions, and the bounded
association bridge. For the `ImplDeclaration`, identify the actual syntax
nodes for `second`, `self`, `selected`, and the body `selected`, their ordered
parent/child ownership, source ranges/keys, and each existing consumer that
does or does not publish them. Separate:

1. parser/CST retention;
2. source occurrence association;
3. HIR/LocalSource executable member materialization;
4. ordinary generated constraints and receiver-first curried Apply;
5. candidate/runtime admission.

Do not infer a later layer from an earlier one. If the exact current path stops
before a layer, prove the missing constructor/consumer by inspecting its
complete owning branch and state the narrow missing premise. Use source
constructor induction/translation validation, not guessed parser output.
Falsifier: the member body is already lowered to authentic executable binders
and body environment, or an ordinary Apply/consumer already consumes the
exact qualified member through a separately proven path.

Proof outputs:

- `notes/theory/2026-10-19-r100-method-body-source-consumer.md`
- `tasks/agent-loop/inbox/20261019-r100-proof.md`

## Implementation assessment (no code authority)

The implementation lane receives only
`tasks/agent-loop/inbox/20261019-r100-implementation.md`. It must inspect at
least two exact owners from `crates/yu-hir/src/shadow.rs`,
`crates/yu-hir/src/module.rs`, `crates/yu-solver/src/candidate_source.rs`, and
`tools/inference-playground/src/runtime/program.rs`, compare them with R85's
open P2/P3/P4 requirements, and record either a source-evidence-only safe slice
or `NO_SAFE_ROLE_CODE_SLICE` with exact owner-local dependencies. No source,
test, build, CLI, or semantic edit is authorized. R85 remains unadopted, so an
implementation patch, new fixture expectation, or claim of runnable role
dispatch is out of scope.

R92's already verified ordinary/effectful CLI result `23` is the present
runnable surface baseline; do not rerun it or count it as new evidence.

## Dependencies and review

Direct frozen inputs:

| Input | SHA-256 |
|---|---|
| R85 positive contract (Draft) | `fee3feaec5e8873fe4f056df3a9ae9ca16c342f0a8b314c027a35719eedd4609` |
| R95 method/role source closeout | `dfdf5272569db6c41e5b19f817b0f1cb39b35dac185fa2459edc7844d4b8cdf1` |
| R93 associated-member source note | `6d3a4d0357f99fa9f1b6978bd66d6210409a6e95a1fe046a53239a09f82e012c` |
| `crates/yu-hir/src/shadow.rs` | `9f7a80055076a01cbd99a3eb9c5bc8c3f0db512f2e84032a53af0eacdad2375b` |
| `crates/yu-hir/src/module.rs` | `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a` |
| `crates/yu-hir/src/module/local_source.rs` | `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786` |
| `crates/yu-hir/src/lib.rs` | `8f6e2b688418dbdb4e2c551cbd9b7b58c809623d492f2da6f7d29cc64189d8d8` |
| `crates/yu-syntax/src/declaration/impl_tail.rs` | `085fd4d0aac3735d9ac61a75a0a7b363a83b2a4bd0e78954a6908144e8853c24` |
| `crates/yu-syntax/src/declaration/impl_decl.rs` | `026edcb3e6d3c9f2214be8b9fa9fd510378b64152de55673c18cb93373f62066` |
| `crates/yu-syntax/src/declaration/role_decl.rs` | `0ec972a3acc036764a9d1407e292a4c676a24beb4cd0b5c3348c093cf3cf8634` |
| `crates/yu-syntax/src/full_parse.rs` | `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8` |
| `crates/yu-syntax/src/statement.rs` | `fe8ba4e144b0c3ea5c8f451dddea42f718e9c3087aa77bb81447c61a9d213797` |
| `crates/yu-syntax/src/syntax_kind.rs` | `26d2a0ddbe1862c95c503420ded0b0d35217bee5ba9f350be9163c065c6b488d` |
| `crates/yu-hir/src/source_identity.rs` | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` |
| `crates/yu-solver/src/candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` |
| `tools/inference-playground/src/runtime/program.rs` | `484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11` |
| `crates/yu-syntax/src/declaration/binding.rs` | `eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544` |
| `crates/yu-syntax/src/pattern/mod.rs` | `1b608422c93ce0f6947125a9b1ea88314a48b3a5e45030ed23e5154492ad7883` |
| `crates/yu-syntax/src/expression/mod.rs` | `05d874dd4c2874eb7b24038467c8a74b22fa6f7821a3980f3348683ad02743f1` |
| `crates/yu-syntax/src/expression/lambda.rs` | `56357346a0f59330a202936f88337af1490b1839f339dc113b0b35f2d8c777b0` |
| `crates/yu-syntax/src/expression/operator_chain.rs` | `81db2aec4774f2cd1ddc12b64fd9206cf41cdf3eee00ed740676ffc6d7fc5669` |
| `crates/yu-syntax/src/lexical/expression_item.rs` | `c981a994a11c539256ef34382c4ae154395e5d438371db4959e914df58aa8c7c` |
| `crates/yu-syntax/src/type_expr/mod.rs` | `2e08a49960cd4010ba39641ae509afb7cf59711c1464d3349f5f6db590ebf01f` |
| `notes/theory/2026-10-19-r85-role-call-preservation.md` | `92d207aecb043c102409c543758213511c9843c9302e09fcc415c76fb6fea259` |
| `tasks/agent-loop/inbox/20261019-r85-proof.md` | `9aa0062e381a4fd83583d585857583a726b6e123ccbb11ad6bca2c6fa9886e4c` |
| `tasks/agent-loop/sprints/effect-hygiene-runnable-role-positive-20261019-r85.md` | `6bab1a76954829dee5c84e438dee66ebb3bac43b7ea7abb403485ae8bd51c62e` |

After frozen outputs, use a fresh read-only compiler/source reviewer and a
delta spec reviewer. Read-only inspection commands are authorized only for the frozen, pinned source and proof inputs: `cat`, `sed`, `rg`, `sha256sum`, and equivalent non-mutating text/hash inspection. No formatter, compiler, test, build, runtime CLI, generated output, or Git command is authorized. Inspection may not create files. All output writes remain restricted to each lane’s exact leased artifact paths.
Blocking/major review finding, dependency drift, mismatch of source owner, or
budget exhaustion ends the packet without repair.

## Leases, resources and stop

- Proof lane, Sol/high, cap 900 seconds: only the proof note and proof handoff.
- Implementation assessment lane, Luna/high, cap 360 seconds: only the one
  implementation handoff; no production/test/code changes.
- Spec review 180 seconds, independent compiler/source review 240 seconds,
  integration/closeout 180 seconds; total cap 1,860 seconds; Astra 0.
- Preserve the three inherited UNKNOWN identities and quarantined board path;
  admit no more than two production workers concurrently.
- Fresh pre-edit spec review precedes both lanes. Freeze exact artifact hashes;
  workers may run only the read-only inspection operations listed above; no worker runs Git or any other command. Only Luna owns `current.json` and Git.
- Next dispatcher trigger is R100 closeout, a source counterexample, or a
  material authority/dependency/lease change. The next allocation after this
  packet must rotate to another open hygiene front or a source-law-resolved
  runnable surface; do not auto-repeat receiver repair or effect-storage work.
