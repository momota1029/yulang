# Sprint R123 rev3 — method member annotations from authentic syntax

Revision 3; preserves rev1 SHA-256
`8c53212ddac7596d2878ce6a3ee8a1c6830c6e3cec3daea566742b930d41f794` and
rev2 SHA-256 `83d6154c5b80a8f928bd7f81a719864f00360b7a447c8fa77196ed895c104387`. Baseline
`beb54cec76867035901c1d1a2b9ec02858c945d4` on `research/simple-sub-intrusion`.
Status: CANDIDATE pending narrow delta review and Luna's explicit grant. Any
repair creates a sequential revision.

## Goal and bounded outcome

Advance method/role breadth with a source-owned proof and executable syntax
observation, while retaining depth and the six separate effect-hygiene fronts.
This packet establishes how an original implementation member's ordered formal
occurrences and optional own annotation occur in authentic parsed syntax and
are indexed by the existing `ShadowArtifact` source projection. It applies that
fact only to R119's member-annotation input. It does not establish executable
member admission, role-target selection, inferred type, method call execution,
M/T/A closure, or R85 adoption.

Use the exact R100 `SecondInt` role signature unchanged in three independently
parsed source artifacts. The implementation headers are:

```yu
my second self selected = selected
my second self (selected:int) = selected
my second self (selected:[] int) = selected
```

The cases distinguish absent annotation, ordinary `int`, and explicit empty
outer effect row. For each original parse, derive and test:

1. The exact member `BindingStatement` is a descendant of the original
   `ImplDeclaration`, and both belong to that parse's authentic source-key
   domain.
2. The target pattern retains binder order `second`, `self`, `selected`.
   The first two binders have no own type annotation; only `selected` has an
   annotation in the latter two cases.
3. The body `selected` is a distinct original occurrence from the formal and
   both map to distinct retained source positions. The explicit empty row is
   represented under that formal's own `PatternTypeAnnotation`; it is not
   absent and is not copied from the role signature.
4. `pending_role_impl_sources` and
   `with_associated_method_role_sources` continue to retain/associate the
   original enclosing role and impl declarations. State exactly which binder
   annotation facts those declaration-level APIs do not themselves return.

The proof traces parser constructors and `ShadowArtifact` source-key/index
constructors with explicit field correspondence. It identifies the exact
`module.rs`/`local_source.rs` admission boundary that still rejects or does not
construct executable role implementation members. No same-spelling identity
join, cross-parse opaque-ID equality, parser association as semantic selection,
or signature-derived executable role is permitted.

Falsifiers: any source fails ordinary parsing; a binder order changes; an own
annotation is attached to the wrong binder, signature or body; absent and
explicit-empty annotation collapse; a member loses original impl ancestry or
source ownership; formal/body positions alias; or the test requires production
parser/HIR changes or weakened expectations.

## Exact input sources

The common role/signature and answer context is the R100 source. Each source is
UTF-8, has no final LF, and is independently parsed. The implementation member
line varies as shown above.

| Case | Bytes | SHA-256 |
| --- | ---: | --- |
| absent annotation (`selected`) | 148 | `fb54857e70924c178842692d7cce1a9c35b7c2a55bceab78710889b913d7dfcb` |
| ordinary annotation (`(selected:int)`) | 154 | `9785e53f0ac8782dfa8369e844054f0e18234b92973ddde01c6b9b236cde63cd` |
| explicit empty effect (`(selected:[] int)`) | 157 | `335126c188f068f2682a94b5e0bf7b81687ec453b53ca62fedec4bdb9f760060` |

Expected outcome is a structural syntax/source-index assertion only. Do not lower
the impl as an executable member, call candidate solving, or run the playground.
R118/R120/R121/R122 remain the separately recorded ordinary/effectful public
execution path; this packet does not claim method execution.

## Authority and frozen dependencies

Charter §21 is the source-role authority. R119's conditional proof is used only
to locate its unsupplied own-annotation/member-source premise. R85 remains
Draft and unadopted. The user goal remains broad: all six effect fronts continue
OPEN and rotate; method syntax/role gets this source-correspondence slice; the
runnable surface remains an early observable for accepted ordinary/effectful
programs.

Pinned direct inputs (SHA-256):

```text
notes/design/2026-09-29-scc-intrusion-redesign-charter.md 547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed
notes/theory/2026-10-19-r119-member-producer-feasibility.md 8f5ac5abe7098d384c57f48e2d73b95c01aba4d3aca8c73c43a2a33d29ef4e7d
tasks/agent-loop/inbox/20261019-r119-proof.md 66843ab0eefe13f067d28414a4a6d59c736dab05d1790a94c03e273e0f3bbd85
tasks/agent-loop/sprints/method-role-producer-feasibility-20261019-r119-rev2.md 6639951a68a8248c705e5df8c954488ae782e8ffb0fbf8639fb821c4326bed58
crates/yu-hir/src/lib.rs 8f6e2b688418dbdb4e2c551cbd9b7b58c809623d492f2da6f7d29cc64189d8d8
crates/yu-hir/Cargo.toml a97f52fc6b9e577f23be4160ecdda9693bec8fe48c626d0e9b7c0e3b0c6fe8d1
crates/yu-hir/src/tests/shadow_method_role_source.rs ea90e8ef445aae1155e28e10356068dfaecb8b2bc430d5bf6f18094acee21e1a
crates/yu-hir/src/shadow.rs 9f7a80055076a01cbd99a3eb9c5bc8c3f0db512f2e84032a53af0eacdad2375b
crates/yu-hir/src/module.rs 153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907
crates/yu-hir/src/module/local_source.rs 3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786
crates/yu-hir/src/source_identity.rs 7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3
crates/yu-syntax/src/pattern/mod.rs 1b608422c93ce0f6947125a9b1ea88314a48b3a5e45030ed23e5154492ad7883
crates/yu-syntax/src/pattern/delimited.rs 9da9ec948775b438a85ca3f27c2805254a4f4171caddb54cabe44e563d017029
crates/yu-syntax/src/type_expr/mod.rs 2e08a49960cd4010ba39641ae509afb7cf59711c1464d3349f5f6db590ebf01f
crates/yu-syntax/src/type_expr/delimited.rs db6335a8f6c95bafb72d096fe241201202938c5869fb89a5e3c43758021651b6
crates/yu-syntax/src/declaration/impl_decl.rs 026edcb3e6d3c9f2214be8b9fa9fd510378b64152de55673c18cb93373f62066
crates/yu-syntax/src/declaration/impl_tail.rs 085fd4d0aac3735d9ac61a75a0a7b363a83b2a4bd0e78954a6908144e8853c24
crates/yu-syntax/src/statement.rs fe8ba4e144b0c3ea5c8f451dddea42f718e9c3087aa77bb81447c61a9d213797
crates/yu-syntax/src/declaration/mod.rs cf1067280be3974a5702b18f47ac02cf824c9d8cf971c1bdbc1b143676fc5c71
crates/yu-syntax/src/declaration/binding.rs eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544
crates/yu-syntax/src/declaration/role_decl.rs 0ec972a3acc036764a9d1407e292a4c676a24beb4cd0b5c3348c093cf3cf8634
```

The parser owner chain is pinned through `impl_tail` → braced statement and
`BindingStatement` construction, and through parenthesized formal and type-row
construction. These are source-construction owners only; role target resolution
and executable member admission are outside this trace. No unlisted input or
code write is implied. Any pinned drift returns to Luna before producer writes.

## Lanes, review and one bounded command

After CLEAN rev3 delta review and Luna's explicit grant:

- Proof `/root/r118_proof_lane`, Sol/high, cap 420 seconds. Writes only
  `notes/theory/2026-10-19-r123-method-annotation-source.md` and
  `tasks/agent-loop/inbox/20261019-r123-proof.md`. Inspect only this contract
  and pinned inputs; no executable commands, Git, or code/test edits.
- Surface test `/root/r118_implementation_lane`, Luna/high, cap 300 seconds.
  Writes only `crates/yu-hir/src/tests/shadow_method_role_source.rs` by
  appending one separate structural test, plus
  `tasks/agent-loop/inbox/20261019-r123-implementation.md`. Preserve all
  existing test bytes and expected outputs. No production edits, CLI behavior,
  method execution, source-inference change, formatter, Git or retry. Read-only
  inspection is limited to this contract and its pinned inputs.
- After both lanes stop, fresh compiler/source, spec/authority and regression
  review the proof and test. No author self-certifies. Repair only in a
  sequential revision with exact delta review.
- Once all three reviews are CLEAN, Luna runs exactly once:

```sh
CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-hir --lib tests::shadow_method_role_source::member_annotations_stay_on_their_original_formal -- --exact --nocapture
```

No alternate build, broad suite, test retry or expectation repair. A failed
command remains an open result. Verification is the one targeted `yu-hir` test;
it proves only the assertions it runs.

Total ceiling: 1,500 seconds (inventory 180, pre-spec 120, proof 420,
implementation 300, reviews 240, command 120, closeout 120); Astra 0. Preserve
all inherited UNKNOWN identities, quarantined board lease, and unrelated frozen
leases. No capacity is reclaimed.

## Parent application and next breadth step

A successful packet refines R119's own-annotation/source-capture premise for
three exact original parses. It does not establish the authentic executable
member owner, role-target join, ordinary candidate admission, runtime
publication, method M/T/A, or any parent closure. The next method step remains
behind its own missing producer/adoption gates. Continue rotating effect
hygiene across distinct fronts and preserve ordinary/effectful runnable
observations as an early surface.
