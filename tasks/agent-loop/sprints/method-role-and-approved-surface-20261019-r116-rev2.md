# Sprint R116 — method/role bridge and approved surface execution

Status: CANDIDATE pending independent pre-spec review and Luna's exact lease grant.
Branch: `research/simple-sub-intrusion`; baseline: current R114-closed workspace.
Contract revision: 2.

Revision 2 corrects only three truncated/transposed dependency hashes found in pre-spec review; rev1 is preserved byte-for-byte.

## Original outcome and success evidence

Original goal: proof-backed type inference/evaluator with sustained breadth across
all six effect-hygiene fronts, proof-backed progress on method syntax/roles, and
early ordinary/effectful source execution. This sprint advances two bounded
outcomes without narrowing that parent goal.

Parent method gate: R100-P2-MEMBER, OPEN. The source domain is the exact R100
role/member fixture below. R100/R108 establish its original syntax occurrences;
R112 establishes that the production path currently maps the implementation
member to `UnsupportedItem` / `HirItem::Error`. R85 remains Draft/unadopted.
The proof outcome is a reusable, source-corresponding callable/role consumer
bridge with the missing member producer stated as a premise. It must not close
P2 or claim method execution.

Surface outcome: add a test-only public stdin CLI observation for one existing
ordinary callable and one existing unambiguous effectful source. Each must exit
successfully, write exactly `7\n` to stdout, and leave stderr empty. This records
current execution behavior; it does not prove general effect hygiene.

Method fixture, exactly 148 bytes with LF separators and no final LF, SHA-256
`fb54857e70924c178842692d7cce1a9c35b7c2a55bceab78710889b913d7dfcb`:

```yu
role SecondInt {
    my second: int -> int -> int
}
impl int: SecondInt {
    my second self selected = selected
}
my answer = SecondInt::second 1 2
```

Ordinary fixture, no final LF, SHA-256
`405b314bc639886d53499d733bc864c36027ee4a4e2f608b8be54ba5bc815e91`:

```yu
my id x = x
my main = id 7
```

Effectful fixture, no final LF, SHA-256
`f3b8173cc77bc99e0d50b0d3dac60de7702eaae2d8874fd875d5ade97a76a059`:

```yu
act io:
    our tick: int -> int
    our other: int -> int
my main = catch io::tick 7 { io::tick(p), _ -> p }
```

Success predicates: frozen proof states the exact conditional source-to-consumer
claim, applies R112's obstruction to R100-P2, and names each unresolved owner;
fresh independent reviews are CLEAN within those scopes. The test-only CLI
assertions check status success, stdout `b"7\n"`, and empty stderr for both
fixtures. One exact Cargo command runs only the new integration test file after
all outputs and reviews freeze.

## Authority, baseline and direct dependencies

No language semantic change is authorized. Reuse only current approved ordinary
callable, §21 role-erasure, and direct primitive-handler behavior. R85's positive
role-call contract and all R81/R84/R85 drafts remain unadopted. Duplicate-arm
priority is excluded because no approved duplicate-operation tie-break was
found. No expected output, production source, or diagnostic expectation changes.

The original R100 source/correspondence chain is bounded by these reviewed
artifacts: R100 proof `84a2aad8a63cad8673e2862e343eff27664c3daf003e97015a0289ba9569a971`;
R108 closeout `cfc0e6a45b329e099f1263833bc7c0160c8d0e034bf7596ffef1dc5da10666e8`;
R108 source test `ea90e8ef445aae1155e28e10356068dfaecb8b2bc430d5bf6f18094acee21e1a`;
R112 proof `9444f51d980c2a8d01aacb407e81c4d2278f88785d6486c0d0ec696da1e48ca9`;
R112 closeout `7f6e27c07a7a39424eed647a0250822075ec65233e06ead3677ceff3a6a6a6b1`;
R85 Draft `fee3feaec5e8873fe4f056df3a9ae9ca16c342f0a8b314c027a35719eedd4609`.

Fresh method/source owners: `crates/yu-hir/src/module.rs`
`c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a`;
`crates/yu-hir/src/module/local_source.rs`
`3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786`;
`crates/yu-solver/src/candidate_source.rs`
`66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c`;
`tools/inference-playground/src/runtime/program.rs`
`7bc27580711d3ef09044e324541904ef3388aca8e3b4f3a72437b1e04dc0210a`.
The method proof must also pin `crates/yu-hir/src/source_identity.rs`
`7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3`.

Fresh public execution owners (paths relative to `tools/inference-playground/`):
`tests/runtime.rs` `f8bebfd4eb4571e2814b83ea8473c035b429fe1eed4e07d26942a096143306ec`;
`tests/runtime_primitive.rs` `2b6a99690e43442c9553786c420c7108bcc8d8d9974391b4f677b73572bac3db`;
`src/lib.rs` `bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b`;
`src/main.rs` `75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100`;
`src/output.rs` `04e99c5bdb562a8edb8a7e17bdcc03f7b46eaca9d8e13b20216b4dcf3032a88a`;
`src/runtime/program.rs` `7bc27580711d3ef09044e324541904ef3388aca8e3b4f3a72437b1e04dc0210a`;
`src/runtime/machine.rs` `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46`;
`src/runtime/primitive.rs` `97485b9439357497aaf3f19555b1d87eef4aabc955b3a2815f23cf49a65c0153`;
`src/runtime/receiving.rs` `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9`;
`src/runtime/continuation.rs` `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3`;
`src/runtime/literal.rs` `2fff177a7ba0cabb4930251e1facc8f9be701ff3ec7baa695ce4c182fa1da35f`;
`Cargo.toml` `87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56`.

Fresh syntax/source identity owners: `crates/yu-syntax/src/full_parse.rs`
`24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8`;
`crates/yu-syntax/src/lib.rs` `18709b87b1b761374b5b81f90fcbf37d001fd7d981597e889aef05ad3f230f93`;
`crates/yu-syntax/src/header.rs` `cd3791144704226f67a05ae3d39aff9b42f4380073b3e9f9817951a493bce5ad`;
`crates/yu-syntax/src/cursor.rs` `f08aae49fcf048ad11890def7ef9cadab56825a63b8d87db44821a792fe9b142`;
`crates/yu-syntax/src/root_statement.rs` `c6d1dc49625d1687ff0dae8f6808f4c97c3f78398aae3bc061c44b6fc9661626`;
`crates/yu-hir/src/shadow.rs` `9f7a80055076a01cbd99a3eb9c5bc8c3f0db512f2e84032a53af0eacdad2375b`;
`crates/yu-hir/src/module/source_annotation.rs`
`b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f`;
`crates/yu-solver/src/shadow_apply.rs`
`5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb`;
`crates/yu-solver/src/lib.rs` `2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee`;
`crates/yu-solver/src/candidate_call.rs`
`e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479`;
`crates/yu-solver/src/candidate_effect.rs`
`6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0`;
`crates/yu-solver/src/candidate_scheme.rs`
`d4ff8a9e98eb667a5eb85aff9c0feec1f0227e86257bb56892493ac1d04a9278`;
`crates/yu-solver/src/candidate_value_graph.rs`
`8738c1b1699228b1a4dfd30af7e03d0afb100ca6124d23037c645246d888dc50`;
`crates/yu-solver/src/candidate_intrusion.rs`
`8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4`;
`crates/yu-solver/src/shadow_scc.rs`
`79e8ff5f459b6fc1389ecacb1da594814f9d9235297d62bc0501c2b3795b39c9`;
`crates/yu-solver/src/scc.rs` `8f3709ec9d52dc79767b6822eb4f671118a3f83814d2e9a9c748dfeac51e1f72`.

Effect authority/reuse evidence: `notes/theory/2026-10-16-runtime-primitive-event-visibility.md`
`7b27f8cf1d8024e249cc7d8a433c77438e3f59e5543cfc46a96a1af278eb3f56`;
`notes/progress/2026-10-16-playground-primitive-handlers.md`
`8d97124d8aafb618f116745754aecd123ac6f3d69f922b788f8d233a9c8f3ef6`.
Their historical tests/reviews are not fresh verification of today's runtime.

## Two continuing lanes

**Proof lane — Sol/high constructive source bridge.** Starting at the exact R100
fixture, consume R108's declaration/member occurrence identity and R112's
production obstruction. Prove only the reusable conditional bridge: given an
authentically admitted callable owner with ordered receiver/selected binders,
current LocalSource and candidate/runtime consumers preserve binder identity,
body lexical resolution, and each binder's own role annotation. Trace the actual
`plain_binding_header` gate and show why the production path does not currently
admit the member or its two-formal header. Apply the result to R100-P2 by naming
the missing authentic plan/root producer and R85 adoption as separate premises.
Do not re-prove R112, pretend the condition is met, claim method execution, or
close P2. Falsifiers include role copied from a signature, lost binder/source
identity, body resolving to a flattened or sibling name, or a consumer requiring
information not preserved by the proposed bridge.

**Implementation lane — Luna/high test-only public execution.** Add a dedicated
integration test with two cells using exactly the sources above. Invoke the
stdin CLI with `--run main --steps 1000 -` for ordinary and
`--run main --steps 10000 -` for effectful. Assert successful status, exact
`b"7\n"` stdout and empty stderr. No production edits. Stop if the exact source
fails ordinary preparation, the effect no longer selects its sole matching arm,
the run fails to complete, or output/diagnostic differs; preserve the result and
do not repair expectations.

Next related step within this contract: strengthen the source-to-consumer bridge
by resolving any exact missing owner within the pinned domain; improve the CLI
test only within its two frozen source cells. No new semantic decision, fixture,
source path, or goal may be added without Luna's versioned revision.

## Permissions and resources

Exact write leases:

- Proof: `notes/theory/2026-10-19-r116-method-role-callable-bridge.md`;
  `tasks/agent-loop/inbox/20261019-r116-proof.md`.
- Implementation: `tools/inference-playground/tests/cli_approved_surface.rs`;
  `tasks/agent-loop/inbox/20261019-r116-implementation.md`.
- Luna only: this contract, `tasks/agent-loop/current.json`, final closeout.

All other paths listed above are read-only pins. Workers cannot alter existing
tests, fixtures, expectations, specs, production code, or sibling outputs.
Authority/dependency/lease changes return to Luna. The method proof is
conditional research only; public tests are compatibility observations only.

Aggregate active-work cap: 1,800 seconds: inventory 180 (spent before this
freeze), proof 600, implementation 420, pre-spec and all post-output fresh
reviews 360 combined, one exact Cargo command 120, Luna closeout/state 120.
Actual runtime use is recorded from receipts; unknown use is never reclaimed.
Astra 0. At most two producer assignments run together. Three inherited UNKNOWN
workers retain reservations, so reviewers begin only after both producers stop.
One verification command, one Cargo process, `CARGO_BUILD_JOBS=2`, 120 seconds;
no probes/builds/formats or other commands by workers. No tests run before frozen
outputs and fresh required reviews are CLEAN.

The implementation command, owned only by Luna after review, is:

```sh
CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test cli_approved_surface -- --nocapture
```

## Frozen seams, review, and integration

Before edits, an isolated `spec_auditor` checks this contract's scope, exact
fixtures, no-new-semantics boundary, source authority and resource/lease gates.
After outputs freeze, assign a fresh compiler/source reviewer to the proof, a
fresh spec reviewer to method/role authority, and a regression reviewer to the
CLI cells. Authors/coauthors cannot review their own artifact. CLEAN means every
claimed correspondence and test assertion is tied to its pinned owner; no
reviewer may upgrade a conditional claim or CLI observation into P2 closure.

Use the typed-source-owner callable constructor relation only conditionally;
do not treat Draft R85 as authority. R100-P2-MEMBER, R113's suffix/runtime
payload, R114's distinct source identities/full permission correspondence, and
all six effect-hygiene parent fronts remain separately OPEN. R111's frozen
unverified file and all R109/R111/R113/R114 one-shot no-retry outcomes remain
intact. No production/cutover claim follows.

Continue the six-front rotation after this milestone: select an actually ready
effect-hygiene frontier under the approved authorities; do not reissue duplicate
priority as a language rule. This sprint's next material consultation trigger
is a semantic/dependency discovery, a counterexample, a resource boundary, an
integration seam, or this sprint's closeout.

Only Luna reviews/adjudicates, updates current state and the durable closeout,
stages explicit paths, and inspects the full outbound commit range. No commit or
push is authorized by this contract until a coherent reviewed integration
checkpoint exists.
