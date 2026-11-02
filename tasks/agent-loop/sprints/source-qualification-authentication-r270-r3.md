# R270 revision 3 — accepted-source qualification authentication

Status: versioned continuation after the R270-r2 read-authority stop. Preserve
revisions 1 and 2, their contracts and stop receipts. R270-r1 contract
`tasks/agent-loop/sprints/source-qualification-authentication-r270.md` is
SHA-256 `3f9b31127f698bc0a76c2371de63a3dc6a481c392d3af1b97c653f0812b891cc`;
its stop receipt is SHA-256
`3e918bace93f91f10bf680c84c66f540527b7e3a5772998b6adc49b8ae5a014f`. R270-r2
contract `tasks/agent-loop/sprints/source-qualification-authentication-r270-r2.md`
is SHA-256 `71742111d143af273c18f8b2722b2524321a3cad0d288609ecfa8ba263fff20c`;
its stop receipt is SHA-256
`330566d2c5e245ff5af38ba3b954d35d0e1e1190143bbb2cc5a81a49628f6877`. The
first two Sol grants are fully charged: 3,000 seconds total, with no refund or
reset. R269 grants also remain fully charged. Luna owns exact leases, fresh
live identity/active-work GO, review, adjudication, state and Git.

Branch `yulang3`; fixed source baseline
`8d646ac2ed171e13a529e25e035fc75f91678b0b`. The original goal remains full
inference/effects soundness → R70 → R71, with the original source domain,
quantifiers, Simple-sub A/B, independent satisfying assignments, shared
witnesses, source/native correspondence, F1/FK1 and foreign continuations.
Nothing in this packet changes those claims or grants semantic, production or
code-edit authority.

## Fixed outcome and evidence bar

Authenticate the concrete `LocalSource` fixture already present in
`candidate_source.rs::local_self_recursion_tests::hir`, tracing its exact input
through header discovery, full parsing, HIR lowering, resolved local names,
candidate collection, the complete Value-reference event inventory, successful
graph sealing and the actual qualification consumers. Determine whether that
accepted constructor path exhibits the R269 level-partition behavior under the
approved parent-copy SCC rule. This is a source-native conditional
characterization unless the full accepted path and an approved-clause defect
are established.

Success requires the exact source spelling; parse/header facts; HIR root and
LocalSource identities/resolutions; proof that collection retains that same
source carrier; all generated vertices, planning levels, raw edges and events;
the successful `seal` premises and result; every event's qualification value;
and the actual consumer calls. A Rust fixture spelling, test assertion,
`unwrap`, or unexecuted expected result is not itself evidence that the
constructor path succeeds. Do not run tests, builds, probes, Cargo, Lean, or
other executable checks. Use a source-level constructive trace and state each
inference. Falsifiers include parse/HIR/collection rejection, changed local
resolution or ownership, an incomplete/different event inventory, seal failure,
different qualification results, or a mistaken reading of the approved rule.

Even a verified qualification discrepancy does not by itself establish an
accepted-source violation, a source-qualified parent counterexample, `Need_D`,
the missing R268 incidence square, or universal R71 coverage. Keep the first
unproved implication and owner explicit. Preserve the no-narrowing rule.

## Fixed technical scope and source inputs

The inherited R269-r4 contract is
`tasks/agent-loop/sprints/slot-family-lineage-cover-r269-r4.md`, SHA-256
`a5f3bd1f3bc701ce75191ec234b72264d0dd9e73d7dfd31b88f0b8da0c6009ec`. It
retains the R268 contract's exact 14-source-body allowance, R255's 36-entry
hash-only/source manifest, original R70/R71 claims, R267-r6/R268 artifacts,
approved decisions, excluded paths and all prior boundaries. Do not open R269
r1, r2 or r3, or expand the inherited source set. Exact direct R269 artifacts:

- R269 theory `notes/theory/2026-11-02-slot-family-lineage-cover-r269-r4.md`,
  SHA-256 `30cc20db3c6d07a7616d40568019b7e6973e946cc579706885f29b9eb9ea6277`;
- R269 handoff `tasks/agent-loop/inbox/slot-family-lineage-cover-r269-r4.md`,
  SHA-256 `47c719197132f5dfed06465105aff2759222049284e7b220ba478dd3fe20679a`;
- R269 review `tasks/agent-loop/history/20261102-r269-r4-independent-review.md`,
  SHA-256 `75dde4c88f1272dfbeab5a39d2cdfbff119bfe69e7acf5126f8bc40e3239ffc7`.

R270-r1 added 41 exact parser paths to R268's 14 inherited source-body files;
r2 added `operator_compilation.rs`. Revision 3 preserves all 42 paths and adds
only ten declaration/for-selector owners required by the concrete `my`
classification route, each pinned before resumed source-body reads and
rechecked at freeze. No tests or unrelated syntax modules are included:

| Path | SHA-256 |
|---|---|
| `crates/yu-syntax/src/lib.rs` | `770a4af4a5832b3210050b4fc5513545569b0ca4718597f67434a714f76f301d` |
| `crates/yu-syntax/src/full_parse.rs` | `dd92603f8f5549b8b3f6e45ab6cb39b6598480b7f1cda7897e27b5113107db93` |
| `crates/yu-syntax/src/header.rs` | `cd3791144704226f67a05ae3d39aff9b42f4380073b3e9f9817951a493bce5ad` |
| `crates/yu-syntax/src/cursor.rs` | `f08aae49fcf048ad11890def7ef9cadab56825a63b8d87db44821a792fe9b142` |
| `crates/yu-syntax/src/root_statement.rs` | `c6d1dc49625d1687ff0dae8f6808f4c97c3f78398aae3bc061c44b6fc9661626` |
| `crates/yu-syntax/src/statement.rs` | `2370423ffef9869032da275a12e6d4a96deb9b1bf43ea098320d78ca6fc45bfd` |
| `crates/yu-syntax/src/sequence.rs` | `1a68331e5d16d46471545e673226541dc848123d1c3e286260359cecf41adcd2` |
| `crates/yu-syntax/src/handoff.rs` | `8ca2c50ae263986423eaf0f43e1a94de9fdf432366698118d6de75feb854d762` |
| `crates/yu-syntax/src/ambient_claim.rs` | `e46fdf1858094fde5535364ebc78f6f0a4997e15ac968a4edf06da9b434bce9f` |
| `crates/yu-syntax/src/syntax_kind.rs` | `fc0cde7e3347b65d7641a589ee02cdc1da6b7fba3fed07cc7d378df20a7bb6a3` |
| `crates/yu-syntax/src/operator_table.rs` | `18a5e54ba38df0c9f923f136cb16652fb910dafbecc6fdc6c146d034fcb43014` |
| `crates/yu-syntax/src/syntax_environment.rs` | `fdafdb177c8e2db7a44d66a8d9bc0c1905cc0a22da6457e470a165ca2501c5d7` |
| `crates/yu-syntax/src/operator_compilation.rs` | `5a13e0b62979ec02c265f9e7f427b772035b395eb661e37f16de6a4f5b04de87` |
| `crates/yu-syntax/src/lexical/mod.rs` | `0f3109a348c48747bd75d46de8afcbf40863c94c10a5bef8c768b6a0a8661c07` |
| `crates/yu-syntax/src/lexical/current_item.rs` | `41efcce2b737a0362484e854a8549bda5f7bf0d2b911499553f1e449c6782a84` |
| `crates/yu-syntax/src/lexical/expression_item.rs` | `aa291aaab95b633d4b6f61aac237846281d69fa1a9c88b4029a21b5c0de8d350` |
| `crates/yu-syntax/src/lexical/item.rs` | `b264b63e84fc73a3ef7dba355864be84d756fab287fa3734eaf37992e3655db7` |
| `crates/yu-syntax/src/lexical/lexer.rs` | `620f91d99cd4b0bd320315398466cbbec2ed625b8a8ebc6ba07f84d0c97524d1` |
| `crates/yu-syntax/src/lexical/observation.rs` | `730e65947f889ef07014aa003eb846012d5cec6ae1434f77edf1cbd0e7096641` |
| `crates/yu-syntax/src/lexical/stops.rs` | `edcf37bbe061c0966ba786d9090361c6c3befdbe3f99aa79f29271bd5230bf5b` |
| `crates/yu-syntax/src/lexical/trivia.rs` | `887f1499fe63d870a70777626f0357c502a356d106c623d9a79e3596a17aba19` |
| `crates/yu-syntax/src/lexical/opaque_region.rs` | `ef905c9d5301e3cbea0634efc9c2ab9844b7de0b2862cfd47c0b22413ec00e4a` |
| `crates/yu-syntax/src/lexical/operator_scan.rs` | `610d3996a5bf173633de24e6a4b205340125f6e1c24bbafc292dfa15cbd076ba` |
| `crates/yu-syntax/src/lexical/position.rs` | `0ca1b4acb27904c28e62b950ae04ee114d992cdffa27accf6098793e73cbb766` |
| `crates/yu-syntax/src/lexical/yumark.rs` | `21738dda1f64d27273983246f0f5d22b0a6da0025209132238a91154c38fcf75` |
| `crates/yu-syntax/src/declaration/mod.rs` | `cf1067280be3974a5702b18f47ac02cf824c9d8cf971c1bdbc1b143676fc5c71` |
| `crates/yu-syntax/src/declaration/binding.rs` | `a9b0602fccc90d49f294706092c85b373b06869b678cdd4c25efd429d0374387` |
| `crates/yu-syntax/src/declaration/operator_header.rs` | `021e79529445054e5d54bfccf93d2287e94221a99e1554fbd7c715cb0706edbd` |
| `crates/yu-syntax/src/declaration/use_decl.rs` | `1f7df7e6101cc398056b610536c723271ed108aeecafe38eb09b8dc62cc45fc0` |
| `crates/yu-syntax/src/declaration/mod_decl.rs` | `6adf9945e096ee027886a05857f6c187134a5331e4ab37493d95304255760741` |
| `crates/yu-syntax/src/declaration/struct_decl.rs` | `7b36b18fc6ef3e149e756a37b0f74719a5ae40be195c6986efe2c44d57fa3de4` |
| `crates/yu-syntax/src/declaration/type_decl.rs` | `e01d1f30c1dca051fb590a9fddac1686621fc789444f9cb053dcc269e746c134` |
| `crates/yu-syntax/src/declaration/enum_decl.rs` | `9c717571426927a3619330b372ec721d1f660377ecd45c6f0ab7f6cf9ed3ec31` |
| `crates/yu-syntax/src/declaration/error_decl.rs` | `56eace59a91d156f59d27a348e98ea353e9cc96595a49fc0f7e58d36dcd7a028` |
| `crates/yu-syntax/src/declaration/role_decl.rs` | `0ec972a3acc036764a9d1407e292a4c676a24beb4cd0b5c3348c093cf3cf8634` |
| `crates/yu-syntax/src/declaration/impl_decl.rs` | `026edcb3e6d3c9f2214be8b9fa9fd510378b64152de55673c18cb93373f62066` |
| `crates/yu-syntax/src/declaration/cast_decl.rs` | `c4907b91f0cbe72606597fb6ef1918c757e9f78621a2c4c68bf0632fe629a0ed` |
| `crates/yu-syntax/src/declaration/act_decl.rs` | `a8582ecc71c37ec4f531ca0441901053e132ec9a2325681496b88e5f695dd9fd` |
| `crates/yu-syntax/src/expression/for_decl.rs` | `fd50ab8b049addc3c366a0eda5519fd38bda31a2b518ba139d90ad24949714ec` |
| `crates/yu-syntax/src/expression/mod.rs` | `05d874dd4c2874eb7b24038467c8a74b22fa6f7821a3980f3348683ad02743f1` |
| `crates/yu-syntax/src/expression/delimited.rs` | `e65c4d500ce0878faf13f1a8d31da816e5db9b6af4690b505c8875d27b700f95` |
| `crates/yu-syntax/src/expression/lambda.rs` | `56357346a0f59330a202936f88337af1490b1839f339dc113b0b35f2d8c777b0` |
| `crates/yu-syntax/src/expression/required_operand.rs` | `9dc7455b0e97e3d57194126d33d330bd85aaba123d43015894728598d6337714` |
| `crates/yu-syntax/src/expression/operator_chain.rs` | `0929f43e65682766543be6aeb0db2dded40b85fdd470240188da66d89757700b` |
| `crates/yu-syntax/src/expression/tails/mod.rs` | `a3ee107c996e028765570c7ba89b12857cd072eddc988b5b4c8eb66ffc753b8c` |
| `crates/yu-syntax/src/expression/tails/with_body.rs` | `4fdf57e9a19b8897871d666ab5ec8adaa7c9219fc775d6c54cddc4555f61c058` |
| `crates/yu-syntax/src/expression/tails/delimited_tail.rs` | `349fe2335e04a68da7d07803f2dd2eb185887d07bf8c9475ba09af089a76a2cf` |
| `crates/yu-syntax/src/expression/tails/colon.rs` | `df37d747f396e8b27c53b6785e4a26f5210162b14e65b4648d449495bf8f5982` |
| `crates/yu-syntax/src/pattern/mod.rs` | `f86fb57da7412376defd7ad15a3cd5671c0708bed55016223a7a038d8c7d303f` |
| `crates/yu-syntax/src/pattern/delimited.rs` | `9da9ec948775b438a85ca3f27c2805254a4f4171caddb54cabe44e563d017029` |
| `crates/yu-syntax/src/cursor/recovery.rs` | `1e216cf585e5548abc178fab0ebc90b6aef409b22c507dda3e08a52399a45f6e` |
| `crates/yu-syntax/src/cursor/recovery/emit.rs` | `d9866a13f28e1acb1e80f927b64baa4d97f51a5e7934ab5c1d870ea757e497a5` |

Luna's bounded locator pass traced the constructor prerequisites and the
concrete header/full-parse classifier calls. `SyntaxEnvironment::empty()`
supplies an empty `OperatorTable`. The fixture begins with `my outer`;
`header.rs::operator_selected` routes the prefix through
`binding_statement_selected_lexical`, which calls use/mod/struct/type selection
and then its binding follower. For `my outer =`, that binding selection
makes `header.rs::operator_selected` return false, so header discovery stops at
the first non-header with empty imports and operator facts.
`operator_compilation.rs::effective_full_parse_operators`
iterates the empty imported entries and empty local-header slice; the pinned
`OperatorTableBuilder::build` starts from `OperatorTable::empty`, iterates an
empty map, and returns that empty table.

The full parser's pinned
`statement.rs::classify_statement_item_lexical` checks
struct/enum/error/mod/type/role/impl/cast/act, `for_statement_selected`, and
then binding. R270-r3 pins each exact selector owner above. The inspected
selector bodies consume already pinned lexical `observation.rs`/`lexer.rs`
owners and do not call another declaration source owner on this `my outer`
path. This closes only the read-authority route to the listed constructors;
it proves neither a successful parse nor HIR/collection/seal/qualification
success. Sol must independently verify selector results and continue the
source-level construction. Do not open any further source path; if the fixed
proof requires another owner, stop and report its exact path and why before
reading it. This packet does not perform repository-wide searches.

## Operational read authority

Producer and reviewer first read only this contract and await Luna's exact
runtime identity comparison and explicit GO. After GO, follow R269-r4's
operational whitelist in its pinned order, verifying its direct pins and all
36 R255 manifest entries before source-body reads and again at freeze. The
whitelist contains AGENTS instructions, exact design/rule indexes and sources,
compact current state, current sprint skills, and role configuration. Read the
fresh `.codex/agents/compiler-referee.toml` only for review. Existing
applicability decisions and exclusions are inherited unchanged. The only new
technical reads are the exact syntax paths above; no operational reference may
expand that set. R270-r1's exact stop receipt is available as read-only history.
No Lean or Lean-only skill, question-board task, tests, builds,
probes, benchmarks, Cargo, scratch/cache output, code changes or Git.

## Sol proof lane

Resume the existing stopped registered `prover`, Sol/high, exact task name
`sol_r270_source_qualification_auth`, exact identity
`/root/sol_r270_source_qualification_auth`, no descendants. Require a fresh
active-work acknowledgement and explicit GO under the current session. This is
a separate new 1,500-second grant; the prior R270-r1 and r2 grants stay fully
charged at 3,000 seconds total. The proof trial belongs to Sol. Stages:

1. Derive the approved source/native requirement and R269 qualification
   question without changing original quantifiers or treating a local shape as
   the whole accepted domain.
2. Recheck the pinned empty syntax-environment/operator construction and
   complete selector route above, then construct the exact syntax/HIR path for
   the fixture and prove its local binding/name resolution identities.
   Establish the precise successful collection and graph-seal premises from
   source constructors; do not infer runtime success from the test's `unwrap`
   calls.
3. Enumerate every relevant Value vertex, birth/planning level, raw edge,
   association and consumer qualification call. Check competing source paths
   represented in this concrete HIR and apply the observed result to the
   approved clause and unchanged R71 edge. If the path cannot be established,
   freeze its first missing constructor fact and owner, without claiming
   absence, violation, counterexample or coverage.

Exclusive outputs:

- `notes/theory/2026-11-02-source-qualification-authentication-r270.md`;
- `tasks/agent-loop/inbox/source-qualification-authentication-r270.md`.

After immutable freeze, fresh independent `compiler_referee`, requested
gpt-6.1-sol/medium, exact task name `r270_source_qualification_review`, exact
identity `/root/r270_source_qualification_review`, no descendants, maximum
600 seconds. Luna records the review at
`tasks/agent-loop/history/20261102-r270-source-qualification-review.md`.
Reviewer challenges accepted-source authentication, exact owners/identities,
collection/seal success, completeness of event/consumer inventory, approved
rule interpretation, competing paths, overclaim and parent application.
Unchecked claims remain INCOMPLETE.

R270 cumulative allocation is exactly 6,000 seconds: original Sol grants 3,000
charged; original Luna readiness/integration 300 retained; fresh reviewer 600
reserved; new Sol grant 1,500; additional Luna corrective readiness/integration
allocations 600 across r2/r3. The new Sol grant is separate and does not reset
prior grants. Astra and descendants remain 0. No prior charge is refunded or
automatically renewed. Preserve every unknown worker/path quarantine and
capacity receipt. Implementation remains `NO_SAFE_CODE_SLICE`; no code edit is
authorized. Stop at any missing owner or grant bound; another authority stop
requires a new boundary decision. Consult the dispatcher at envelope
completion or a material source-authenticated finding requiring changed
authority, dependency or implementation admission.
