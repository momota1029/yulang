# R271 revision 2 — recursive local-package source manifest

Status: proposed continuation under the unchanged inference/effects soundness goal. R271-r1 stopped before `chasa_recover::In::token/with_str`; preserve the exact R271-r1 contract and stop receipt without rewriting either. R271-r1 contract SHA-256 `a657ae431d1cd28965c0320b67951c441b67398211e02999465dc272a6cda86a`; R271-r1 stop receipt SHA-256 `9ac1772de2f34fd38c7c474e55f1116f167c62158310ce4420d972db83caf0d4`. Its 1,800-second Sol grant remains charged, the prior 600-second Luna allocation remains retained, and its unissued 600-second reviewer allocation stays cancelled. R270's cumulative Sol 4,500 seconds remain separate and charged.

## Fixed parent and exact outcome

Unchanged parent: full inference/effects soundness → R70 → R71, original source domain and quantifiers, Simple-sub A/B, independent satisfying assignments, shared witnesses, source/native correspondence, F1/FK1 and foreign continuations. This packet continues authentication of the concrete fixture `crates/yu-solver/src/candidate_source.rs::local_self_recursion_tests::hir`, exact source spelling `my outer = { my loop x = { my direct = loop x; my helper y = loop y; helper x }; loop }`, through syntax, HIR lowering, candidate collection, graph seal, full Value-reference event inventory and actual qualification consumers.

R271-r1 has established only conditional facts: the literal helper yields `None` for ordinary nonempty `{`/identifier spellings; if the specified CST is successfully available, HIR's `form` creates a temporary self Local before parameter bindings, and block construction processes prefix initializers in order with owner-qualified local IDs. These facts do not authenticate the parse, accepted HIR carrier, collection, seal or qualification. Continue the full exact evidence bar and falsifiers from R271-r1; no quantifier or source-domain narrowing. A local discrepancy alone is not a parent counterexample or approved-clause defect.

## Recursive dependency boundary

R271-r1's syntax/HIR manifest was complete for those two packages but omitted their local parser engine. This revision computes a finite package closure from the pinned root package manifests and workspace lock, without Cargo commands:

- Normal local path closure: `yu-syntax` → `chasa-recover`; `yu-hir` → `yu-syntax`; `yu-solver` → `yu-hir`, `yu-syntax`, `yu-types`; `yu-types` → `yu-hir`.
- The fixture is under `yu-solver` `cfg(test)` and calls the HIR `shadow` entrypoint. Its exact `yu-core` dev-dependency manifest is included only to record how the `shadow` feature is activated for that test configuration; no `yu-core` source body or test is authorized.
- `chasa-recover` uses `reborrow-generic` with the derive feature. `In::token` delegates to local `parser::token`; its transaction calls local checkpoint/rollback and `Input::mark/rollback`. `Input for &str` and `LexRecover` are in the exact local package closure.
- Cached registry sources are present for `reborrow-generic` 0.1.2, `reborrow-generic-derive` 0.1.1, and `seq-macro` 0.3.6. Their exact `.crate` archive SHA-256 values match Cargo.lock checksums. The exact cached package manifests and relevant source modules are listed below. No network fetch is allowed.
- `yu-syntax` directly lists registry package `chasa` 0.5.0, but the bounded source-use search found no `chasa::` import/use in the syntax/HIR/solver source roots. Its exact version/checksum is pinned by Cargo.lock; no `chasa` source-body read is authorized by this revision.
- Other registry API dependencies (including rowan and unicode-ident) remain pinned by the exact Cargo.lock. If the source trace requires an unlisted external implementation body, stop before reading/fetching it. Do not treat dependency pinning as a source correctness premise.

The exact manifest below contains 139 paths: all production `.rs` modules in the five repository-local packages above; the complete 100 R271-r1 entries; the root workspace manifest/lock; exact package manifests needed for local closure and feature configuration; and only the cached registry source/archive files named above. Test directories, `*_tests.rs`, dev/test source bodies and all unlisted external sources are excluded. Every worker read is path-by-path within this finite table, never wildcard authority. Read only bodies needed for the source trace. If any required path lies outside the table, stop before opening it.

| Exact path | SHA-256 |
|---|---|
| `/home/momota1029/.cargo/registry/cache/index.crates.io-1949cf8c6b5b557f/reborrow-generic-0.1.2.crate` | `7646e43508f68c666d937914c642cd9acbdacd0d632204748b56314308c0d208` |
| `/home/momota1029/.cargo/registry/cache/index.crates.io-1949cf8c6b5b557f/reborrow-generic-derive-0.1.1.crate` | `954a567771a8f35b8edab95a757ae811572b36a16e6f68c9d91f7ba51b6125ba` |
| `/home/momota1029/.cargo/registry/cache/index.crates.io-1949cf8c6b5b557f/seq-macro-0.3.6.crate` | `1bc711410fbe7399f390ca1c3b60ad0f53f80e95c5eb935e52268a0e2cd49acc` |
| `/home/momota1029/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/reborrow-generic-0.1.2/Cargo.toml` | `9fcde5bb490000f0059c01bf77bb7a47e1ab975b8a38fde136b8a7d7cb45caac` |
| `/home/momota1029/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/reborrow-generic-0.1.2/src/lib.rs` | `818b681625ad08b6a2805fc33c2a077b3248270ff6592cc214e6d816a77b06ed` |
| `/home/momota1029/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/reborrow-generic-derive-0.1.1/Cargo.toml` | `9711dd904f2dd189dc0d3f1adfdccddf5c8abe061665ded1d3acd62b9544a502` |
| `/home/momota1029/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/reborrow-generic-derive-0.1.1/src/lib.rs` | `53b2b16bcb50de8196a116c9dba735f820523a3f165642a76e859283b81f0b2e` |
| `/home/momota1029/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/seq-macro-0.3.6/Cargo.toml` | `f5eba9db2eb619a616a3fd1bec4a02bc2cd3acaa88cf0f549c645606bdcca39e` |
| `/home/momota1029/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/seq-macro-0.3.6/src/lib.rs` | `218aeb16d88888358fd7a966e44f645da53b68da98d36fa3a58fa5e7caacf242` |
| `/home/momota1029/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/seq-macro-0.3.6/src/parse.rs` | `d9cb43862649ac90caa72f5da26e2c3cdedda873cef200c276d528280c3c9ecb` |
| `Cargo.lock` | `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5` |
| `Cargo.toml` | `a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a` |
| `crates/chasa-recover/Cargo.toml` | `ff7ef8af10850ac4b1de7822f4897ed483810b61e9a118bd1db3d296cb2ec903` |
| `crates/chasa-recover/src/input.rs` | `303d4dbcad1030b2a3f270a677b0cbfe697bf703c6cd39f159f88348da69bffe` |
| `crates/chasa-recover/src/lib.rs` | `c88c816920daf1b3af9f35b05cf4a256b499e77c78eb02890f62339a1aceff72` |
| `crates/chasa-recover/src/parser.rs` | `1fdc8ba6be46b8f34a6224f7687d1f192b086273180d5b7f593397b98df09bbf` |
| `crates/yu-core/Cargo.toml` | `2be9f92dbb92013436311b696b4020d10bc99a965a82a25181d8957fc5e1b08d` |
| `crates/yu-hir/Cargo.toml` | `a97f52fc6b9e577f23be4160ecdda9693bec8fe48c626d0e9b7c0e3b0c6fe8d1` |
| `crates/yu-hir/src/lib.rs` | `4daa2b1753fcf2984c5c27bacb968541c51115ca9f7619d36f8c0e6c7972ef5b` |
| `crates/yu-hir/src/module.rs` | `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646` |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `crates/yu-hir/src/module/local_source/string.rs` | `f0fe4d7146a4c6c36779a36e352e02f3844303f80a41d79abd07cd47ab19f717` |
| `crates/yu-hir/src/module/source_annotation.rs` | `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f` |
| `crates/yu-hir/src/module/source_exports.rs` | `03727fd3918738a48afde7f7a875de60b63b43ac2cc620896a4ed73d8b0a9179` |
| `crates/yu-hir/src/module/source_impl.rs` | `558ec50c83040d21fa05e768dffdc46b8a328435b56fc828822a6190ba56a2d5` |
| `crates/yu-hir/src/module/source_role.rs` | `d16945ae153d25cdadea9e9071cdfc2ab73925b46d92e598a0e18e5d60f4d3e3` |
| `crates/yu-hir/src/shadow.rs` | `b964bab6dcdb7ebeca9f964c134ac8fb041c928c20ce0a895fea6b6af0fbb93e` |
| `crates/yu-hir/src/source_identity.rs` | `4bd5fa4066a1fd445a9757374c44d602decd1d791a394cd81c6066efa063fb23` |
| `crates/yu-solver/Cargo.toml` | `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed` |
| `crates/yu-solver/src/candidate_call.rs` | `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f` |
| `crates/yu-solver/src/candidate_context.rs` | `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905` |
| `crates/yu-solver/src/candidate_effect.rs` | `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_receiver.rs` | `5ca308e7b890e57a8458a151554ece55585d762565204d39c520c4b534e44ade` |
| `crates/yu-solver/src/candidate_scheme.rs` | `6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e` |
| `crates/yu-solver/src/candidate_scope.rs` | `4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03` |
| `crates/yu-solver/src/candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `crates/yu-solver/src/candidate_value_graph.rs` | `aaaa88a374083f898188cd390b8cf0244855d8c09c8939b9e68ee2831bc692cf` |
| `crates/yu-solver/src/f5c_binder_substitution.rs` | `6b2d9d53546fc2218132dad65fac8619ec125c65817af5fe42239ebc85ffee80` |
| `crates/yu-solver/src/f5c_draft.rs` | `cb67684c633214878c1795d896aca02b525ebf8de4e5cbd3aaf8de7a8e6c433d` |
| `crates/yu-solver/src/f5c_draft_heap.rs` | `b973ec0667e6f80de54d9a1de55df112361859982ea2617dae3fe8d34903b1cb` |
| `crates/yu-solver/src/f5c_generalization.rs` | `928607961bff9ab747fd759aed1dacd3aa13abc9e20bf3bb8a957a4c7bd12ffb` |
| `crates/yu-solver/src/f5c_generalization/flat_source_arena.rs` | `0abc91b90303818bd372bc33d1e391e24a2bb747df70984cad8f54f5d60f3af7` |
| `crates/yu-solver/src/f5c_generalization/flat_walk_sink.rs` | `ff8b117e7578d93f1d441faec132df4859b7118c5a0d56d1044dbb3f2ab913b1` |
| `crates/yu-solver/src/f5c_materialization.rs` | `a342860980dc14dd6dc10996adf992946e1b420b6d3d8ee176a77937d0c6a93b` |
| `crates/yu-solver/src/f5c_normalization.rs` | `da57ee8fc3dd3a604ef5bf65457cf0c4d38fb976eb9e080e8520ea6a1e97728a` |
| `crates/yu-solver/src/f5c_replay.rs` | `71fb166c38dbd93571abcbc3ff290b3b79fe2a4ecba8159edd5f60933c8b3b2a` |
| `crates/yu-solver/src/f5c_tree_analysis.rs` | `f69fb7938dd22ba6cc65b8a1474e9e3f05c30af106c3ca110778b4a225807173` |
| `crates/yu-solver/src/incoming_sample_trace.rs` | `b3b10bed1b41b138a83e37346969f946deeac43192ae0e551f8c343fd44f12c5` |
| `crates/yu-solver/src/intrusion_transport.rs` | `22015507c307e9dffcd1ad25fec3c8d4184545106110fbfd71ba11472ba95458` |
| `crates/yu-solver/src/lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| `crates/yu-solver/src/scc.rs` | `8f3709ec9d52dc79767b6822eb4f671118a3f83814d2e9a9c748dfeac51e1f72` |
| `crates/yu-solver/src/shadow_apply.rs` | `99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5` |
| `crates/yu-solver/src/shadow_apply/local_source_observation.rs` | `fa7e5a1288eae3ed9093a733645adcac4bd88011802d4fe95fdd10acab2fe66b` |
| `crates/yu-solver/src/shadow_candidate_source_crosswalk.rs` | `392d665579a74810134846e1274c0c9ce975a7eb0e2cfb9ad79a07af2cd2eeb0` |
| `crates/yu-solver/src/shadow_f5.rs` | `b6a6c70da75329ff66cd9e6c0a2598a54cc8f0de7ba956f6f28b24616ca3a994` |
| `crates/yu-solver/src/shadow_initialization.rs` | `6ea0914a11a4a05d6dde8d63c413cfd42fb887596b3315d998848d502a91715a` |
| `crates/yu-solver/src/shadow_scc.rs` | `79e8ff5f459b6fc1389ecacb1da594814f9d9235297d62bc0501c2b3795b39c9` |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| `crates/yu-syntax/Cargo.toml` | `567b705fabf7558250dbfa59e833d4ff04cb3041db8ed742311865d8cf3081d3` |
| `crates/yu-syntax/src/ambient_claim.rs` | `e46fdf1858094fde5535364ebc78f6f0a4997e15ac968a4edf06da9b434bce9f` |
| `crates/yu-syntax/src/cursor.rs` | `f08aae49fcf048ad11890def7ef9cadab56825a63b8d87db44821a792fe9b142` |
| `crates/yu-syntax/src/cursor/recovery.rs` | `1e216cf585e5548abc178fab0ebc90b6aef409b22c507dda3e08a52399a45f6e` |
| `crates/yu-syntax/src/cursor/recovery/emit.rs` | `d9866a13f28e1acb1e80f927b64baa4d97f51a5e7934ab5c1d870ea757e497a5` |
| `crates/yu-syntax/src/declaration/act_decl.rs` | `a8582ecc71c37ec4f531ca0441901053e132ec9a2325681496b88e5f695dd9fd` |
| `crates/yu-syntax/src/declaration/binding.rs` | `a9b0602fccc90d49f294706092c85b373b06869b678cdd4c25efd429d0374387` |
| `crates/yu-syntax/src/declaration/cast_decl.rs` | `c4907b91f0cbe72606597fb6ef1918c757e9f78621a2c4c68bf0632fe629a0ed` |
| `crates/yu-syntax/src/declaration/declaration_companion.rs` | `ea033e30aaa9e8f2ae5ecb5264debd7d51ec532ba9f7ec9c7fedd476bfc78681` |
| `crates/yu-syntax/src/declaration/declaration_variant.rs` | `204a44d42cdf7706d58e7849050683610e270049c49a079e8af2d5af541e2220` |
| `crates/yu-syntax/src/declaration/derives.rs` | `13de94bad098dc312e1a30bac45a82ed2de5f5bc7046353a65ea15dd4411ebf0` |
| `crates/yu-syntax/src/declaration/enum_decl.rs` | `9c717571426927a3619330b372ec721d1f660377ecd45c6f0ab7f6cf9ed3ec31` |
| `crates/yu-syntax/src/declaration/error_decl.rs` | `56eace59a91d156f59d27a348e98ea353e9cc96595a49fc0f7e58d36dcd7a028` |
| `crates/yu-syntax/src/declaration/fields.rs` | `cd92297422bc49a3574e07f3c81e240bff456d135f0c4ba194296e36fcf5ca93` |
| `crates/yu-syntax/src/declaration/impl_decl.rs` | `026edcb3e6d3c9f2214be8b9fa9fd510378b64152de55673c18cb93373f62066` |
| `crates/yu-syntax/src/declaration/impl_tail.rs` | `9f3e60f47542919aa713efae44ad9396fff43ba464064b3e5c093b7a6cb83e61` |
| `crates/yu-syntax/src/declaration/mod.rs` | `cf1067280be3974a5702b18f47ac02cf824c9d8cf971c1bdbc1b143676fc5c71` |
| `crates/yu-syntax/src/declaration/mod_decl.rs` | `6adf9945e096ee027886a05857f6c187134a5331e4ab37493d95304255760741` |
| `crates/yu-syntax/src/declaration/operator_header.rs` | `021e79529445054e5d54bfccf93d2287e94221a99e1554fbd7c715cb0706edbd` |
| `crates/yu-syntax/src/declaration/role_decl.rs` | `0ec972a3acc036764a9d1407e292a4c676a24beb4cd0b5c3348c093cf3cf8634` |
| `crates/yu-syntax/src/declaration/struct_decl.rs` | `7b36b18fc6ef3e149e756a37b0f74719a5ae40be195c6986efe2c44d57fa3de4` |
| `crates/yu-syntax/src/declaration/type_decl.rs` | `e01d1f30c1dca051fb590a9fddac1686621fc789444f9cb053dcc269e746c134` |
| `crates/yu-syntax/src/declaration/use_decl.rs` | `1f7df7e6101cc398056b610536c723271ed108aeecafe38eb09b8dc62cc45fc0` |
| `crates/yu-syntax/src/diagnostics_schema.rs` | `22967edb1f0819e3cef46b4727601f25bfbb2a8c9a5aa19524833f02efdc10c8` |
| `crates/yu-syntax/src/expression/case_like.rs` | `6e306bc420e4084832008b64cf39c790648fc1510ba3f1de2876590f79ebe961` |
| `crates/yu-syntax/src/expression/delimited.rs` | `e65c4d500ce0878faf13f1a8d31da816e5db9b6af4690b505c8875d27b700f95` |
| `crates/yu-syntax/src/expression/for_decl.rs` | `fd50ab8b049addc3c366a0eda5519fd38bda31a2b518ba139d90ad24949714ec` |
| `crates/yu-syntax/src/expression/if_expr.rs` | `b04aa84e530947ee92ba98451c0b366b05450681d54d78b00dadaa4f8e308282` |
| `crates/yu-syntax/src/expression/lambda.rs` | `56357346a0f59330a202936f88337af1490b1839f339dc113b0b35f2d8c777b0` |
| `crates/yu-syntax/src/expression/mod.rs` | `05d874dd4c2874eb7b24038467c8a74b22fa6f7821a3980f3348683ad02743f1` |
| `crates/yu-syntax/src/expression/operator_chain.rs` | `0929f43e65682766543be6aeb0db2dded40b85fdd470240188da66d89757700b` |
| `crates/yu-syntax/src/expression/required_operand.rs` | `9dc7455b0e97e3d57194126d33d330bd85aaba123d43015894728598d6337714` |
| `crates/yu-syntax/src/expression/tails/assignment.rs` | `8d5229ac9778d1bd5d84c739b2eeff582bb2807ab794c63aa49555ba28c62026` |
| `crates/yu-syntax/src/expression/tails/colon.rs` | `df37d747f396e8b27c53b6785e4a26f5210162b14e65b4648d449495bf8f5982` |
| `crates/yu-syntax/src/expression/tails/delimited_tail.rs` | `349fe2335e04a68da7d07803f2dd2eb185887d07bf8c9475ba09af089a76a2cf` |
| `crates/yu-syntax/src/expression/tails/fixed_access.rs` | `9e88d7ce18d8bd2d3c3bfa6fbdd6cac7e37032a21fedc35774c71597ff7a21bd` |
| `crates/yu-syntax/src/expression/tails/inline_slot.rs` | `de8da369638545727b83fffaadbd487209275f8af9a5c00beb48d1695fbcf5ba` |
| `crates/yu-syntax/src/expression/tails/mod.rs` | `a3ee107c996e028765570c7ba89b12857cd072eddc988b5b4c8eb66ffc753b8c` |
| `crates/yu-syntax/src/expression/tails/type_annotation.rs` | `edf609d719ffb7698b565e41cd6b76a0eae489703f017e70efd90f290e4c9c4a` |
| `crates/yu-syntax/src/expression/tails/with_body.rs` | `4fdf57e9a19b8897871d666ab5ec8adaa7c9219fc775d6c54cddc4555f61c058` |
| `crates/yu-syntax/src/full_parse.rs` | `dd92603f8f5549b8b3f6e45ab6cb39b6598480b7f1cda7897e27b5113107db93` |
| `crates/yu-syntax/src/handoff.rs` | `8ca2c50ae263986423eaf0f43e1a94de9fdf432366698118d6de75feb854d762` |
| `crates/yu-syntax/src/header.rs` | `cd3791144704226f67a05ae3d39aff9b42f4380073b3e9f9817951a493bce5ad` |
| `crates/yu-syntax/src/lexical/current_item.rs` | `41efcce2b737a0362484e854a8549bda5f7bf0d2b911499553f1e449c6782a84` |
| `crates/yu-syntax/src/lexical/expression_item.rs` | `aa291aaab95b633d4b6f61aac237846281d69fa1a9c88b4029a21b5c0de8d350` |
| `crates/yu-syntax/src/lexical/item.rs` | `b264b63e84fc73a3ef7dba355864be84d756fab287fa3734eaf37992e3655db7` |
| `crates/yu-syntax/src/lexical/lexer.rs` | `620f91d99cd4b0bd320315398466cbbec2ed625b8a8ebc6ba07f84d0c97524d1` |
| `crates/yu-syntax/src/lexical/mod.rs` | `0f3109a348c48747bd75d46de8afcbf40863c94c10a5bef8c768b6a0a8661c07` |
| `crates/yu-syntax/src/lexical/observation.rs` | `730e65947f889ef07014aa003eb846012d5cec6ae1434f77edf1cbd0e7096641` |
| `crates/yu-syntax/src/lexical/opaque_region.rs` | `ef905c9d5301e3cbea0634efc9c2ab9844b7de0b2862cfd47c0b22413ec00e4a` |
| `crates/yu-syntax/src/lexical/operator_scan.rs` | `610d3996a5bf173633de24e6a4b205340125f6e1c24bbafc292dfa15cbd076ba` |
| `crates/yu-syntax/src/lexical/position.rs` | `0ca1b4acb27904c28e62b950ae04ee114d992cdffa27accf6098793e73cbb766` |
| `crates/yu-syntax/src/lexical/stops.rs` | `edcf37bbe061c0966ba786d9090361c6c3befdbe3f99aa79f29271bd5230bf5b` |
| `crates/yu-syntax/src/lexical/trivia.rs` | `887f1499fe63d870a70777626f0357c502a356d106c623d9a79e3596a17aba19` |
| `crates/yu-syntax/src/lexical/yumark.rs` | `21738dda1f64d27273983246f0f5d22b0a6da0025209132238a91154c38fcf75` |
| `crates/yu-syntax/src/lib.rs` | `770a4af4a5832b3210050b4fc5513545569b0ca4718597f67434a714f76f301d` |
| `crates/yu-syntax/src/literal/mod.rs` | `7cca1bf63c176809621b5b8e6c011faaf038bf9d2aad05f77e2f7234fb4b01c9` |
| `crates/yu-syntax/src/literal/rule_literal.rs` | `d21f7e27eb89dfa3c6717b895726e827974728be962faefcb08c9ce9092753ee` |
| `crates/yu-syntax/src/operator_compilation.rs` | `5a13e0b62979ec02c265f9e7f427b772035b395eb661e37f16de6a4f5b04de87` |
| `crates/yu-syntax/src/operator_table.rs` | `18a5e54ba38df0c9f923f136cb16652fb910dafbecc6fdc6c146d034fcb43014` |
| `crates/yu-syntax/src/pattern/delimited.rs` | `9da9ec948775b438a85ca3f27c2805254a4f4171caddb54cabe44e563d017029` |
| `crates/yu-syntax/src/pattern/mod.rs` | `f86fb57da7412376defd7ad15a3cd5671c0708bed55016223a7a038d8c7d303f` |
| `crates/yu-syntax/src/root_statement.rs` | `c6d1dc49625d1687ff0dae8f6808f4c97c3f78398aae3bc061c44b6fc9661626` |
| `crates/yu-syntax/src/rule/expression_list.rs` | `e30e915dca56c9609709280e9f053c151e16e1f9619340a56abd470241b545f5` |
| `crates/yu-syntax/src/rule/mod.rs` | `ed5fd98986375025b0e37c9378ad9fbd2a0e35c1e4d5761a55148b578f888707` |
| `crates/yu-syntax/src/sequence.rs` | `1a68331e5d16d46471545e673226541dc848123d1c3e286260359cecf41adcd2` |
| `crates/yu-syntax/src/statement.rs` | `2370423ffef9869032da275a12e6d4a96deb9b1bf43ea098320d78ca6fc45bfd` |
| `crates/yu-syntax/src/structural_diagnostic.rs` | `6cabb3482d24c8a68a65864d6171c09bebcec4d25a305e90a60909d3dce37036` |
| `crates/yu-syntax/src/syntax_diagnostic.rs` | `b3c5e959e646ad3d557c4f60c367d80731bf6a8e616a08326827f687e9077714` |
| `crates/yu-syntax/src/syntax_environment.rs` | `fdafdb177c8e2db7a44d66a8d9bc0c1905cc0a22da6457e470a165ca2501c5d7` |
| `crates/yu-syntax/src/syntax_kind.rs` | `fc0cde7e3347b65d7641a589ee02cdc1da6b7fba3fed07cc7d378df20a7bb6a3` |
| `crates/yu-syntax/src/type_expr/delimited.rs` | `db6335a8f6c95bafb72d096fe241201202938c5869fb89a5e3c43758021651b6` |
| `crates/yu-syntax/src/type_expr/forall.rs` | `987f9f923bff80b8476ffa64b1e8b53d4784e84c07dbc1472c7bf305469fe71f` |
| `crates/yu-syntax/src/type_expr/mod.rs` | `2e08a49960cd4010ba39641ae509afb7cf59711c1464d3349f5f6db590ebf01f` |
| `crates/yu-syntax/src/type_expr/record.rs` | `98d93b9795f4a33fe4a43e0368921e4ab698278fd8895eb1214b792a9a1fda57` |
| `crates/yu-syntax/src/type_expr/variants.rs` | `8ccf273de0d475b999207f216822f35354cdee51a2b00aba3a8be5bafd2bc16e` |
| `crates/yu-syntax/src/virtual_statement_block.rs` | `dd1534640c8bd5e9497272ff1ff8e0c63be17176a0dbbcd67799eec673057b82` |
| `crates/yu-types/Cargo.toml` | `1fae5cab6325fc575ff586f665460592c3c66d9fb03310d060d5d018cb251a9c` |
| `crates/yu-types/src/lib.rs` | `fb3d53cdcce6a2d7149508ba0bdc9dad643cfc795fefdb9914afcb461e4aa6d8` |

Recheck all 139 rows before technical reads and at immutable freeze. Preserve the root Cargo.lock package identity/checksum entries and verify cached `.crate` hashes against them. No Cargo metadata/build/download command is permitted.

## Sol lane and accounting

Resume the existing stopped registered Sol prover identity `/root/sol_r270_source_qualification_auth`, Sol/high, after fresh live-roster comparison, contract-only WAITING receipt, exact output lease record and a fresh explicit GO. No descendants. The new R271-r2 Sol grant is a separate 1,800 seconds; all prior R271-r1 1,800 and R270 4,500 charges remain fully charged. No reset/refund.

Stages:
1. Revalidate the exact manifest and derive the concrete `SyntaxIn::token` → `chasa_recover::In::token` → `parser::Token::run_once` → `checkpoint/rollback` equation. Follow `Input for &str`, `LexRecover` and the cached reborrow derive/trait only as needed. Establish the exact failed continuation/suffix restoration for the fixture's whitespace without relying on unit-test execution.
2. Continue full syntax/header/full parse; construct exact HIR roots, local binding IDs, parameter scopes and Name resolutions. Establish successful carrier formation under the actual fixture input, not from `unwrap` or expected tests.
3. Trace retained source through candidate collection; enumerate all vertices, planning levels, raw edges and events; derive the actual graph `seal` premises/result, each qualification value and its real consumers. Check competing paths and apply only proved facts to the approved rule and unchanged parent.
4. On any failed constructor or external/unlisted dependency, stop at the first exact premise/owner and preserve the conditional prefix facts. Do not create an R271-r3 assignment automatically.

Exact output files, regranted only after absence verification and GO:
- `notes/theory/2026-11-02-source-qualification-authentication-r271.md`
- `tasks/agent-loop/inbox/source-qualification-authentication-r271.md`

The R271-r1 reviewer reservation was cancelled unissued. This revision reserves a fresh independent reviewer `/root/r271_source_qualification_review`, requested gpt-6.1-sol/medium, maximum 600 seconds, but does not issue it until Sol freezes a coherent result. Luna records review at `tasks/agent-loop/history/20261102-r271-source-qualification-review.md`. The reviewer challenges cursor restoration, parse/HIR rejection paths, exact resolved carrier, collection/seal success, full event inventory, qualification and parent application.

R271 cumulative accounting after this revision is exactly 5,400 seconds retained/allocated: r1 Sol 1,800 charged + r1 Luna 600 retained + fresh r2 envelope 3,000 (Sol 1,800, review 600, Luna 600). The r1 review reservation remains cancelled/unspent. R270 charges remain separate. No Astra or descendants, automatic renewal, semantic change or code edit. Parent/A/B remains 0→0 unless actual evidence justifies a change; implementation remains `NO_SAFE_CODE_SLICE`. Stop at the exact grant or authority boundary and consult the dispatcher at the next material event.

Operational whitelist remains R271-r1's exact ordered whitelist, with only its technical-source section superseded by these 139 exact rows. No tests, builds, probes, benchmarks, Cargo, Lean, source edits, generated/scratch/cache output, Git, network or nested CLI.
