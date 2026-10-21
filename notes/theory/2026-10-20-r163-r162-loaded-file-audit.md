# R163 audit of the frozen R162 loaded-file prefix

Status: frozen revision 1; source/artifact evidence, pending fresh independent review. Author `/root/r163_source_audit`; no descendants. Exact lease: this note only. The current-session parent assignment grants 180 seconds, read-only inputs, no builds/tests/sample runs, source edits or Git mutation. Requested/observed model metadata is UNKNOWN here. No claim of independent review.

## Objective, baseline and authority

Authenticate every loaded-file record in the existing R162 Types JSONL against the exact R161 inputs; characterize the smaller source identity premise supplied to R152–R154. Method: deterministic Python standard-library decoding, byte equality, SHA-256/Git-blob SHA-1, contiguous UTF-8 span checks and a CST kind stack. This is a bounded source/artifact characterization, not a new language decision or constructive parent theorem.

Pinned Y2 baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`. The repository HEAD observed read-only was `09f5108098d55bc09326ace1f05ca6b6aaf667e1`; no repository compiler bytes enter the calculation. Governing sections: R163 contract “Frozen prefix and exact input identities”, “Outcome and parent gates”, and “Lanes, resources, review, and stop conditions”; packet “Source/proof analysis lease”; rules/design-authority.md “Authority order”; rules/git-concurrency.md “Integration ownership” and “Disjoint-file mode”; rules/research-lab.pre-sprint.md “One semantic baseline, explicit dependency invalidation” and “Commit conveyor and two-phase integration”. Root AGENTS/AGENTS.pre-sprint, current state and its README were read. The sprint skill limits this child to its packet; the yulang-proofs skill distinguishes source evidence from theorem closure. No child dispatch occurred.

The accepted Types/Console sources, initialization/output requirements and original Simple-sub/evaluator A/B quantifiers remain as selected by the primary. No alternative language meaning is proposed.

## Frozen dependency hashes

- `tasks/agent-loop/sprints/yulang2-types-console-loaded-registration-witness-20261020-r163.md`: `e3f6db10990b9e791402e186a3f5dbbc2bfff543dca4593baa765309fb0a11e0`.
- `tasks/agent-loop/inbox/20261020-r163-loaded-witness.md`: `61052288f773089a056eefb619f544fe0ae50fb5ebd557208e21c179d8220430`.
- `notes/theory/2026-10-20-types-console-initializer-certificate-r152-rev2.md`: `e062bbd9db76669dbd9335ed99c2902ea28ad7ee9106051dc90f5f1a0966cd0c`.
- `notes/progress/2026-10-20-r153-closeout.md`: `1cfef02ddad05dc43e0004694b6f4b34431daead2839e4687c44922d70b313cb`.
- `notes/progress/2026-10-20-r154-closeout.md`: `45413f2e896fdd50ad4761cd6a4572a7a993a3f8b33a54664416e40f79f76ea5`.
- `notes/theory/2026-10-20-types-console-registration-certificate.md`: `35f31341c74d36404e950f763ac669b73c7025ac3abd206397806507550d0818`.

- `/tmp/yulang2-r160-observer/out/types.jsonl`: `413fd2e4a260f9a16b5a58b811cf391f349ded5095c09a9eccfd38992a279eda`, 6,496,626 bytes.
- `/tmp/yulang2-r161-witness/logs/lib-manifest.txt`: `15d7355d8768adbde5bec5a0a77796b1717db733e897bb56e84795e5ef8ac211`, exactly 40 distinct entries.
- Exact Types input: 142 bytes, `8cbfb97a8df8e5dc4916313769c39a84626ae124f91f8a9672f1ad8b866f98e6`.
- Exact Console input: `ada6174d8795ddb10a8c533c812b771d9dddced816762e0e246022467499a076`; identity checked only, with no Console loaded record in this evidence.

No dependency was changed. The R152 reviewed rev2 hash above is the actual current hash, consistent with the R153 closeout; this audit does not reuse the earlier unreviewed hash.

## Executed checks and derivation

All Python audit commands exited 0. No compiler, test, build, sample or runtime process ran. Commands were `python3 - <<'PY'` standard-library input audits, plus read-only `rg`, `cat`, `sed`, `head`, `pwd` and `git rev-parse HEAD`. The principal calculation was:

1. Decode every JSONL line; require event ordinals exactly `list(range(730))`, first 41 events `loaded_file`, remaining 689 `registration_event`. All lines are complete JSON; JSON completeness is not run completeness.
2. For each nonempty loaded module path, map segments to `lib/<segments joined by />.yu`; require its source bytes equal that disk file, SHA-256 equal the corresponding manifest entry, and SHA-1 of `b"blob "+decimal_length+b"\0"+bytes` equal its manifest blob ID. Require the encountered 40 paths equal the entire manifest path set, with one occurrence each. All library band paths are empty. The Types record has empty module path and band path `["Types"]`.
3. Require Types loaded bytes equal `b"use std::prelude::*\nmod std;\n" + Types_input_bytes`. The prefix is 29 bytes; the loaded total is 171 bytes, with SHA-256 `39e4482e95321ede5eeadedc47e84bcf9dd27c589c17936f0cb18a08a0b478fd`.
4. For each record require `source_bytes == len(source.encode("utf-8"))`. Iterate all CST events: push each enter kind; each leave must pop the identical kind; enter/leave text/start/end must be null. A token requires a nonempty stack, start equal the accumulated byte offset, end equal start plus UTF-8 token byte length, and exact equality to the corresponding source byte slice. Both endpoints must decode as UTF-8 boundaries. Require final offset equals source length, empty stack, and concatenated token text equals source text.
5. For every registration record join `source_file.segments` to a loaded `module_path`; every present span names that same file and lies within its UTF-8 byte boundaries. Of 689 records, 655 spans are present, 22 absent and 12 suppressed by copy. For the 584 available module/band joins, choose the longest loaded-module ancestor of module_path and require band_path equals that loaded file's band. All pass. For 105 `unavailable_anonymous_ancestry` records, both paths are null and both statuses identify that limitation. These structural joins do not reconstruct the anonymous owner.

Coverage: all 41 records, 87,648 source bytes, 32,929 tokens, 20,703 enter/leave pairs, 74,335 total CST events, including 45 source bytes with the high bit set. No seeds, random range, mutation campaign or generated source cases were used. A diagnostic candidate equation `band_path = module_path` was rejected by the actual records: library declarations inherit the empty band; it is not an accepted source invariant. The successful check uses the explicit loaded ancestor/band join above.

The independently supplied source bytes and manifest discriminate source substitutions, truncation, length errors and module/file swaps. The CST balance/span checks would reject mismatched kinds, omitted/duplicated token bytes, noncontiguous offsets and offsets within UTF-8 encodings. Failure of any required equality would block this audit. No such failure occurred. SHA checks authenticate agreement with the pinned inputs, not an independent historical origin of the primary-supplied manifest.

## Per-record authentication

Every row passed all byte, manifest (library rows), UTF-8, concatenation and balanced-kind checks. Order below is the observed stream order, not a declaration or runtime-root order theorem.

| Ordinal | Source | Bytes | Tokens | Source SHA-256 |
|---|---|---:|---:|---|
| 0 | lib/std.yu | 174 | 84 | `0abfa2ee4dd8c73d926fbbdcc00d282177b0d37e38b7358b2c015bd5d904c1f5` |
| 1 | lib/std/core.yu | 112 | 67 | `984643783e83bc1bd9c8998fe6b9bcc26a0d3b7606050fb3e37ec5859e8529b7` |
| 2 | lib/std/int.yu | 676 | 276 | `2d0d9b3bba4a4726dbb7f985e46524eea6b7e794759719a78d31984792b79822` |
| 3 | lib/std/float.yu | 583 | 219 | `3ae124ddb0b0034e20fff5a97b9ba3dd4e94cd8ba4aad318adcf06444e37a5fe` |
| 4 | lib/std/bool.yu | 177 | 66 | `2d52be35270f14a487b88608e508aed64860a2f0b3a3843fbc843e9e19e18eb9` |
| 5 | lib/std/num.yu | 1315 | 628 | `631417ef1a85e38564fcc10d17b6eac6f64dfb735bf46d823ef1c7dd015f5e69` |
| 6 | lib/std/data.yu | 87 | 42 | `6d01995705e03e3d3ccb5c65a367c84510d1bf7346d0e0f58edab3bff70bf84c` |
| 7 | lib/std/text.yu | 103 | 49 | `81922b35c86cc5c0f97380535abaf11d4c717f88b7d31feb5fe361dc0f4926eb` |
| 8 | lib/std/control.yu | 76 | 35 | `e8882cf281655a4db91f073801d9ef3a7b93cf62ce038b0650410fd87ea9ba25` |
| 9 | lib/std/io.yu | 122 | 58 | `21c5b06167bbf1ab8363ee0517dfa5f47914d5fba15598392ec64becb70d86e0` |
| 10 | lib/std/time.yu | 4689 | 1958 | `1ecaa6181213fcac70922579b964bd491947c95ea1cda8ee09cc00f2a081d29f` |
| 11 | lib/std/testing.yu | 452 | 168 | `adac62af53c21b9a70d83035f37e265f9415c49510db324680b2884ad3da1f91` |
| 12 | lib/std/prelude.yu | 1070 | 413 | `a9d65efddb7d5bb3a8962a2cd64e9bd55a377ec6ff5b3bc29c25db8d1a67b3e0` |
| 13 | lib/std/core/cmp.yu | 1453 | 701 | `03881a76d3a159a23079ff0a1a87dbca42c4c101df47cd61c8f850fcbb7e33a8` |
| 14 | lib/std/core/convert.yu | 267 | 120 | `ba8b1c5dbc5bbb324953dc0cf2e267710b84c08638db89da7b757457f72074fb` |
| 15 | lib/std/core/fmt.yu | 7737 | 2958 | `bb36229d7d75008a5ae4fef6c162bbf4bd7dd7ab186cd331fd689daaa71cf212` |
| 16 | lib/std/core/ops.yu | 2055 | 928 | `cb2c15eca2803a6b5a65e33541dd1213bd5f985c470a7767c17a4d59f77ca8c0` |
| 17 | lib/std/core/seq.yu | 472 | 215 | `64a72e1095913f52c4105bcc73493ace22371f71e05af88585225dae81f7067a` |
| 18 | lib/std/num/frac.yu | 1963 | 889 | `2d6dbf1cac9d45871cc9fcbe812e6a9999361bdf7d285bab916397a08b3e0939` |
| 19 | lib/std/data/fold.yu | 712 | 280 | `e822e1ba32abd4147179ef580bfcecaeb28027e514d368bda057a6953f88cbd3` |
| 20 | lib/std/data/index.yu | 86 | 27 | `66c31cd3f83bae43a990c8a79276bd8a6f0020f654a0da2755dcfec10501ada0` |
| 21 | lib/std/data/list.yu | 4445 | 1886 | `f6dc71d39f1b3b965ef2e766ce4749f68b3e3fbdcebe777f13f801b958e83125` |
| 22 | lib/std/data/opt.yu | 64 | 33 | `c1fe41a74f9c7f6b36bdbf3ca80056ecc78bd62e77ed2e8819ba8f791eb57c1a` |
| 23 | lib/std/data/range.yu | 1977 | 801 | `a7c341ebac7cf7f43a0e548da92fb06caf731f6691f1053abf9498cb1f066f7a` |
| 24 | lib/std/data/result.yu | 738 | 302 | `71ff113880bd6f0fb3f3b8d931fb8b508fa1a37d79d7957302d35eace607a7e2` |
| 25 | lib/std/text/bytes.yu | 1094 | 409 | `65e0b5b315166fecdf8d5b4abe99c7609416c635098e88f803008d6f104f13bd` |
| 26 | lib/std/text/char.yu | 556 | 178 | `5e453910ccf392a36a4b359d5f03948050a922a64de8ad29fdd7e031ea3d3af2` |
| 27 | lib/std/text/config.yu | 4103 | 1247 | `18fdfb8c10c1d9f34f9e45a859a362ef53ed1f838f96b4a38a7105e813ba3b35` |
| 28 | lib/std/text/parse.yu | 12498 | 4514 | `b17dce9b9474a3cec830f2c749210e00c752144822836512c928d64d716f5845` |
| 29 | lib/std/text/path.yu | 407 | 144 | `aa05a885d9bec57df63a9330c55c4e6ccb65329f8deee941fa48e29c149c9fab` |
| 30 | lib/std/text/str.yu | 19664 | 6620 | `3ba0fb8e37c7dbfc6ff118611530632d02a9017c8433c10fbcfa2ad4f0c2513b` |
| 31 | lib/std/text/yumark.yu | 7719 | 2509 | `8384abc7a19934e02e3640ce8996fbfa42569585f230fa7ad9e0c10046783680` |
| 32 | lib/std/control/flow.yu | 2615 | 1119 | `8800b16df70d6df4cf45f652bebc57cd9a0428dcd3849a1d852e0a2546a331d8` |
| 33 | lib/std/control/junction.yu | 775 | 319 | `63c33098ad7e17c3ac5fdd924d58b57b0e24450f491c9b6a57e127e249e97a9d` |
| 34 | lib/std/control/throw.yu | 67 | 25 | `aa6803e6ca976f97229a1697f3baac3e017b660821538a41b66889832f26dd89` |
| 35 | lib/std/control/nondet.yu | 1722 | 714 | `ff04cc3f126fad3e4e828aef629c44b5c6e74ed458f09f55c6199cd3f6507159` |
| 36 | lib/std/control/var.yu | 633 | 306 | `dc670a126dc9d7abccc9453140ebc1b30c2d9d6c5b1329b5e0841db7fbdff8a2` |
| 37 | lib/std/io/console.yu | 659 | 312 | `37e95b1e3b744e5824268f46022b8544f9aeaad8f7532733ad074aef61598a93` |
| 38 | lib/std/io/file.yu | 2203 | 848 | `ce03a8f7f4e383d8376f164efbde37272f94f82bef09ba01c31ee80f1d550034` |
| 39 | lib/std/io/net.yu | 1157 | 397 | `e653f1fe333f08fb51a7aaa0ab3a4af7861a3f157e8044048bdee331d5e9ecb5` |
| 40 | input/Types.yu + loader prefix | 171 | 65 | `39e4482e95321ede5eeadedc47e84bcf9dd27c589c17936f0cb18a08a0b478fd` |

## Registration prefix and exact obstruction

There are **689 registration events only, a prefix ending at ordinal 729**. They are not a complete registration witness. The last record is `act_companion_binding`, DefId 1013, module 193, module order 2, name `sub`, mode `CopiedSourceExport`, path `std::control::flow::label_loop::next`, copied-source provenance and suppressed source span. No subsequent event, completion sentinel, complete ModuleTable or successful process termination is present. The primary's R162 receipt reports timeout status 124 at 60 seconds. No completion count can be inferred from the maximum DefId or the valid last JSON line.

The prefix does contain four direct-CST Types binding events:

| Ordinal | DefId | Module/order | Name | Loaded UTF-8 name span | Visibility |
|---:|---:|---|---|---|---|
| 41 | 1 | 0/2 | id | [84,86) | Our |
| 42 | 2 | 0/3 | answer | [97,103) | Pub |
| 43 | 3 | 0/4 | name | [116,120) | Pub |
| 44 | 4 | 0/5 | pair | [139,143) | Pub |

Those source slices equal the indicated names. This gives named identity evidence for these observed events, not completeness of sample/imported/generated declarations. Event-kind counts are binding_value 317; role_companion_method 33; role_impl_method 105; operator_decl 36; act_companion_operation 49; synthetic_value_helper 58; act_companion_binding 27; act_companion_method 4; type_companion_method 60. Counts describe only the prefix.

## Application to R152–R154 and oracle independence

Established here: the recorded loaded source/CST text has exact pinned source identity, byte extent and internal nesting, with explicit module/band joins. This supplies the finite loaded-file identity subpremise that R154 left unknown for the captured Types invocation. It also ties the four observed Types name events to exact source offsets.

Conditional use only: if the reviewed observer actually emits the production GreenNode and the registration events from their claimed producer sites, these records are evidence of that source route. The observer's CST walk and the parser share the actual candidate construction; byte reconstruction is an independent calculation, but not an independently implemented parser or a proof of parser grammar correctness. The audit does not prove SyntaxKind meanings, operator-table correctness, complete registration-table construction, or that every omitted producer was observed. It does not re-audit the observer binary/candidate correspondence or the R152–R154 source owners. Their CLEAN relations are reused only within their stated hypotheses.

R152 publication/classification and R153 helper/cursor facts cannot supply missing registration events or successful lowering. R154's fixed-table vector/query/cursor relation still requires the actual complete table and consumer success/stability premises. Therefore the remaining premise is narrower than unknown loaded bytes, but the complete declaration/root census, imported identity and composition/order/cycle bridge remain UNKNOWN. No census, static inference acceptance, runtime host output, theorem closure or production claim follows. `WAITING_NO_SAFE_CODE_SLICE` and all original parent gates remain OPEN.

Resource receipt: one sequential Python process per small input audit; principal audited input is 6.50 MB; observed principal Python peak RSS 57,840 KiB, audit process wall receipt 0.026 seconds (not whole assignment elapsed). No heavyweight processes or generated scratch artifacts. Whole-assignment CPU and precise elapsed wall time were not instrumented; work stopped within the 180-second grant. Only this leased note was created. No Git mutation, source edit, manifest/lockfile write or shared-record write occurred.

Recommended next action: fresh independent review of this frozen audit and the R163 candidate/packet, then only the primary may issue the separately budgeted complete static captures to resolve the missing registration tail.

## Commit packet

- Exact leased path: `notes/theory/2026-10-20-r163-r162-loaded-file-audit.md`.
- Baseline SHA: Y2 `a58eefc31e22141574b6f20c6a5748151c6d79f1`; observed Y3 HEAD `09f5108098d55bc09326ace1f05ca6b6aaf667e1`; R163 contract/packet hashes above.
- Changed dependency hashes: none.
- Review status: frozen revision 1; independent review pending; writes stopped on submission.
- Checks already run: all-line JSON/order/count checks; 40/40 library byte/SHA-256/Git-blob joins; exact Types prefix/sample relation; 41/41 source lengths/token reconstructions/UTF-8 spans/CST stacks; 689 source-file joins and 655 present span bounds; 584 available module/band joins and 105 explicit unavailable pairs; sample/contract/predecessor SHA-256 checks. No builds/tests/sample runs.
- Proposed research-checkpoint message: `research: authenticate R162 loaded-file prefix for R163`.
- Shared-record deltas intentionally left to primary/curator: mark the Types captured loaded-source identity subpremise established as bounded evidence after review; retain incomplete registration prefix through ordinal 729, all census/inference/runtime/parent gates OPEN, and the anonymous-ancestry limitation; record STOPPED/FROZEN worker receipt. No change of authority or semantic decision.
