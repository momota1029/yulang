# R76 proposal: method and role source-to-inference boundary

Status: **PROPOSED / NOT ACTIVE**. This proposal implements the user's portfolio direction to preserve proof depth while broadening beyond effect-storage work. It grants no writer lease, worker, execution, semantic choice, or production authority.

## Parent and portfolio outcome

Continue the compiler's source-to-inference implementation with a bounded method/member-access and declared role/impl slice. The goal is a usable constructor-owned HIR source input plus a constructive source-to-HIR correspondence proof, followed by the first role/method candidate constraint that existing approved authority actually licenses. If no selection law applies, report its exact missing premise and leave selection unresolved.

Do not treat field syntax as method dispatch. Do not equate declared `role`/`impl` with Pure/Handler callable-role inference. Do not infer candidate eligibility, ambiguity resolution, generalization, or method selection from successful solving or from an index key alone. No parser, solver, evaluator, or accepted semantic change is proposed.

The source-level projection may proceed independently of selection where it preserves receiver/member/occurrence/range/scope and declaration identities without assigning a meaning. The earlier design charter keeps method selection, roles, and implementation resolution outside the settled ordinary effect/handler gate; any early work must name its concrete dependency and stay within this bounded input/projection result.

## Evidence and authority pins

Baseline HEAD is `d21c8eb3a87e43dd441474c9f138e71b1d8372ff`. The live worktree is not clean because R74/R75 artifacts and the failed R75 observer snapshot remain uncommitted. Exact R74/R75 dirty source/artifact paths and live-byte hashes at proposal time are in `r75-worktree-manifest-20261019.txt`, SHA-256 `110fdb37e691fc6014b5177e40b0d406d9c32c65d4eed94a75f3aaa694235418`. The manifest excludes the mutable current-state pointer and this R76 proposal itself; those are scheduling records, not compiler overlays. Treat every such overlay as unrelated and frozen; R76 must neither depend on nor modify it. Any manifest/dependency drift invalidates this proposal until Luna repins it.

Pinned source and authority bytes:

- `syntax-reference/en/src/expressions/call-field-path-tails.md` — `0fbbe46d52328b0438c4acc5e2e958380efa45e74ef0020c4762383804d3c253`. It defines `.identifier` as `FieldTail` and explicitly excludes resolution, types, and execution.
- `crates/yu-syntax/src/expression/tails/fixed_access.rs` — `9e88d7ce18d8bd2d3c3bfa6fbdd6cac7e37032a21fedc35774c71597ff7a21bd`.
- `crates/yu-syntax/src/declaration/role_decl.rs` — `0ec972a3acc036764a9d1407e292a4c676a24beb4cd0b5c3348c093cf3cf8634`; `impl_decl.rs` — `026edcb3e6d3c9f2214be8b9fa9fd510378b64152de55673c18cb93373f62066`. These establish parser/CST construction only.
- `crates/yu-hir/src/lib.rs` — `91cbf982d8281af8c364d1e07e7f425b8bf2a71467af54e1012cbc4171f1dd4e`.
- `crates/yu-hir/src/module/local_source.rs` — `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5`.
- `crates/yu-hir/src/module.rs` — `c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a`; `crates/yu-hir/src/shadow.rs` — `460c813cb0d2e21565df011b1d816abbc2b180cef13797a1b7b453e9ee413f66`.
- Test registration owner: `crates/yu-hir/src/lib.rs` at the pinned hash above.
- `docs/yulang3-architecture.md` — `76b59a473c84a0654a40b7598c9a2d4ce54eeb512c6aa3f5213e95aa8fab44a5`, §6.6. It defines candidate index keys `(RoleId, head/shape)` and `(method name, receiver head)`, not selection laws.
- `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` — `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed`; it places method/role/implementation resolution behind the ordinary effect/handler gate unless a concrete dependency requires earlier bounded work.
- `notes/design/2026-10-05-inferred-function-call-views.md` — `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1`. It governs a distinct Pure/Handler callable-role source direction and does not authorize method dispatch or declared-role selection.

No approved method-resolution or declared-role selection law has been identified by this proposal. Its exact applicability is a pre-activation gate, not an implicit assumption.

## Proposed exact write leases

Luna/implementation:

- `crates/yu-hir/src/module/local_source.rs`
- `crates/yu-hir/src/shadow.rs`
- `crates/yu-hir/src/module.rs`
- `crates/yu-hir/src/lib.rs` (only the exact test-module registration)
- new `crates/yu-hir/src/tests/shadow_method_role_source.rs`
- `notes/progress/2026-10-19-r76-method-role-implementation.md`
- `tasks/agent-loop/inbox/20261019-r76-implementation.md`

Proof lane:

- `notes/theory/2026-10-19-r76-method-role-source-proof.md`
- `tasks/agent-loop/inbox/20261019-r76-proof.md`

Fresh compiler/spec reviewers are read-only on one frozen snapshot. No code path in the R75 worktree manifest is leased to R76. No wildcard or directory lease is implied.

## Proof and implementation obligations

Implementation records exact receiver identity/structure, member spelling and token/source range, source occurrence, lexical scope, and applicable declared role/impl identities without resolving an unlicensed selection. Proof establishes the source-constructor correspondence, identity preservation, receiver association, owner/scope preservation, and exhaustive coverage for the fixed supported source cases. If an approved rule is found, derive/invert its candidate constraint while preserving every licensed candidate and shared type constraint; otherwise return the exact missing rule as `NO_SAFE_ROLE_SOLVER_SLICE`.

Independent falsifiers: receiver identity changes; member range or spelling is lost; lexical/declaration owner changes; field access is prematurely classified as dispatch; a candidate is omitted; a constraint is justified only by successful solving; or an unrelated ordinary constraint changes.

## Proposed resources and stop conditions

Proposed cap: 2400 seconds, with no R75 carryover: Luna implementation 900 including bounded verification; proof 600; fresh compiler 300; spec 300; integration 300; Astra 0. This is not an active allocation. Exact runtimes, remaining resources, and live leases must be reconciled before activation.

Stop selection work at the first absent semantic rule, source identity/scope gap, omitted candidate, verification failure, dependency/hash drift, or resource boundary. Source projection may continue only if it remains independent and within the exact contract. Do not open another effect-storage packet automatically. Parent/A/B remain OPEN 0→0; R50 remains NOT_ADOPTED.
