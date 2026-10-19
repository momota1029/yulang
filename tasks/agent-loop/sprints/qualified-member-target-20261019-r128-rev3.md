# R128 rev3 — qualified member target join T

Status: CANDIDATE rev3; read-only delta review only. Rev1 and rev2 pre-specs found major findings, repaired here; no proof or implementation grant exists. Proof and implementation remain unassigned until CLEAN review and Luna's exact lane grants.

Branch `research/simple-sub-intrusion`; baseline `8bad5d05f17b433b2c5164b91248462de3f7a6fe` (R127 closeout pushed). This advances method/role source correspondence after R127's §21 native payload entry and keeps an executable HIR evidence path in view. It makes no method-selection decision and changes no compiler behavior.

## Fixed outcome

Trace the unchanged R119 source's `SecondInt::second` qualified head, together with its two ordinary application edges, through the actual syntax, HIR LocalSource resolver, declaration identity and solver candidate gate. Identify the concrete target producer/consumer seam, or establish a more immediate source-formation obstruction. Apply the result to `R119-TARGET-JOIN-1` only. Keep the authentic member producer M and full candidate/runtime admission A separate and OPEN.

The exact original source is 148 UTF-8 bytes, has no final LF, and has SHA-256 `fb54857e70924c178842692d7cce1a9c35b7c2a55bceab78710889b913d7dfcb`:

```yu
role SecondInt {
    my second: int -> int -> int
}
impl int: SecondInt {
    my second self selected = selected
}
my answer = SecondInt::second 1 2
```

The separate structural control is:

```yu
act SecondInt:
    our second: int -> int -> int
my answer = SecondInt::second 1 2
```

The Act control is parsed independently. It can show the established operation-namespace path; it is not a method target and supplies no identity comparable to an opaque identity from the role/impl artifact.

## Proof and test obligations

### Proof lane — 480 seconds

Construct a finite constructor/data-flow account for the exact source:

1. Establish the authentic `PathTail`, family/member token structure and the two application-tail source edges from the parser constructors and original source keys.
2. Follow `LocalSourceBuilder::expression` from the original `OperatorChain`: distinguish its initial path tail from its reversed ordinary Apply construction; identify the retained Apply operands and their source ownership without inferring method meaning from spelling or order.
3. Follow `resolve_operation` through the effect and operation namespaces populated by source annotation. Name the exact declaration identity this route can produce and the declaration kinds it cannot consume.
4. Follow the caller in `yu-solver/src/shadow_apply.rs::solve_mode`: identify the exact HirItem/SourceRootId conditions under which `hir.local_source_for` yields the `answer` LocalSource and invokes `candidate_source::preflight`. Then follow the resulting `LocalSourceForm::Operation` to its operation-declaration consumer. For this exact source, establish whether the caller conditions are met, or state the earliest unmet condition. If invoked, establish the head-specific unresolved-operation rejection. Keep it separate from later whole-module `hir.errors()` admission and from any candidate path that is not reached. Do not describe a source-code conditional as an observed runtime failure; the structural test does not execute this solver gate.
5. Apply the result to R119-TARGET-JOIN-1. Keep method target join T, authentic member producer M, complete admission A, R85 adoption, and all parent/A-B obligations distinct and OPEN.

The separate Act control may support a structural contrast only. Do not compare opaque identities across parses. The falsifier is an existing authenticated path in these pinned owners that maps this original role implementation member to its ordinary executable target; also falsify if the two ordinary Apply edges or original source provenance are lost/reordered, or if a failure is assigned to a gate that the execution path never reaches.

Proof output: `notes/theory/2026-10-19-r128-qualified-member-target.md` and `tasks/agent-loop/inbox/20261019-r128-proof.md`.

### Implementation lane — 180 seconds

Add one isolated source-structure test to `crates/yu-hir/src/tests/shadow_method_role_source.rs`, preserving every existing assertion. It must use the exact original role/impl fixture, inspect its original `answer` carrier if available, and report same-artifact source keys, retained `PathTail`/operation carrier, declaration-resolution form, and both ordinary Apply edges/operands. Include the independently parsed Act control only to distinguish its operation-namespace route; never compare cross-parse opaque IDs. If an earlier carrier/formation obstruction prevents the intended observation, record that obstruction without deleting declarations or fabricating a root. No production edit, semantic change, fixture/golden/diagnostic expectation change, or public method-execution claim.

Implementation output: the test above and `tasks/agent-loop/inbox/20261019-r128-implementation.md`.

## Authority, breadth and limits

Governing authority: user goal in `tasks/agent-loop/current.json`; `rules/design-authority.md`; charter §§21 and 24; top-level inference principles; unchanged Draft R85 offer. R119 and R123 are evidence, not semantic authority. This packet does not adopt R85 lookup semantics or authorize an implementation of method dispatch.

The broad goal remains proof-backed inference/evaluator with breadth and depth: rotate across all six effect-hygiene fronts, advance method/role syntax with source correspondence, and keep ordinary/effectful source execution runnable early. The existing six-front status map remains in R84/R85 receipts. R128 advances only T and an HIR structural observation; it proves no effect-hygiene parent and no method execution. Proposed next rotation after R128: receiver-permission expiry after continuation resumption with public execution evidence (R129), subject to a fresh boundary review. Do not return to open-ended effect storage/fiber accounting.

Original Simple-sub/evaluator A/B claims, quantifiers, supported source domain and adoption gates remain unchanged and OPEN. R119 M/T/A, R85 adoption, and all six effect-hygiene parents remain OPEN. Conditional data flow, parser association, structural test success, an earlier Role/Impl error, or a same-spelled Act operation do not close them.

## Pinned inputs at baseline `8bad5d05f17b433b2c5164b91248462de3f7a6fe`

| Input | SHA-256 |
|---|---|
| `notes/progress/2026-10-19-r119-closeout.md` | `3da7d16c7919250b6080dffabfc501ef09ae1ca5928135a38be57819e6ae6afd` |
| `notes/theory/2026-10-19-r119-member-producer-feasibility.md` | `8f5ac5abe7098d384c57f48e2d73b95c01aba4d3aca8c73c43a2a33d29ef4e7d` |
| `notes/theory/2026-10-19-r123-method-annotation-source.md` | `782282c048b7b119829fe71960e438acb2c4dfd99d933b52723027fb3d25ad4a` |
| `rules/design-authority.md` | `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `crates/yu-syntax/src/full_parse.rs` | `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8` |
| `crates/yu-syntax/src/expression/operator_chain.rs` | `81db2aec4774f2cd1ddc12b64fd9206cf41cdf3eee00ed740676ffc6d7fc5669` |
| `crates/yu-syntax/src/expression/tails/fixed_access.rs` | `9e88d7ce18d8bd2d3c3bfa6fbdd6cac7e37032a21fedc35774c71597ff7a21bd` |
| `crates/yu-syntax/src/expression/tails/delimited_tail.rs` | `349fe2335e04a68da7d07803f2dd2eb185887d07bf8c9475ba09af089a76a2cf` |
| `crates/yu-hir/src/module.rs` | `153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907` |
| `crates/yu-hir/src/lib.rs` | `8f6e2b688418dbdb4e2c551cbd9b7b58c809623d492f2da6f7d29cc64189d8d8` |
| `crates/yu-hir/src/module/local_source.rs` | `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786` |
| `crates/yu-hir/src/module/source_annotation.rs` | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |
| `crates/yu-hir/src/source_identity.rs` | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` |
| `crates/yu-hir/src/tests/shadow_method_role_source.rs` | `e7a332e65d7c4e7f252e8d04cc57b1d0d5fa3fd416c16a8522c6880b834840a1` |
| `crates/yu-solver/src/candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` |
| `crates/yu-solver/src/shadow_apply.rs` | `838d862dd34fe2b2bd70c5d92c5ce9af0aa98f10f8b6a8eddf313ae798686543` |
| `crates/yu-solver/src/candidate_context.rs` | `002b9d86e26cfda6fdf094ea4d161501849a7127d55c2d147d408a781b9fd28d` |
| `rules/testing.md` | `829eb0c6b6b10db902f0329e3117351b92dba9ca1480ef5722ccd6d2fabbb524` |

## Fixed resource budget and gates

Rev3 delta: pin the test registration owner `crates/yu-hir/src/lib.rs` and align the implementation lane heading with its 180-second allocation. The allocation is rebalanced within the existing 1,500-second cap: pre-spec 240 (rev1 120 charged conservatively, rev2 delta 60 charged, rev3 delta 60 reserved), with closeout reduced from 120 to 60; proof 480, implementation 180, final reviews 240, verification up to 120, inventory 180. The sum remains 1,500 seconds. No Astra allocation, borrowing, reset, background work, or inherited UNKNOWN lease/resource release. The delta reviewer has read-only access to the frozen rev3 contract and pinned inputs, cap 60 seconds, and may report mismatches only; no producer starts before the CLEAN result and Luna's separate grant.

After proof and implementation both stop, freeze all outputs and assign fresh independent compiler/source, spec/authority, and regression review (80 seconds each). Only if all three are CLEAN, verify exactly once:

```sh
cargo test -p yu-hir --lib tests::shadow_method_role_source::qualified_member_head_routes_through_operation_namespace_without_target_join -- --exact
```

The full registered name includes `tests::shadow_method_role_source`, per `crates/yu-hir/src/lib.rs` test-module registration, and `--exact` selects only this new test. The complete test-registration owner is pinned above and the implementation grant is capped at its allocated 180 seconds. No test/build/CLI/probe/formatter/Git run is authorized before that gate. Any dependency/pin mismatch, earlier source formation that makes the planned test unavailable, semantic authority issue, material proof omission, or resource inconsistency stops R128 at that boundary and returns the exact evidence to Luna. Luna alone integrates, reviews the complete outbound range and pushes coherent reviewed work non-forcibly.
