# Sprint: root visibility carrier through LocalSource — R134 rev3

Status: **FROZEN_CANDIDATE_FOR_PRE_VERIFICATION_DELTA_REVIEW**; rev1 BLOCKING source-attribution and rev2 BLOCKING package-name findings are preserved. No code lease is active; candidates remain frozen.
Branch: `research/simple-sub-intrusion`; HEAD `9fab033a27390ac12f7553a9d6af11a82ad66e1b`.
The worktree contains frozen R132/R133 candidates and closeouts. R133's one
verification command is exhausted and is never retried by R134.

## Goal and fixed outcome

The broader user goal remains proof-backed Yulang inference/evaluator breadth
and running as much of the unchanged Yulang2 Web demo as the current language
supports. R134 targets only the concrete source-carrier obstruction revealed
by R133's exact identity-only fixture. It does not change the fixture or its
three expected values, does not add syntax or visibility semantics, and does
not claim general polymorphic soundness or whole-demo compatibility.

Frozen source: `web/playground/examples/yulang2-identity-island.yu`, 210 bytes,
SHA-256 `b4d68db12c1845f23b5c8a3231249952470868d22d9489a8590270a57de77a3f`.
Expected selected-definition observations remain `int_identity -> 7`,
`bool_identity -> true`, `string_identity -> "ok"`.

R133's one authorized check built WASM and Vite, then the first identity
selected-definition call failed with `candidate lowering unavailable:
StructuralProjection` from the `lower_module_with_local_source` preparation
path, before `CandidateInference::solve`. The exact attribution to root
visibility is a **source-based hypothesis** pending a focused witness: root
admission in `module.rs::plain_binding_header` accepts `my`, `our`, and `pub`,
while `local_source.rs::body` currently requires `MyKw`. The unchanged fixture
has three `our` result definitions. R134 must establish or falsify this exact
rejection chain before implementation.

## Authority boundary and invariant

Owner-admitted top-level visibility already belongs to ordinary root
admission/HIR. R134 may carry that admitted visibility into local-source body
projection solely to verify that the authentic root header matches the
already-admitted `HirVisibility` and extract the same `BindingBody` child.

Preserve the original header, visibility, binding identity, parameters, body
syntax/source keys, occurrence identity, root schedule and all downstream
behavior. Add no import/export lookup rule, new visibility class, source
acceptance rule, syntax, runtime mode, API or production authority. Local
bindings inside braced/indented blocks remain private-only; `our` or `pub`
local declarations stay unsupported. Malformed or mismatched headers must
remain rejected. A visibility-sensitive body/carrier dependency or newly
required source owner stops this contract for review.

## Exact R134 question and falsifiers

The R133 smoke error is wrapped by `prepare` around
`lower_module_with_local_source`, before `CandidateInference::solve`. Source
has two distinct routes that can reach the binding `body` helper, and the R133
error variant alone does not identify which route or root failed:

- In the opt-in local-source path, `lower_plan` calls `local_source::form`
  directly for an admitted binding (`module.rs::lower_plan`); `form` then
  calls `body` for that binding (`local_source.rs::form`).
- In the ordinary-carrier path, root HIR items are lowered first, then
  `form_ordinary` runs and invokes `form`, which can also reach `body`
  (`module.rs` post-lowering carrier loops).

Establish which route is active for the exact fixture and which first root or
operation returns `StructuralProjection`. Then test whether the `our` header
check in `body` is that first rejection; do not infer it from the shared error
variant alone. Reconcile `body`'s shared caller `Builder::block`, which
independently rejects non-private local bindings.

The proposed repair is admissible only if tests/evidence show:

1. Existing root admission remains the sole authority for `my`/`our`/`pub`;
   the source carrier checks the actual header against that admitted value.
2. Root body extraction yields the exact pre-existing body child without
   changing parameters, root visibility, source identity/provenance, order or
   consumer construction.
3. Local block bindings remain private-only and malformed/mismatched headers
   remain rejected.
4. The exact 210-byte fixture passes focused HIR/candidate CLI execution and
   the one authorized Web/WASM smoke, producing all three original values.
5. Existing candidate proof limitations and all parent gates remain OPEN.

Falsifiers: the first error is elsewhere; visibility affects body formation;
root provenance or IDs change; malformed root headers become admitted; local
non-private bindings start working; candidate conflicts/contamination occur;
or any value differs. No workaround that rewrites `our` to `my`, drops a
result, changes the exact fixture, or repeats R133's check is allowed.

## Frozen baseline and direct pins

| Path | SHA-256 |
|---|---|
| `crates/yu-hir/src/module/local_source.rs` | `d7c02fb7ba08fa389229064c6c12504a237fbd15687858431738cb2b2939a5ce` |
| `crates/yu-hir/src/module.rs` | `153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907` |
| `crates/yu-hir/src/shadow.rs` | `ae5f40a9b1d34d08938eb23b8bc3d1756411d146b5c83ba73b7294f5d332a654` |
| `crates/yu-hir/src/source_identity.rs` | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` |
| `crates/yu-hir/src/lib.rs` | `8f6e2b688418dbdb4e2c551cbd9b7b58c809623d492f2da6f7d29cc64189d8d8` |
| `crates/yu-hir/tests/conditional_local_source.rs` | `1a271192071dc3c690080802c69ad63246f631f7a9039b4200c40fbffb139c40` |
| `tools/inference-playground/src/lib.rs` | `a0769f77feac552304f0516b0742637f51660c0bb8bf9391d18ae0f9de5e2473` |
| `tools/inference-playground/src/runtime/program.rs` | `28748da0458da92b9d1190b250bbb84bdecc6643718eacbca95a04f5d6c9aa0d` |
| `tools/inference-playground/src/runtime/machine.rs` | `4fb918732047f61184bc8f89b829bde68a8d1e6649a24d02640ec14500ae0acd` |
| `apps/yulang-wasm/src/lib.rs` | `2fc9feb353b3130c4efc888270cec14cba8b2bbcc2fca03d3780c676e0468f8a` |
| `apps/yulang-wasm/Cargo.toml` | `c00101fa1b063622a9826a7971add7396e0f73b614d408f2e962a006799966f6` |
| identity fixture | `b4d68db12c1845f23b5c8a3231249952470868d22d9489a8590270a57de77a3f` |
| Web smoke harness | `099ffecad2ffd944ee84ba5a024f99c13c9a8aaa3a736390fedb23b2a6638c05` |

Any mismatch or newly required owner stops before code. Generated ignored
`web/playground/dist/` and `web/playground/src/wasm/` from R133 remain generated
outputs, not source inputs or authorized edits.

## Lanes and exact leases

**Constructive source proof, prover (Sol/high), maximum 420 seconds:** write
only `notes/theory/2026-10-20-r134-root-visibility-carrier.md` and
`tasks/agent-loop/inbox/20261020-r134-proof.md`. Prove the concrete rejection
chain and the proposed visibility-parametric body projection invariant using
the current source constructors/consumer, or return a counterexample. State
all premises and omitted cases; use R133 only conditionally for identity
consumer steps. No commands, implementation edits or Git.

**Implementation, implementer (Luna/high), maximum 360 seconds after a CLEAN
prospective review:** write only `crates/yu-hir/src/module/local_source.rs`,
`tools/inference-playground/tests/cli_demo_identity.rs`, and
`tasks/agent-loop/inbox/20261020-r134-implementation.md`. Add focused in-file
HIR coverage for root `my`/`our`/`pub` carriers and retained private-only local
bindings; add a CLI regression using the exact identity fixture and checking
the three selected values. No tests/builds/formatters/compiler/CLI/Git during
implementation.

Fresh final compiler/source and spec/regression reviewers, maximum 240 seconds
combined, inspect all changed paths and preserved scope. No producer
self-review. After frozen handoffs and CLEAN reviews, Luna may run once each,
serially and within the 480-second verification allocation:

```sh
timeout 120s cargo test -q -p yu-hir root_visibility_carrier
timeout 120s cargo test -q -p yu-playground --test cli_demo_identity
timeout 240s npm --prefix web/playground run check
```

The tests are bounded structural and exact-fragment evidence; the Web check
establishes only the three selected values, not whole-demo or theorem closure.
Stop at the first failed command. No retry or alternate invocation in R134.

## Resources and stop conditions

Fresh R134 cap: **1,800 seconds** — inventory 120, prospective review 120,
proof 420, implementation 360, final review 240, verification 480, closeout
60. Zero Astra; one heavy process maximum. R133's approximately 537 unused
seconds do not transfer. Preserve the separate R132 360-second UNKNOWN
implementation reservation, R114 360-second unreconciled reservation and
R133 180-second UNKNOWN implementation reservation.

Stop on non-CLEAN pre-review, failed rejection-chain attribution, owner-pin
mismatch, visibility-dependent formation, provenance/identity change, any
local visibility relaxation, changed source/oracle, new owner/semantics,
non-CLEAN final review, first verification failure or exhausted stage. Luna
alone owns exact leases, closeout, staging, commit and non-forced push.

## Rev3 command correction

The R134 rev2 final regression reviewer found that the HIR package is named
`yu-hir`, so its first test command's `-p yulang-hir` target was invalid. Rev3
changes only that package selector to `-p yu-hir`; all candidate paths, source,
oracles, proof scope and other commands remain byte-identical. This correction
must receive a CLEAN delta review before any verification command runs.
