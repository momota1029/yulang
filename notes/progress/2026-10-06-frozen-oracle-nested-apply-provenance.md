# Frozen infer nested Apply provenance capture

Date: 2026-10-06
Status: frozen, independently compiler-referee-reviewed capture and regression-reviewed structural join; no semantic authority
Yulang3 baseline: `b9d8627b2f828c9fe3b1f573e5de39f3e90710c4`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Lease: this note only

## Objective, method and governing scope

Capture a completed historical inference result for the exact nested ordinary
application `my repeated f x = f (f x)`, then delimit what the existing current
shadow inventory test can compare. The user's experimental shadow/differential
authorization permits structural evidence; Oracle semantics are explicitly
non-authoritative. This follows `rules/design-authority.md` §§Authority order,
Approval and implementation gate; `rules/research-lab.md` §§One semantic
baseline, explicit dependency invalidation, Evidence quality and stopping
unproductive loops; and `rules/git-concurrency.md` §Disjoint-file mode.
No selected language meaning is revised.

The prior recipe is
`2026-10-06-shadow-live-infer-application-provenance-join.md` §Capture and
verification, with the temporary helper retained at
`/tmp/yulang2-oracle-capture/crates/yulang/examples/capture_application_provenance.rs`.
This capture calls the same public old loader once in a new scratch copy,
filters provenance to the empty root module path, traces returned poly identity,
and separately parses the same prelude-prefixed bytes for argument boundaries.
The root Scheme is neither displayed nor compared.

## Exact input and observed result

Input is 25 UTF-8 bytes, no trailing LF, SHA-256
`8aff5712f28ad70b36f65b89c806c9a56155a3e31fddefcb443d4d6cb2081ee6`.
Hex: `6d7920726570656174656420662078203d2066202866207829`.

The loader returned successfully: `errors=[]`, `file_count=41`. Its provenance
table contains exactly two entries whose application file is the empty root
path. Both report `origin: Source`, `module: ModuleId(0)` and refer to actual
`App` nodes. This is a root-source count, not a count of every application in
the embedded standard library.

| Root incidence | Old App node | Old callee / argument node | Recorded App span | Recorded callee span | Normalized App / callee |
| --- | --- | --- | --- | --- | --- |
| Outer | `ExprId(8398)` | `8394` / `8397` | `38..45` | `38..39` | `18..25` / `18..19` |
| Inner | `ExprId(8397)` | `8395` / `8396` | `41..44` | `41..42` | `21..24` / `21..22` |

Normalization subtracts exactly 20 bytes, the public
`IMPLICIT_PRELUDE_IMPORT = "use std::prelude::*\n"` from old
`crates/yulang/src/source/mod.rs:50`. This entrypoint uses
`source_with_implicit_prelude_only`, not the 29-byte prelude-plus-module prefix;
see `source/mod.rs:1394`, `source/std_sources.rs:277`, `:317`, `:528`.
Normalized source slices are respectively `f (f x)`, `f`, `f x`, `f`.

The outer callee is `Var(RefId(3452))`; the inner callee is
`Var(RefId(3453))`. Both resolve to `DefId(2286)`, label `f`, and both targets
are `Def::Arg`. This identity is separately checked within the same returned
arena against the root definition `repeated`, `DefId(2285)`:

```text
Lambda ExprId(8400), PatId(1937) = Var(DefId(2286)), label f
  body ExprId(8399)
Lambda ExprId(8399), PatId(1938) = Var(DefId(2287)), label x
  body ExprId(8398)
```

The inner argument is `Var(RefId(3454))`, resolving to `DefId(2287)`, label
`x`. The outer argument is directly the inner App `ExprId(8397)`; old poly IR
has no intervening Group node here. Equality of callee targets is an arena
identity observation, not an inference from equal labels.

### Argument spans: capture versus reconstruction

`ApplicationProvenance` stores App and callee spans only; it has no argument
span field (`crates/infer/src/lowering/application_provenance.rs:42`). The
separate frozen parser dump of the same prefixed bytes gives:

| Argument | Frozen CST envelope | Normalized envelope | Underlying old argument expression span |
| --- | --- | --- | --- |
| Outer | `ApplyML` child `Expr/Paren`, `40..45` | `20..25`, `(f x)` | Inner App's captured `41..44`, normalized `21..24` |
| Inner | `ApplyML` child `Expr`, `43..44` | `23..24`, `x` | No separate poly argument-span field |

The lowering route explicitly takes `arg.text_range()` as its argument boundary
and sends it to `make_source_app` (`lowering/expr/tail.rs:108`). Thus the CST
boundaries are source-side reconstruction supported by the inspected route,
not direct argument-span fields extracted from the returned inference result.
The outer parentheses account for the envelope/inner-App difference. No
interval subtraction is used to guess an argument span.

## Current shadow comparison and exact gap

At the pinned Yulang3 baseline,
`crates/yu-core/tests/shadow_raw_structural_inventory.rs` used the identical
source literal and checked two direct call incidences with one binder and
distinct use identities. Its common loop checked each incidence against its
retained Apply/callee `Use` and exact pending rows. After the old capture, the
primary extended that test with a focused cross-version source-provenance join.
The regression review of that delta passed with no findings; the focused core
test ran and passed three tests. The earlier raw-inventory implementation
review/checks are recorded in
`2026-10-06-shadow-raw-structural-inventory.md` §Verification.

`RawStructuralArena::from_artifact` retains existing identities and forms;
`Skeleton::resolved_call_incidences` follows only an immediate retained `Use`.
The current builder retains a `Form::Group` for the outer argument, unlike old
poly IR. Source ownership and the same-formal/two-use relationship therefore
have a structural comparison seam, while raw node identity or a literal
old/new tree equality is inappropriate.

The new test normalizes the reported old App/callee ranges by the 20-byte
prelude and checks the current raw arena retains the same two source ranges,
direct callee binder, and distinct use identities. It also checks the current
outer Group around the inner Apply rather than demanding old/current tree
equality. The assertion is limited to current identities plus captured old
source spans; it does not link old RefIds to current UseIds or compare inferred
types/effects. The old App's direct argument edge and frozen runtime identities
remain capture observations, not fields cross-checked against current HIR.

## Evidence class, independence and omissions

This is a bounded historical execution characterization on one source and one
frozen implementation, not a theorem or a source acceptance guarantee. The
precise premise is that the named public loader at the pinned old commit runs
with its embedded standard-library prefix and returns the observed poly arena
and sparse provenance table. Successful inference and the absence of reported
errors describe this historical run only.

The old loader and current shadow inventory are distinct compiler mechanisms;
no transition rules were supplied by a toy checker. The separate old parser
and old lowering share parser definitions, prefix bytes and source-range
conventions, so their agreement is not an independent source-semantics oracle.
The callee/formal identity check also shares the returned arena/resolver with
the old App capture. The new test joins source spans and checks the current
same-binder/two-use pattern, but does not map old `RefId`/`DefId` values to
current artifact IDs. No successor call-view, effects, typed capture, signature licensing,
complete profile/admission, soundness, principality, source adequacy or
production inference result follows.

Coverage: one deterministic input, no seeds or randomized ranges, one loader
invocation and one companion parse. No mutation, LF/trailing-space variant,
self-application, recursive, annotated, grouped-callee, import, error-recovery,
or resource-limit case was tried. This is the assigned small witness; no
minimality across the language is claimed. Failure conditions were loader
error/panic, compilation failure, missing root ownership, non-App provenance,
wrong/missing formal identity, timeout or observed memory pressure. There was
no retry or broadened search.

## Independent review

A compiler referee reviewed the frozen capture note against the pinned source
routes. No findings remained. The review independently checked source bytes,
prelude length, normalized span arithmetic, the absence of an argument-span
field in `ApplicationProvenance`, and the current Group/old erased-parentheses
distinction. Loader counts, `errors=[]`, runtime ExprId/RefId/DefId values,
resource figures, and retained stdout/helper hashes remain reported capture
observations rather than independently reproduced output.

A regression auditor reviewed the later current-test delta and found no
regression or overclaim. It verified exact source/range normalization, current
per-call direct-use identity joins, the Group difference, and feature gating.
The focused test-only change passed three tests. This review does not
independently authenticate the old runtime capture or add semantic authority.

## Command, resources and dependencies

Scratch root: `/tmp/yulang2-nested-apply-provenance-20261006`. One copy of the
clean pinned checkout was made; the previous scratch target cache was copied
into its isolated target directory. The original target cache and original checkout were not
written. Direct frozen source dependencies and `Cargo.lock` were byte-equal in
the new scratch before/after capture. The original checkout remained clean at
the pinned SHA.

Run once from that scratch root:

```sh
/usr/bin/time -v -o capture.time timeout --kill-after=15s 600s env \
  RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 \
  CARGO_TARGET_DIR=/tmp/yulang2-nested-apply-provenance-20261006/target \
  cargo run --locked --offline -p yulang --example capture_nested_apply_provenance \
  > capture.stdout 2> capture.stderr
```

Exit 0; one Cargo process, two-job cap, one incremental build. Cargo reported
2.22 seconds; timed command wall time 3.80 seconds, user CPU 1.84 seconds,
system CPU 0.20 seconds, maximum RSS 258,424 KiB, zero swaps. This RSS is the
`time -v` maximum process observation, not an aggregate concurrent-memory
measurement. No Cargo/rustc was active at the resource check; approximately
25 GiB RAM was available. Copy preparation time and aggregate peak memory were
not measured. Frozen `infer` emitted 105 pre-existing warnings; no warning fix
was within this lease. No benchmark, broad suite or second build ran.

Retained scratch stdout SHA-256:
`4d1b0563cd7d1764b16f142b753e745318e68db9f378745a651cb31296823314`.
Helper SHA-256:
`a32dbfd388041ed5151c74f7f2a8b98c660e7c69540d605281be3c9f9e8e7889`.

Direct current dependencies were rechecked byte-for-byte against baseline:

| Path | SHA-256 |
| --- | --- |
| `crates/yu-core/src/shadow_derivation.rs` | `c04bfffc414631455dc765c83208d4dbcee9099715f43f5eb7d22bcb875c90a2` |
| `crates/yu-hir/src/shadow.rs` | `4b0914f3a29a5ca47fd912de23ebad690d57908ad628e5dc392b0d8b6df811ac` |
| `crates/yu-core/tests/shadow_raw_structural_inventory.rs` | `be01b7c8c30b21a20c4c6a142b9db19d5b4f84db061107b870198ceae7eff01a` |
| `crates/yu-core/tests/shadow_legacy_application_provenance.rs` | `6445b21a9a5287cfa12b6a78e01169fe62f68ddb9067e8659b3f54a9cc36d160` |
| Prior capture note | `2ba131e4e086d33a519185dec2e64331e5c5f57700ff2ebdab0e3d2ee538792e` |

## Reproducible temporary helper

This helper was added only to the new scratch, without manifest changes:

```rust
use yulang::source::{build_poly_from_source_text_with_embedded_std, IMPLICIT_PRELUDE_IMPORT};
use poly::expr::{Def, Expr, Pat};
fn main() {
    let source = "my repeated f x = f (f x)";
    println!("source={:?} bytes={} final_lf={} prefix_bytes={}", source, source.len(), source.ends_with('\n'), IMPLICIT_PRELUDE_IMPORT.len());
    let output = build_poly_from_source_text_with_embedded_std("capture_nested.yu", source).expect("frozen source build");
    println!("errors={:?} file_count={}", output.errors, output.file_count);
    let mut entries = output.application_provenance.iter().filter(|(_, p)| p.application_span.file.segments.is_empty()).collect::<Vec<_>>();
    entries.sort_by_key(|(_, p)| p.application_span.range.start);
    println!("root_source_owned_applications={}", entries.len());
    for (id, p) in entries {
        println!("app={:?} provenance={:?}", id, p);
        if let Expr::App(callee, argument) = output.arena.expr(id) {
            println!("callee={:?} argument={:?} argument_is_app={}", callee, argument, matches!(output.arena.expr(*argument), Expr::App(_, _)));
            if let Expr::Var(reference) = output.arena.expr(*callee) {
                let target = output.arena.ref_target(*reference);
                println!("callee_ref={:?} target={:?} target_label={:?} target_is_arg={}", reference, target, target.and_then(|d| output.labels.def_label(d)), target.is_some_and(|d| matches!(output.arena.defs.get(d), Some(Def::Arg))));
            }
            if let Expr::Var(reference) = output.arena.expr(*argument) {
                let target = output.arena.ref_target(*reference);
                println!("argument_ref={:?} target={:?} target_label={:?}", reference, target, target.and_then(|d| output.labels.def_label(d)));
            }
        } else { panic!("source-owned provenance must target App"); }
    }
    for (id, label) in output.labels.def_labels() {
        if label == "repeated" {
            println!("root_def={:?} label={}", id, label);
            if let Some(Def::Let { body: Some(body), .. }) = output.arena.defs.get(id) {
                let mut cursor = *body;
                while let Expr::Lambda(pat, next) = output.arena.expr(cursor) {
                    if let Pat::Var(formal) = output.arena.pat(*pat) {
                        println!("lambda={:?} pattern={:?} formal={:?} formal_label={:?} body={:?}", cursor, pat, formal, output.labels.def_label(*formal), next);
                    }
                    cursor = *next;
                }
            }
        }
    }
    let prefixed = format!("{}{}", IMPLICIT_PRELUDE_IMPORT, source);
    let tree = rowan::SyntaxNode::<parser::sink::YulangLanguage>::new_root(parser::parse_module_to_green(&prefixed));
    for node in tree.descendants() {
        if u32::from(node.text_range().start()) >= IMPLICIT_PRELUDE_IMPORT.len() as u32 {
            println!("cst_kind={:?} range={:?} text={:?}", node.kind(), node.text_range(), node.text().to_string());
        }
    }
}
```

## Commit packet

The nested source-provenance test now joins the frozen App/callee spans with
current source positions and existing lexical identities. Remaining follow-up
would cover broader source shapes or a successor type/effect judgment, with
its own independently justified premise and review gates.

- Exact leased repository path: `notes/progress/2026-10-06-frozen-oracle-nested-apply-provenance.md`.
- Baseline: `b9d8627b2f828c9fe3b1f573e5de39f3e90710c4`.
- Dependency hash changes: none; original Frozen Oracle clean/pinned, direct
  current inputs equal the baseline.
- Claim/review: frozen historical characterization, independently
  compiler-referee-reviewed; the current structural test delta is independently
  regression-reviewed. Old runtime values remain reported capture observations.
- Checks: one bounded old loader/CST capture, source bytes/hash, formal identity,
  dependency equality and original-checkout status; source-route review;
  focused current shadow test (3 passed), rustfmt and diff checks.
- Proposed commit message: `research: capture frozen nested Apply source provenance`.
- Shared deltas left for primary/curator: optionally link this characterization
  from `tasks/current.md`; record the exact nested-source comparison gap.
  No theory-status promotion, design/index or question-board change is proposed.
