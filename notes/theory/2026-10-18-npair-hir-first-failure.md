# NPAIR source-entry HIR refusal: exact observable boundary and unresolved producer

Assignment `NPAIR-HIR-FIRST-FAILURE-20261018`, revision 1. Author
`/root/hir_first_failure_proof`; no descendants. Requested Sol/high; observed
model/effort UNKNOWN. Candidate source/native audit, pending independent review.
Sprint `npair-source-admission-correspondence-20261018`, contract revision 1,
SHA-256 `fdbc808bafb8d32df8f86701f41923fbaaf25de91764fdaf65429aa02da6ed25`.

## Parent application

Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN with all
original quantifiers and source-domain obligations, including independent F1/FK1.
Original conditions genuinely discharged: **0**. The adopted nonempty
concrete-only negative formal row remains the implementation target. No change
to generation, accumulation, propagation, levels, extrusion, qualifying
intrusion, generalization, provider witnesses or residual lineages follows.

The existing HIR correspondence proof applies only after authentic supported
CST formation and successful HIR construction. Its conditional preflight
obstruction cannot be substituted for the earlier HIR refusal observed in the
actual fixture. This audit reduces the diagnostic uncertainty: the returned
`StructuralProjection` alone does **not** establish source-identity corruption.
It also represents ordinary unsupported source formation at this opt-in API.

## Runtime evidence reused, without a new run

The frozen second-failure receipt
`notes/progress/2026-10-18-npair-source-admission-second-hir-failure.md`
(`215cffccb5458a24d3ddf9fbe11cb04e10fcfd14e5b6e7a026eefd7615f9e930`)
records this exact fixture:

```yu
act ctrl
my receive (f:() -> (() -> [ctrl] int)) = ()
```

The correctly selected regression ran one test and failed at HIR lowering,
before `CandidateInference::solve` or preflight. The earlier operation-bearing
input also failed at that boundary; its complete text is not reproduced by this
receipt, so this audit makes no claim about its exact first failing node.
No source acceptance, source refusal by the new predicate, or producer execution
has been observed for either input.

## Exact source facts and first-producer limitation

1. `module::lower_module_with_local_source:1029` initializes source identity and
   the source-node map, enables `local_source`, and calls ordinary module
   lowering. `lower_module_with_counters:1053` separately creates a red syntax
   root using `SyntaxNode::new_root(parsed.green().clone())`, then calls effect
   declarations before planning/lowering bindings. `source_identity::source_keys:26`
   builds its map by walking `parsed.source_root()`. Whether lookups across those
   two roots match requires the uninspected `ParsedFile`/source-root and syntax
   identity owners. Distinct constructor expressions alone prove no mismatch.
2. The first direct key-dependent error site for a correctly shaped bare effect
   declaration is `source_annotation::declarations:198`, the
   `source_nodes.get(&node)` lookup. Earlier declaration shape/recovery checks
   return `unavailable()`, which is `FormationError::Unsupported` at line102.
   Thus either kind of declaration failure can produce the observed public
   error. The actual first executed failing branch remains **UNKNOWN**.
3. Crucially, `local_source.rs:32-38` explicitly converts
   `FormationError::Unsupported(_)` to `HirAvailabilityError::StructuralProjection`.
   `module::lower_plan:1984-1993` uses `?` on `local_source::form`, so a supported
   binding plan with an unsupported annotation/body also produces the identical
   public error. In contrast, `form_ordinary:499-550` retains unsupported source
   formation as `SourceCarrierOutcome::Unsupported`; these routes cannot be
   conflated. The target uses the opt-in `local_source` route.
4. At the HIR annotation owner, empty type groups are supported
   (`source_annotation::parse_group:505-527`) and a function head may be such a
   group (`parse_type_source:469-479`). The local source body builder also
   explicitly supports empty parenthesized expressions as Unit
   (`local_source::Builder::expression:1054-1065`). Therefore neither unit syntax
   is intrinsically refused by those constructors. These facts assume the
   corresponding CST shapes; they are not text-to-CST evidence.
5. The frozen producer source at `candidate_effect.rs:2333` uses
   `act io` and an annotated `consume` formal with both AAR/RRR concrete negative
   positions, returning `consume`. It is a useful authentic-entry fixture design,
   but the existence of its source and assertions proves no successful runtime
   on this snapshot. It bypasses ordinary solve preflight after formation. Reuse
   its source only while preserving the original target row/descriptor, and
   separately observe the normal solve path.

No exact parser-versus-HIR mismatch is established. No semantic repair follows
from the public error alone. In particular, changing HIR APIs, weakening
annotation shapes, or guessing a parser fix would exceed this evidence.

## Dependency validation boundary

All following actual source hashes matched their frozen governing pins:

| Source owner | SHA-256 |
|---|---|
| `crates/yu-hir/src/module.rs` | `60e91c9a51394b04af42b3ec7c284062b34fcd9faa4ea79c35b4ae58aaf460ed` |
| `crates/yu-hir/src/module/local_source.rs` | `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5` |
| `crates/yu-hir/src/module/source_annotation.rs` | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |
| `crates/yu-hir/src/source_identity.rs` | `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3` |
| `crates/yu-syntax/src/pattern/mod.rs` | `1b608422c93ce0f6947125a9b1ea88314a48b3a5e45030ed23e5154492ad7883` |
| `crates/yu-syntax/src/pattern/delimited.rs` | `9da9ec948775b438a85ca3f27c2805254a4f4171caddb54cabe44e563d017029` |
| `crates/yu-syntax/src/type_expr/delimited.rs` | `db6335a8f6c95bafb72d096fe241201202938c5869fb89a5e3c43758021651b6` |
| `crates/yu-solver/src/candidate_effect.rs` | `9ea9498692bdff12c2a7ebd8546ca2b443a095c0700f3e87ad6c956cc690e212` |

The frozen syntax-read amendment
`notes/progress/2026-10-18-npair-source-admission-failure-read-lease.md`
(`5499f2552bde197fb9410cd33e5d1570fd6344a5dacf94ded132b950991e8773`)
prints the `type_expr/mod.rs` pin as
`2e08a49960cd4010ba39641ae509afb7cf59711f1464d3349f5f6db590ebf01f`.
Actual SHA-256 is
`2e08a49960cd4010ba39641ae509afb7cf59711c1464d3349f5f6db590ebf01f`.
The differing nibble is recorded rather than silently repaired. That owner was
read before validation, an ordering error; all findings dependent on its content
are withheld here. Luna was notified immediately upon validation. Further
reliance requires primary pin reconciliation. This does not invalidate the
matching HIR-owner facts above.

The prior HIR proof `930f99d168ede5e5592a6348ffc4a6f84ccd40c8d78128befaf91297816bafc2`
is reused only under its stated successful-formation premise. The adopted scope
receipt `fe06a42da82d9bc66da133d0266b0fa1133ffbcfb1128100377c715c0ace0d06`
is semantic authority. Source authors are historical/UNKNOWN; prior proof author
is `/root/npair_hir_source_proof`, receipt/adoption author Luna `/root`.

## Minimal next evidence and handoff

TODO `NPAIR-HIR-FIRST-PRODUCER-20261018`, owner Luna / HIR source entry:
preserve the first formation error owner before the lossy conversion, or inspect
the actual failing declaration lookup and authentic CST. The smallest diagnostic
distinction is (a) declaration recovery/shape/key failure before any binding,
(b) formal annotation parse failure, or (c) body formation failure. A temporary
diagnostic probe needs an explicit primary continuation; this worker ran none.
Falsifier for any proposed cause: the first observed branch occurs earlier or
under a different owner. Requested evidence is one exact owner/branch plus CST
shape/source-key result; no accepted-source semantic change is required merely
to observe it.

If a new read owner is necessary, Luna first identifies and pins the actual
`ParsedFile::source_root` implementation and node-identity contract. If the
existing source is malformed, a supported fixture retaining the exact negative
row can repair the test alone. If genuine HIR identity construction is broken,
return a separate owner-local implementation contract and original quantifiers
unchanged. This note grants neither repair.

Checks: source inspection and SHA-256 checks only; no tests, builds, executable
parser probes, compiler edits, Git, external contact, or descendants. Budget
<=300 seconds, charged in full as allocated; actual CPU duration UNKNOWN.
Only this note and the assigned inbox are written. Work stops at dependency
mismatch/first-producer uncertainty and frozen handoff; no further writes after
the final hash receipt. Fresh independent review and integration belong to Luna.
