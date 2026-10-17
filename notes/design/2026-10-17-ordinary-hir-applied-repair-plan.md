# Ordinary HIR applied-conformance repair plan

Status: Luna implementation plan for independent pre-code architecture review;
not a new language decision. Sprint `ordinary-hir-applied-conformance-repair-20261017`
rev1 (`05c07691781bbf737c901bc5ca514268a36404d5bf79a446e4953aaaca6c0f39`),
candidate baseline `4f4dcb7b9`. Parent theorem and all original quantifiers,
source domain and source/native obligations remain unchanged; original
conditions closed: 0.

## Fixed authority and proof result

The accepted source grammar and diagnostic contract are the adopted ordinary
HIR successor rev4, SHA-256
`2e61e2acb1a8981bb78592accc48207a24a5cc4c75278e100f63eb960acfeea3`. Its
resource clause is superseded only by the adopted output-sensitive correction,
SHA-256 `e8b53a773675ba54f0cb5dcc4d62a993e8dd16954e0c92c58fdfc80c620d411e`:
projection work/storage is `O(V+E+R)`, with `R` the physical descendant
`HirErrorId` references stored across flat Apply lists. Public HIR, grammar,
errors, ordering, IDs, and source identity behavior do not change.

The frozen proof/source packet contains seven repair invariants and falsifiers
at `notes/theory/2026-10-17-ordinary-hir-applied-repair-invariants.md`
(`1f3afae18e36ca0abf5a9be1fbf2d1220fad0836a0cce3c370e6cce15a027a28`) and its
handoff (`7bd7cfe427f498c88bab2fab71ae1f24b4ab7f30c24552bbd2030404dcbdf6c3`).
They do not prove an original theorem premise. The prior applied compiler review
is receipt `9f576d7f6362f87ae21d01d997dc7418c529aade689d7eafbd22d78b5cf239a6`.

## One implementation outcome

Repair all seven findings as a single coherent candidate:

1. Preserve `causal_errors` on admission refusal and keep the original gate,
   recovery check and fallback ahead of operand resolution.
2. Reject comma-bearing `CallTail` and Group shapes from their actual direct
   tail/parenthesized source nodes before resolving any operand.
3. Stage newly observed operand diagnostics, then emit them at the existing
   semantic-error seam after the retained duplicate-definition event; bind
   final dense IDs before assembling Apply lists.
4. Recompute `EvaluationClass` from each final canonical binding value after
   replacement, including its parameter-Lambda prefix.
5. Carry exact source nodes (or their parse-owned `SourceNodeKey`) alongside
   association construction. Keep public `HirExpr` and its existing callers
   unchanged. `ChainParser::value`, nested collection, and
   `structural_continuation` must produce the provenance for the same retained
   nodes they construct; the continuation owns its actual tail node. Establish
   shape/path agreement by construction. No `(kind, range)` lookup, independent
   second association walk, or spelling/range identity reconstruction.
6. Store the owning `items` index when admitting a body; validate item kind and
   root identity, then finalize that slot once. No per-admission scan from the
   start of the module.
7. Correct grouped fixtures to preserve their authentic unresolved-name
   diagnostics and check exact parse-owned keys, Group/Apply constructors and
   distinct callee/argument nodes.

For item 5, the proposed seam is a crate-private owned association product
containing the existing `HirExpr` plus a private source-provenance tree/sequence
created by the same `ChainParser` operations. It must retain a one-to-one
constructor/path relation for every node admitted by the ordinary projection;
it is not a public field added to `HirExpr`. Existing `associate_chain_owned`
callers keep their current product/behavior through an adapter, while ordinary
admission consumes the provenance-bearing variant. The architect must confirm
that this is constructible without duplicating or cloning whole subtrees and
without a changed public API. If it is not, stop before edits and return the
smallest exact owner/API boundary.

## Feasibility, accounting and publication gates

The provenance product adds at most constant metadata per visited retained
node, hence `O(V)` storage within `O(V+E+R)`. Association itself currently
allocates recursive `Vec`s; inspect and account for those paths as part of the
`lib.rs` change. Avoid claiming fallible allocation where standard collection
growth remains infallible. The implementation must not publish a partial HIR
or source identity stage on failure. Preserve checked child/count/byte/ordinal
arithmetic and reserve all projection-owned destinations before publication.
Apply lists are each built once by ordered child concatenation; Group forwards
the child aggregate without cloning it. Keep `R` counts and allocation bytes in
the candidate receipt.

Pre-code architect review is limited to: authentic provenance feasibility,
public-surface preservation, association/error-list allocation implications,
preflight and diagnostic staging, linear owning-item finalization, checked
reservations and failure atomicity. A CLEAN result is not theorem proof or
independent implementation review. Luna records adjudication and only then
starts the implementer.

## Exact sequence, leases and evidence

Plan author cap: 90s; this file and
`tasks/agent-loop/inbox/20261017-ordinary-hir-applied-repair.md` are the exact
plan leases. Proposed fresh architect cap: 120s, read-only on this frozen plan,
handoff, source pins, and adopted contracts. No code or test edits before CLEAN
review and Luna adjudication.

After that gate, proposed Luna/high implementation cap remains 1110s and the
exact sequential writer lease expands to:

- `crates/yu-hir/src/lib.rs` — the private construction-owned provenance seam;
- `crates/yu-hir/src/module.rs`;
- `crates/yu-hir/src/source_identity.rs`;
- `crates/yu-hir/src/shadow.rs`;
- `crates/yu-hir/tests/ordinary_application_admission.rs`;
- `crates/yu-solver/tests/research_accepted_call_vertical.rs`;
- `tasks/agent-loop/inbox/20261017-ordinary-hir-applied-repair.md`.

Current-input pins from the failed candidate and proof packet:

```text
lib.rs                                                  5bdcb7c0df022da919cef5402c62dc1c7baf0700a4d06e526a608cbd7db21464
module.rs                                               b4f89fe7c5dc8a3f4260fbe3dd2b173546e07385fbd8dbb38275f3625217127f
source_identity.rs                                      7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3
shadow.rs                                               460c813cb0d2e21565df011b1d816abbc2b180cef13797a1b7b453e9ee413f66
ordinary_application_admission.rs                      38b822bc801c0538878cc5fb3f929f55dee784e2377f4bc75f03679ea9872492
research_accepted_call_vertical.rs                     9c3dea05d11c49bae09520d5f6fe27430f1706185232daf2cf8e8d801a42d71a
ordinary repair invariants                              1f3afae18e36ca0abf5a9be1fbf2d1220fad0836a0cce3c370e6cce15a027a28
proof/source handoff                                    7bd7cfe427f498c88bab2fab71ae1f24b4ab7f30c24552bbd2030404dcbdf6c3
```

Hashes in the sprint's original `5fbceb68d` table are historical baseline
blobs and are not current implementation inputs. The three inherited UNKNOWN
leases remain quarantined. Resource cap is unchanged at 2760s: coordination
120 charged, proof/source 240 charged, plan 90, architect 120, implementation
1110, applied reviews 480, pre/post regression 240, Cargo 240, reserve 120.
The proof lane's unknown elapsed time is conservatively charged at its full
240s reservation. The plan, architect, and implementation authors/reviewers
are sequential; the implementer requires a fresh active acknowledgment.

After implementation STOP/freeze, obtain fresh applied compiler (180s), spec
(120s), and architect (180s) reviews, then regression pre-run review (120s).
Only after CLEAN adjudication may Luna run each of the contract's two Cargo
commands once, sequentially, at most 120s each. Obtain regression post-run
review (120s). A known CI formatting failure is reported separately from
new-code compilation/test results. No retries or changed expectations are
implied.

The vertical can show only existing ordinary HIR/source identity and
feature-gated candidate propagation observations. Standard Apply/Group
`ConstraintBatch::collect[_mode]`, semantic Call, source T/native adequacy,
F1/FK1, N-Transport, soundness, principality and termination remain OPEN.
