# Same-birth replay — concrete attribution and publication evidence

BIRTH-LEVEL-REPLAY-20261024/r1. Baseline `7af2bbfe9588128e90f6706f99243e91b63a7ae3`. [Contract](birth-level-replay-20261024.md) SHA-256 `775ba304c72d0263639aefa520fbdce743848c3e02e166687500aec1e59450c2`.

## Objective and method

The user explicitly requested another closure attempt under the approved immutable birth-level induced SCC rule. The original source domain, complete Call/effect evidence, actual extrusion occurrences and parent/copy pairs, publication/use independence and original Simple-sub A/B obligations remain. Implementation is excluded. This attempt follows one concrete source through native allocation, bound replay and publication, replacing the previous abstract factorization-only method.

```text
let top = lambda h.
  let rec f = lambda x. (lambda z.{a=x})(h(f x))
  in {a=succ((f 0).a), b=(f true).a}
in top
```

F has birth2 and H_parameter birth1. The self-call F/F qualifies; F/H does not. The rule does not identify either source Value's birth with every associated type coordinate's current level.

## Results applied to the parent

The [producer trace](../../../notes/theory/2026-10-24-birth-level-replay-intrusion.md) and [publication proof](../../../notes/theory/2026-10-24-birth-level-publication-replay.md) construct:

1. The complete finite scalar reference history through f's publication. The self-call itself creates no copy. Calling h creates R₂≤C₁ and D₁≤J₂. The later D₁≤Z₂ comparison creates no copy. Completing f replays Record(B₂)≤C₁ and creates the actual positive pair (T₁,B₂), with B₂≤T₁ and Record(T₁)≤C₁.
2. The exact freshening map o,B,W,R ↦ o_i,B_i,W_i,R_i while C,T remain shared. Int/Bool uses succeed in that native history; all retained physical bounds are accounted for. This is not asserted to be a complete Yulang source witness.
3. A conditional publication consequence: if B₂=T₁ is legitimately added and consumed before publication, both uses share the same level1 anchor and require Bool≤Int. Authentic qualification and the consumption time are premises, not conclusions of this calculation.
4. Real source checking seeds for the recursive call, h call and wrapper call; BR1's induction showing contextual source support is the union of predecessor support; actual pair retention, `any` activation and transformed-output recapture owners. If the shown scalar projection path is generated, it retains both F/F and F/H support at the new copy.

The final step is not established: dependency support does not itself prove authentic ownership of a later extrusion occurrence by every contributing seed. Full source Call/receipt/effect generation of the displayed contextual path also requires a correspondence proof. Current code has no immutable birth field and is not certified as implementing the new rule. Replacing its qualification predicate alone leaves the support/ownership issue unresolved.

Applied to BL-JOINT, this work fixes a concrete source, actual native pair, source-set transport path and publication map at which the missing obligation must be discharged. It neither proves all qualified equalities preserve original source conclusions nor supplies a complete source-qualified counterexample. No arbitrary solver valuation/client is promoted to required source acceptance. No source domain is narrowed.

## Independent review and adjudication

Reviewer `/root/astra_semantics_review` authored neither target and verified all five frozen hashes (contract and four targets below). It reported **no BLOCKING or MAJOR finding in the stated conditional scope**. It accepted the scalar branches and physical bounds, PR1's complete traversal, PR2's independent uses, PR3's conditional rejection, BR1's inspected source-support calculation and the memo/retention trace. The guide summaries preserve their limited applicability.

The reviewer inspected the October12 association authority and October13 preservation obligation. It confirmed that **BR-ATTR is a genuine correspondence obligation**: definition-root origin for call-demand extrusion does not establish that every ancestor in a replay support set owns every later copy. Primary accepts that adjudication. This is not permission to choose an ownership convention that avoids rejection; the association must be derived under the existing rule.

After producer/reviewer STOP, primary transferred the exact producer-note lease and updated only the two proof headers and the companion's reviewed-versus-integrated status annotation. No mathematical statement or guide changed after review. Reviewed and integrated hashes are distinguished below. No whole-language or current-implementation certification follows.

| Target | Reviewed SHA-256 |
| --- | --- |
| `notes/theory/2026-10-24-birth-level-replay-intrusion.md` | `020da82308ef03c3e5123f03c30bdedd93b1a47fa544be7a4784125275aedc1d` |
| `notes/theory/2026-10-24-birth-level-publication-replay.md` | `a03bd3923a5a32a7c94922596294b6cc2ff6de97b834c6d99dde0b41275d6de3` |
| `docs/yulang-whole-proof-closure-ja.md` | `9f69004dced116b741a3d02eec2529aa35c4f5cb72fe31cce371b3d5edb6d17f` |
| `docs/yulang-proof-index-ja.md` | `b6cfaab5ca4d2772891c04fe2af8c69e1525e0eb4c36ef27a90cf95a9863c445` |

Integrated proof hashes: producer `7bc8ccee1ee9c0a2ce168e5f1687ae76e7794b097cb3d35dc85ccb5d4f717c5b`; publication `0e84e618a077b6f3d138707349fbfe51d09e8ccdd54628ad772640f6c12ea244`. Both guides retain the reviewed hashes.

## Exact remaining evidence

**BR-ATTR:** source Call→bound replay→extrusion transport must derive the actual occurrence(s) owning (T₁,B₂), and each occurrence's origin/receiver. Determine whether F/F is an authentic owner, F/H is the only owner, or another justified occurrence is generated. Do the same for retained-output reuse. Neither the numeric target level nor membership in an accumulated support set answers this question.

**BR-SOURCE / publication:** construct the full original source producer path and complete Call/effect/member evidence, then the actual publication and intrusion consumption action. If F/F ownership and pre-publication consumption are established, the conditional two-use rejection applies; calling it a required-coverage counterexample additionally requires the original source witness or independently established acceptance contract. If only nonqualifying ownership is established, the independent native instances remain in this example, but all-source preservation still needs a general invariant.

If the implementation's `any` consumer applies F/F support that does not own the new occurrence, that is an implementation/source attribution mismatch. It is not a refutation of the user's birth-level semantics. Old cross-level helper rejection remains superseded. Previous cooccurrence clarification and all other full-language obligations remain unchanged.

## Runtime, checks and integration scope

Direction30s, producer190s and independent review80s are sequential reservations, not observed durations. Prior4290s + current300s = **4590s charged**. Requested Astra/medium; observed model/effort/duration UNKNOWN. Maximum one child concurrently. No automatic renewal or unobserved refund. Direction, producer and reviewer returned actual completion/STOP and no-descendant receipts. The reviewer also supplied the end-boundary direction: derive the exact full source recipe, authentic original/reuse occurrence association and equality-consumption time, then apply PR3 only if its premises hold. Final worker status is recorded from live reconciliation in the compact current state. No post-session work is claimed.

Final live reconciliation shows all five existing children completed, with no descendants. Primary proof/document construction ends at this checkpoint; only final static/Git integration and reporting remain.

Only documentation/proof construction and static source inspection are performed. No implementation, tests, builds, compiler execution, probes, manifests, nested CLI, child network/Git or descendants. Static checks cover the15 frozen inputs, final frozen leases, Markdown target existence/fences, compact JSON below16KiB, exact scope and whitespace; these checks are not independent mathematical review.

The intended integration contains exactly seven paths: the two new proofs, two guides, contract, this outcome and current state. The original `/home/momota1029/rust/yulang` checkout and its unknown reservations remain quarantined. The untracked withdrawn question bundle is excluded. Only primary stages the explicit paths and inspects the complete outbound range before a normal push of `research/semantics-proof-20261024`. The containing commit identifies the final integrated snapshot.

**Disposition:** concrete native replay/publication and source-support evidence; whole source preservation, full soundness/principality, combined inference termination and implementation correspondence remain OPEN.
