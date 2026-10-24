# Birth-level native falsifier and signed residual construction

BIRTH-RESIDUAL-CLOSURE-20261024/r1. Baseline `c737e06d5d664fcd9d036f7f45c89444cf2f07b9`. [Contract](birth-residual-closure-20261024.md) SHA256 `530db5ea012a4668d049ac88bd7fdf06c690f20af1aea46250f87efe760874e7`.

## Original objective and progress classification

The user activated the persistent goal 「閉じなさい．」. Its scope is the original complete semantics and type-soundness objective, not a renamed finite native theorem. Implementation remains excluded; only existing Astra children are used. Previous turn: PROGRESS for EC1–EC4's exact finite solution pullback, with the receiving correspondence unchanged. This turn changes the evidence by refuting a concrete proposed shortcut and inspecting an additional retained native demand constructor; it does not declare the whole objective achieved.

## Constructed result and original-parent application

The [native producer](../../../notes/theory/2026-10-24-birth-level-extrusion-redundancy.md) constructs an empty-start original-grammar history:

```text
let top = lambda h.
  let rec f = lambda x. lambda y.
    {first=h x, next=f {a=y}}
  in f
in top
```

The h call creates B₂≤C₁. The same-birth recursive F/F demand itself creates no copy. Recursive completion decomposes the Function argument, producing Record(Y₂)≤B₂ and then Record(Y₂)≤C₁. This creates actual T₁/Y₂. The final cyclic result/store and both subsequent freshenings are finite and explicitly derived. Thus the proposed invariant that every descendant of a same-birth Call is copy-free is REFUTED in native scope. The actual delayed pair's source association is a separate proposition; the selected intrusion semantics is not refuted.

The [primary residual construction](../../../notes/theory/2026-10-24-residual-demand-source-association.md) proves both signed boundary cases: positive replay is b∘d, negative replay is d∘b. The actual native cut and its fresh-coordinate renaming commute. Function Argument swaps the comparison direction, while Record follows the actual matched field. It applies this construction to the new Argument/Swap example.

Source typed-interface composition preserves the supplied boundary incidence (conditional RD3). The original constructor must still produce the source typed map and native bound derivation together (RD4). This is not hidden as an assumed conclusion, nor presented as a completed RG-OWNER theorem.

The newly inspected ScopedDemand record supplies an authentic original_call through whole-Function bound/replay/rewrite paths. Actual FunctionPort consumption clears demand, and Value ExtrusionLink resets the scoped payload. This eliminates the proposed shortcut of reading that field at the scalar delayed copy. The original Derived/Replay/creation evidence remains available; no erased-provenance claim is made.

## Frozen review inputs

| Target | SHA256 |
| --- | --- |
| `notes/theory/2026-10-24-birth-level-extrusion-redundancy.md` | `36f21b9212893f97909829f075eda1a194be9ec86ff071c13de6fd1e33e7de6c` |
| `notes/theory/2026-10-24-residual-demand-source-association.md` | `4a6a920fa46f05a088cdc20708a8b1c4514732a49a90da1930bd391504f2ab62` |
| `docs/yulang-whole-proof-closure-ja.md` | `b5843c388c2b0cd5d69d3d4e2d688bf1da07b6225024fc739198ebf7265dc222` |
| `docs/yulang-proof-index-ja.md` | `93c28dd6afd595cf87803950685d4e49afef89a92182f336d3378e6c950406b4` |

Independent reviewer `/root/astra_semantics_review`, author of neither new proof, checked all five frozen hashes. It accepted the concrete native trace/store/cycle/freshening and INV refutation, typed-cut/renaming RD2, conditional source composition RD3 and its explicit missing bridge RD4, and actual ScopedDemand owner analysis RD5. It returned STOP with no descendants.

**MAJOR, BRD2:** a comparison request does not imply branch execution because constrain may return on a cache hit. Its concrete counterexample has x0.upper=[C,x1], x1.upper=[C] and both x0,x1 at payload level q, with C below q. Direct traversal to C caches the comparison before the later x1→C path. Primary accepts the finding and retracts the unconditional path claim. The repaired lemma requires cache misses for the traversed comparisons and distinguishes requests from branch execution; the original proof then applies under that explicit premise. This generic repaired lemma has no second independent review and is not used to certify the original whole theorem.

**MINOR:** primary added the early-return case to BRD1 and defined RD1's fresh comparison as an actual cache miss. The concrete source trace uses distinct relevant comparisons and needs no change. Producer lease transfer occurred after its actual STOP. Proof headers record exact review/repair scope; guides remain unchanged from frozen inputs.

The end-boundary recommendation is to construct abstract source-indexed inference alongside native erasure. Seed, Function port, bound insertion, replay and extrusion must produce complete typed interface maps and signed boundary evidence together. Their source-law proofs precede correspondence to Rust records. Missing implementation correspondence must not become an artificial prerequisite for a mathematical construction; the desired receiver equation must still be derived rather than declared.

Integrated hashes after the explicit primary repairs: native falsifier `3d447e6982069023d2be69cee3e4cfc208e3f231f92407f34c0d1d8942a44211`; residual construction `c96289283cd427d949160f6973c925d1faec6a4fa43ce8fae3e7ae47dc65936e`. Both guide hashes are unchanged.

## Original outstanding requirements

Original receiving-occurrence RG-OWNER, complete source-to-constraint construction, source-scoped equality lift/publication/use, required A/B and natural inference, full semantics/safety and combined termination remain OPEN. The proof objective remains active. The next action must construct the source-indexed inference operation or otherwise discharge an original obligation, not merely restate RD4.

## Resources and ownership

Prior5190s + direction30/producer190/review80 = **5490s charged**. Requested inherited Astra/medium; observed model/effort/duration UNKNOWN. One child at a time, no descendants or unobserved refund. The producer stopped on its frozen handoff; final review/STOP reconciliation is recorded at integration. Parent goal persistence does not claim any post-session live worker.

Final runtime listing shows all five existing children completed, without descendants. The primary has ended this packet's proof writing and performs final static/Git integration. The active user goal remains active for subsequent original proof work; packet cessation is not goal completion.

No implementation changes, tests, builds, compiler/probes, scratch, child Git/network or nested CLI. Original checkout and unknown external reservations remain quarantined. Protected question files are excluded. Primary owns exact seven-path integration: two new proofs, two guides, contract, this outcome and current state. Static hashes/links/whitespace are document integrity checks, not proof certification.

Whole-goal completion is unproven and is not requested from the goal tool at this milestone.
