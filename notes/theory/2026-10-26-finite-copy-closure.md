# Finite-copy closure obstruction after a level-lowering merge

Status: checked conditional algebraic certificate; primary-reviewed. Native/source application remains open.
Baseline supplied by primary: `9a34b280dd23255f0a6583e30b4adbcc34670787`, branch `yulang3`.
Author: bounded leaf `/root/finite_copy_certificate`, revision 1, 2026-10-26.

## 1. Finding and scope

The proposed cycle is valid in a successful, merge-free Value closure with the
individual operational obligations stated below. Its successor is derived from
the actual directions of one-sided row storage, Function variance and selected
bound copying. The proof does not require symmetric storage of row inequalities.
It also does not require repeatedly extruding one previously rewritten raw pair:
the receiving negative row changes at each iteration.

This is **not yet a source-qualified counterexample** to the original inference
termination claim. A scalar bound graph does not by itself establish the native
Replay fibers, operation histories and queue completion required by the proof.
The certificate therefore leaves those premises explicit. It proves neither
native divergence in the presence of bounded identities/resource errors, nor
failure of source soundness or principality.

The original parent remains `YulangClosure.SourceProblem.InferenceTermination`
in `notes/theory/lean/YulangClosure/Contracts.lean`, namely accessibility of every
supported initial inference state under the actual inference-step relation.
The original source domain and the birth-level SCC authority are unchanged.
`2026-10-26-original-termination-closure.md` already leaves finite demand/copy
ancestry and the concrete whole-state relation open. This result attacks the
proposed low-level ancestry argument; it does not replace the original relation
with an always-enabled abstraction.

## 2. A concrete algebraic seed

Write `F(x,y)` for the Function with Value argument x and Value result y. Fix
inert, closed Effect ports. Initially let A and B have current level 1 and R,C
have current level 0. Perform these operations in order:

1. Admit `F(B,B) <: B`. At target 1 the structural extrusion preserves B;
   the result is the exact lower `F(B,B)` on B.
2. Admit `A <: F(B,B)`. At target 1 the negative structural extrusion preserves
   B; the result is the exact upper `F(B,B)` on A.
3. Positively extrude `F(C,A) <: R`, with this occurrence qualified for
   intrusion. Positive A-copying traverses A's lowers, not its retained high
   upper. Merge its copy into A at settlement. A now has current level 0 and
   still has the exact upper `F(B,B)`. B remains at current level 1.
4. Admit `B <: A`. Since A is lower-level than B, this stores A on **B.upper**
   and replays B's lower `F(B,B)`. It does not lower B and need not add B to
   A.lower.

The required post-seed facts are therefore

```text
level(A) = 0, level(B) = 1,
F(B,B) in lower(B), F(B,B) in upper(A), A in upper(B).
```

This construction is a rule-level seed. The selected source term's generation
order, occurrence identity, origin/receiver Values, same-birth induced-SCC
membership, and actual native arrival at this seed remain unproved here. No
test source or observer was executed by this worker.

The native reason old high structure survives is precise:
`candidate_intrusion.rs:599` (`merge_candidate_rows`) appends both sides of the
copy's bounds to the parent, retains parent storage, then assigns the minimum
of parent/copy levels. It does not recursively re-extrude the parent's existing
Function upper. Positive row extrusion reads only the selected lower side in
`candidate_extrusion.rs:109`.

## 3. The derived cycle

Consider a completed positive extrusion of `F(B,B)` into a low receiver r. It
creates distinct polarity copies N,P of B. Operation-local row memoization is
keyed by `(endpoint, polarity, target)`, so the positive and negative B copies
are distinct. Both are level 0. The negative snapshot includes B's already
installed upper A. Since A is already low, copying that selected bound returns
A itself; therefore `A in upper(N)`.

The returned Function is `F(N,P)`. Its retained rewritten demand installs this
Function on lower(r). The first r is A. Later receivers are preceding negative
copies and have upper A. In the later case, cut replay gives
`F(N,P) <: A`. Extrusion into A now preserves the entire Function because N and
P are already level 0. Thus this demand also installs `F(N,P)` on lower(A).
This unchanged-extrusion step is necessary; ordinary graph transitivity must
not silently stand in for actual dispatch.

Cut with A's retained upper `F(B,B)` gives

```text
F(N,P) <: F(B,B).
```

Function argument contravariance produces `B <: N`. Since B is at 1 and N at
0, the actual row-owner selection stores N on B.upper. B's original lower
`F(B,B)` consequently generates `F(B,B) <: N`. Positive extrusion into this new
low receiver produces another negative B copy N' and positive copy P'. N'
again retains upper A. Fresh allocation makes the row birth ordinal of N'
strictly greater than N's. The notation `N' > N` means birth order, not a
subtyping assertion.

Extrusion adds more facts than these: the negative source link inserts N on
B.lower, the positive source link inserts P on B.upper, and positive copying
can retain other low bounds. None is used as an immediate replaying cut in
the proof. These silent links do not themselves establish the claimed loop.
The loop uses the explicit incoming comparison `B <: N` and its replay.

For a finite successfully completed prefix choose the greatest relevant
negative-copy ordinal. The clauses above demand a strictly greater one.
Equivalently, induction derives relevant negative copies above every natural
bound. Thus this merge-free closed prefix cannot exist with finitely many
negative B copies.

## 4. Exact native owners and what they do not yet prove

| Primitive obligation | Native owner inspected | Established static correspondence / remaining application |
| --- | --- | --- |
| One-sided `B <: N` storage | `candidate_extrusion.rs:1115`, `candidate_apply_value` | Low upper row selects `(B, Negative, N)`. The new Lean theorem also applies the existing `NativeValueStructure.selectBound` definition to levels 1 and 0. |
| Selected negative upper copying | `candidate_extrusion.rs:85`, `:109`, `:126`, `:393` | Low rows return unchanged; side lengths are snapped before the one-sided link; fresh copies are memoized before traversal; `Work::Bound` installs and transports the selected upper. A bound added after the snapshot cannot be inferred on an earlier copy. |
| Function argument polarity | `candidate_extrusion.rs:304`; `lib.rs:14800` | Extrusion flips the argument polarity; Function comparison emits upper argument below lower argument. Effect obligations are additional real children. |
| Rewritten lower installation | `lib.rs:14718`, `:14760`; `candidate_extrusion.rs:1138` | Changed extrusion enqueues the retained rewrite; subsequent unchanged extrusion reaches one-sided insertion and replay. A return from extrusion alone is not completed demand dispatch. |
| Retained raw-pair memo | `lib.rs:14448`, `:15275`, `:15345` | Currentness can skip an already admitted pair. A retained extrusion target is reused rather than freshened, and replacement diagnostic admission preserves it. A new receiver N gives a different raw pair `F(B,B) <: N`; if that pair was already processed, its retained event must postdate N's birth. The formal proof of this historical alternative remains open. |
| Cut replay | `candidate_extrusion.rs:1070`; `candidate_context.rs:3992` | Native Replay enumerates actual bound-origin fibers and suppresses already recorded dependency products. Scalar lower/upper membership alone is insufficient. New-pair or previously-owned continuation coverage must be proved for each used cut. |
| Queue ownership | `candidate_context.rs:4156`, `:4206` | `candidate_replay_bound` uses `provenance=None`; ordinary replay enqueues children and can return `Queued`. It does not recursively settle a child drain before returning. Retained restoration has a different synchronous branch. |
| Function child dispatch | `candidate_context.rs:3505`; `lib.rs:14955` | Port admission retains the swapped/preserved context and scoped metadata before enqueue. Nonzero scoped transformers can reject with `ReceiptMismatch`; the scalar proof does not discharge these guards. |
| Settlement boundary | `lib.rs:14042`, `:14308` | Both ordinary and retained drains call settlement only at their no-current-item/empty-worklist boundary. Pending qualification alone does not immediately merge B's copies. Empty queue during an active Function-admission stage is not such a boundary. |

There is no other production call to `settle_candidate_intrusion` in the source
search performed for this packet; additional occurrences are in tests. This is
a static call-site observation, not a whole native execution theorem.

### Why pending qualification is not automatically a counter-objection

If an induction establishes that every finite successful prefix after the seed
still owns one unfinished cycle consequence, the first later settlement point
is unreachable. The later B copies may then be qualified and pending without
ever lowering B. Consequently it is unnecessarily strong to assume all later
occurrences are unqualified.

Conversely, one cannot assume B stays high in an arbitrary final state which
has undergone additional settlements. The correct application is a
**first-subsequent-settlement** argument: take the finite prefix just before
that first settlement, prove its operational closure, and apply the certificate.
The native completion/fiber argument establishing that prefix's closure is
still missing. This note does not infer it merely from an empty worklist or a
`completed` relation memo.

## 5. Lean artifact and exact premises

`notes/theory/lean/YulangClosure/FiniteCopyClosure.lean` imports the existing
`NativeValueStructure` module. It introduces a Value-only `Snapshot` and a
`Closed` proposition with ten separate primitive obligations: cut, Function
argument projection, one-sided row-upper admission, unchanged low-Function
installation, positive extrusion, copied upper retention, rewritten lower
installation, both copy levels, and chronological freshness.

`Snapshot.copy b a receiver n p` records an operation whose selected negative
snapshot already contained the low upper a. This avoids the invalid inference
that a newly added parent upper must occur on every historical copy. `Seed`
contains exactly the five post-seed facts in section 2.

The authored declarations are:

| Fully qualified theorem, under `YulangClosure.FiniteCopyClosure` | Statement |
| --- | --- |
| `initial_copy` | `Closed s` and `Seed s a b` produce an anchored negative copy. |
| `anchored_copy_produces_newer` | The same primitive laws turn any anchored negative copy n into an anchored copy with greater birth ordinal. This is proved through the cycle, not assumed in `Closed`. |
| `arbitrarily_large_anchored_copy` | For every natural bound there is an anchored negative copy at least that large. |
| `no_finite_copy_closure` | `Closed s`, `Seed s a b`, and a finite bound on recorded negative B copies imply `False`. |
| `native_high_to_low_selects_parent_upper` | The existing native selector chooses the upper side of the high parent for a level-1/level-0 row comparison. |

This is a conditional fixed-point obstruction with a nontrivial local
derivation. `Closed` is not claimed as an established native instance and is
not an alternative definition of actual native success. Merely checking the
Lean file does not prove the source/native application. The represented cases
are row/Function Value ports at levels 0 and 1. Full Effect/context metadata,
records, tuples, variants, publication, FreshUse, rollback and source syntax
are not represented.

No Lean/Lake process, native solver, test or build was run by this worker;
the primary owns verification. Toolchain files inspected specify Lean 4.35.0
and no external packages. All five theorem types and complete transitive axiom
audits remain to be checked by the primary. No project axiom, `sorry`, `admit`
or checker bypass was introduced. That source inspection is not an axiom audit.

## 6. Required application, owners and falsifiers

1. **Native closure at the first settlement frontier — native/proof owner.**
   Construct one successful uncancelled history after the seed, including
   scalar entries, nonempty retained fibers, Replay dependency products,
   currentness/retained-rewrite cases, Function child admission, and outstanding
   queue/frame ownership. Show every `Closed` clause needed by the cycle at
   the first proposed settlement. A missing fiber, discarded continuation,
   allowed contextual rejection, earlier merge, or reused birth identity
   defeats this application and must be reported at its actual owner.
2. **Source seed and approved qualification — source/semantic owner.**
   Derive the source's actual types, levels, ordered constraints, relevant
   origin/receiver Values and birth-level induced-SCC qualification, with one
   coherent contextual and scoped history. The quoted source's 20-second
   observation is a primary-reported finite observation, not this derivation.
3. **Unbounded algorithm versus Rust — original-machine owner.**
   Identify the original mathematical transition system in which allocations
   succeed with unbounded identities. A Rust call may end with
   `IdentityExhausted`, `ReceiptMismatch`, or another actual availability
   failure. Excluding finite successful quiescence does not exclude such
   termination. The authoritative abnormal-path policy explicitly permits
   safe resource failure; this note changes no accepted source envelope.

Until these owners provide the bridges, the original whole termination gate
remains OPEN. No production implementation or approved semantics is changed.

## 7. Dependency fingerprints

SHA-256 at static inspection:

```text
80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61  crates/yu-solver/src/candidate_extrusion.rs
475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97  crates/yu-solver/src/candidate_intrusion.rs
57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e  crates/yu-solver/src/candidate_context.rs
ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07  crates/yu-solver/src/lib.rs
81060e17ad37f2e4a47edb7ed2829bea6820438bf3d4db0e4de8d113fd9497fc  notes/theory/lean/YulangClosure/NativeValueStructure.lean
```

Only this note, the new Lean module, and the exact assigned handoff were written.
No existing compiler/proof source, shared status, dependency, configuration,
Git state, pending question, or test expectation was edited.

## 8. Primary verification and disposition

The primary independently read the five theorem bodies, their primitive
premises, the one-sided selector and the native owners listed above. The
selected-copy record is necessary: the proof does not infer that later-added
parent bounds existed in an earlier copy snapshot. `freshAfterReceiver` is an
explicit chronological allocation premise; it is not derived from subtyping.
The conclusion correctly concerns finite successful closure and excludes no
resource-error termination. The certificate is accepted at this conditional
scope only.

The pinned Lean 4.35.0 / Lake 5.0.0-src+eb6cafb focused module build and all five
public theorem type/axiom checks exited 0. The complete originating-module
audit in `lean/AuditFiniteCopyClosure.lean` also exited 0, checking all 36 theorem
declarations, including generated theorems. Dependencies were only `propext` and
`Quot.sound`; no project
axiom or `sorryAx` was accepted. The full default project was not built for
this leaf addition, and the library root was not changed.

Verification receipts (raw output retained in scratch, not committed):

- Focused checker log SHA-256:
  `7fa4aea7db6ba013be57f71f537dd8a0448aa5b480b6ddb9f69c19c684d27f63`.
- Complete-origin audit log SHA-256:
  `8726433e332621ea9a30b4849288bc72505eb160b5efadfc92e6705f9df51b94`;
  exit 0, 1.780 seconds.

A separate primary observation stopped after 12,001 trace events with 83 Value
rows; its explicit observer cutoff is not solver completion or divergence.
That prefix is not an instance of the `Closed` premise. The original whole
termination gate remains open after this checked result.
