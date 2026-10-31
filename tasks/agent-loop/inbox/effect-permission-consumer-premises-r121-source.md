# R121 consumer premises — source handoff, revision 1

Outcome class: **bounded static source evidence / conditional local implication**. The successful consumer guard supplies a same-record indexed family read without requiring that the index be the first match. It does not authenticate a Rust-to-Lean indexed-read relation. Final correspondence disposition: **`NO_AUTHENTICATED_LOCAL_TRACE`**. Independent review PENDING.

Sprint `EFFECT-PERMISSION-CONSUMER-PREMISES/20261102-R121`; contract SHA-256 `0544d0f08716328e016906544e4b3b9f4c556c7fb71a4a123d1f04f6cba419c6`. Assignment `/root/r121_source`, sole author, no descendants. Current-session launch/lease is recorded by the primary in `current.json`. Requested/observed model and effort UNKNOWN. Sole write lease is this handoff. This worker owns no source, shared-record or Git changes.

## Baseline, dependencies and method

Source baseline `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`. The subject receiver is the already authenticated R120 in-memory composition, SHA-256 `108a50b5ed8aaa4813fa42ec4372d72dab4f67d4a158e7f551b8672ca3b9f470`; it was **not reconstructed, saved or executed here**. Fresh `sha256sum` matched all three direct dependencies:

| Frozen R120 handoff | SHA-256 |
| --- | --- |
| `effect-permission-member-trace-r120-source.md` | `0c503338c144eab1feb2fce128227a7409f312b947876cd504f5b1af9fd1050e` |
| `effect-permission-member-trace-r120-proof.md` | `2ce7eaba1483c4f9d5c190977421717125aa55b37c5764ee75b7b834d2da9415` |
| `effect-permission-member-trace-r120-review.md` | `ab6b4daa848196610986f62eebb7b5bbc3a32ba8bbdee0973954785b51ccc50b` |

Read those handoffs and their consumer/borrow excerpts, plus only the immutable baseline receiver lines 1830–1905 and effect lines 462–487 through `git show`. The baseline consumer is explicitly the pre-R117/R119 version: its direct registration indexing is not attributed to the composed consumer. It supplies the unchanged source/formal/row field checks; the changed selection, pointer, packed slot and member read are taken from the authenticated R120 handoff. R120 prints the changed member expression exactly, while abbreviating the adjacent native predicates; this report preserves that distinction and does not invent their omitted spelling. No raw patch, dirty working-tree Rust, synthesized source or additional Lean artifact was read.

Governing sources read: root AGENTS and preserved base, `rules/research-lab.md` and its preserved source-evidence/dependency/checkpoint sections, `rules/design-authority.md`, `rules/git-concurrency.md`, the accepted top-level inference principles, handoff protocol, exact current assignment and R121 contract. The selected task changes no language meaning or parent scope.

## Consumer control flow and separate coordinates

R120 authenticates this composed consumer expression at virtual receiver 1870–1901:

```rust
if *permission_index != self.catch.permission_index
    || !std::ptr::eq(*permission, self.catch.permission)
    // source/registration/row/entry checks
    || self.catch.permission_member_index
        .and_then(|index| self.catch.permission.concrete.get(index))
        != Some(self.catch.provider_family)
    // native view/member, full operation and allowed-family checks
{
    return None;
}
```

The comments above are R120's abbreviations, not executable statements. Its preceding selection filters `self.permissions` by `request.registration`, obtains a first match and rejects a second. Thus successful continuation through this section requires exactly one matching inventory entry. Registration 7 and packed inventory slot 0 may differ; the selected stored slot must equal `catch.permission_index`, not registration. The pointer comparison separately requires the selected inventory permission and the captured permission to be the same record address. Equality of their payloads alone cannot establish this check.

The baseline's preserved adjacent source checks compare the selected permission's registration, source owner, lambda occurrence, annotation position, source row and entry effect with the request. Subsequent formal/recipe checks compare formal registration, owner, lambda, parameter/formal identities and recipe identity. These are additional restrictions on a successful consumer; membership alone cannot discharge them. The composed native-view/member, operation and allowed-family checks remain additional restrictions recorded by R120, without an expanded predicate inventory in its printed consumer excerpt.

Five coordinates must remain distinct: formal registration, packed permission slot, native view/member pair, concrete member index and full resolved family value. Native endpoint member 0 can name family 9 while its position in permission `[4,9,9]` is 1. Neither coordinate equality nor a displayed family name substitutes for full family equality.

Rust `||` evaluates left to right and short circuits under ordinary Rust semantics. An earlier true mismatch skips the member read and immediately returns `None`; such an evaluation supplies no successful-read premise. If control proceeds beyond this entire rejecting guard, every earlier disjunct was false, the indexed-read expression was evaluated, its inequality was false, and every later disjunct was false. Conversely, the indexed-read equality alone does not guarantee guard success or success of the containing function: uniqueness, pointers, slots, source/native fields and later control flow still matter.

## Explicit local derivation

Let `p` name the actual `self.catch.permission` record, `m` its actual optional member index and `f` the actual `self.catch.provider_family` reference at this guard. Assume execution reaches the guard and continues past its rejecting branch under ordinary Rust `Option`, reference comparison and vector indexing meanings. The actual expression then gives:

```text
m.and_then(|k| p.concrete.get(k)) = Some(f).
```

Because the right side is `Some`, `m` must be `Some(k)` for an in-range index `k`; `p.concrete.get(k)` must yield `Some(v)`; and `v` must compare equal to `f` by the actual resolved `SourceEffectId` equality used by the expression. Hence a concrete element of this very vector has that full family value. This is value comparison of element references, not pointer equality of the element references. The distinct record pointer guard binds the uniquely selected inventory record to `p`. The implication is a paper derivation from authenticated expressions and ordinary operation meanings; it is not a checked operational theorem.

No hypothesis about `.position`, first occurrence, absence of an earlier equal member, or how `m` was produced is used in this local derivation. To transfer it to a Lean list proposition still requires an authenticated interpretation of this actual record/vector, length/order/elements, successful `.get(k)`, `usize` index and equality into the same permission list and family in Lean. R120 identifies no such established interpretation. Applying R119's already written `indexed_read_member` would need its actual indexed-read equation on that interpreted list; this lane does not manufacture that equation or certify the unchecked theorem. The proof lane owns its exact minimal-premise audit.

## Discriminators, construction and reachability

- Required duplicate case: permission `[4,9,9]`, provider family 9, captured member index 1. Changing only that field to 2 leaves the indexed family read equal to 9. With all other local checks held satisfied, this local value guard accepts either index. The changed field need not be reachable through safe capture. The smallest duplicate witness is `[9,9]`, changing 0 to 1. Both witnesses refute only the inference “successful local value guard implies first-match index.” They do not refute membership or establish a source attack.
- First-match search contributes a canonical selected occurrence and its exact source construction history. R120 shows `.position` searches the selected permission and direct projection/request copies carry its result and reference. That history supports index 1 on the unmodified `[4,9,9]` path. Authenticating that stronger history needs search and transport correspondence. Local membership needs a successful same-record read and therefore can avoid the first-match premise; the broader trace TODO remains open.
- `None`, an out-of-range index, an empty vector or an in-range different family cannot satisfy the local equality with `Some(f)`. In `[4,9,9]`, index 0 reads 4 and rejects for family 9. An earlier mismatch can prevent these reads from running, but then the rejecting guard does not continue successfully.
- A different permission record with equal payload cannot be substituted solely by value equality: the actual consumer also tests `std::ptr::eq`. Duplicate registration records fail the uniqueness step before this guard. Duplicate family elements in one record are permitted by the source copy and are a separate issue.
- Registration 7 at packed slot 0 after an earlier unannotated/empty-concrete formal is a coordinate discriminator, not an authenticated reachable source program. The baseline constructor retains nonempty concrete rows in order, and its internal lookup borrows `&permission.concrete`. Those are source construction expressions, not PRE-state provenance proofs. Empty annotations remain admitted source cases even though this constructor creates no retained empty-concrete permission.
- R120 capture checks owner/batch/live-state identity and native view/member/full-family identities before witness construction. Consumer success does not reconstruct the earlier `Action::FormalEntry`, its source generation or the R39 PRE-state from a post-state. The slice starting-address comparison in capture does not independently establish slice length or arbitrary provenance; the actual baseline borrow supplies additional textual construction evidence, still uninterpreted in Lean.

There was no behavioral oracle, seed, range enumeration, executed mutation, Rust/Lean run or independent formal library interpretation. This method is complementary premise analysis of a frozen trace; it shares the ordinary Rust operation meanings stated above and inherits the reviewed R120 byte-authentication result. It provides no new independent composition calculation. These boundaries prevent a paper guard discriminator from becoming a whole-language counterexample or correspondence proof.

## Parent application, checks and stopped-writing receipt

Reduced dependency: **the local family-membership consequence does not require first-match correspondence, provided the actual same-record indexed read and its interpretation are authenticated**. Exact remaining blocker: the Rust read/equality/record-to-Lean relation itself is absent, so `NO_AUTHENTICATED_LOCAL_TRACE` remains the result. This does not retire or weaken `R119-AUTHENTICATE-MEMBER-TRACE-1`, R39 PRE-state absence, R45 `OwnerReads`/identity/extraction, R114 transport, original inference soundness/effect hygiene or production gates. All remain OPEN. No source semantics, support restriction or accepted constructor changed.

Actual commands: read-only `cat`, `sed`, `rg`, `sha256sum`, immutable `git show`; `apply_patch` writes only this handoff. Hash commands matched every direct pin; read commands exited 0. Some broad batched reads were truncated, followed by focused complete dependency reads. No compiler/checker/build/test, recomposition, environment/storage probe, cache, temporary/scratch/worktree/mount, Git mutation or descendant. Bound ≤240 seconds; CPU/RSS and exact elapsed telemetry UNKNOWN, no resource telemetry probe. No background process was started. Writes **STOPPED** after this revision; hash is returned externally.

Recommended next action: the assigned Lean lane should audit the existing `indexed_read_member` application using this successful consumer equality, isolate the same-record indexed-read interpretation as the remaining premise, and preserve the stronger trace and parent obligations.

Commit packet: exact leased path `tasks/agent-loop/inbox/effect-permission-consumer-premises-r121-source.md`; baseline `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`; all dependency hashes unchanged as above; independent review PENDING; no executable checks or theorem/axiom receipts; proposed message `research: isolate permission consumer membership premises`; shared-record deltas intentionally left to primary: local membership avoids first-match, same-record indexed-read interpretation still OPEN, duplicate-index guard discriminator retained, no parent or production promotion.
