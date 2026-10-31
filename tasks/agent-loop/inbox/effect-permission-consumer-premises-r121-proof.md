# R121 consumer premises — proof audit, revision 1

Outcome: **conditional premise reduction; `NO_AUTHENTICATED_LOCAL_TRACE`**. Existing R119 `indexed_read_member` already expresses the required finite membership consequence. It requires no first-match search. Its successful indexed-read premise has not been authenticated for the actual Rust record/vector/index/family, and the existing candidate theorem remains CONSTRUCTED / UNCHECKED. No new theorem or semantic model is supplied. Independent review PENDING.

Sprint `EFFECT-PERMISSION-CONSUMER-PREMISES/20261102-R121`; contract SHA-256 `0544d0f08716328e016906544e4b3b9f4c556c7fb71a4a123d1f04f6cba419c6`. Assignment `/root/r121_proof`, sole author, no descendants. Current-session identity and exact lease are recorded by the primary in `current.json`; this lane writes only this handoff. Requested/observed model and effort UNKNOWN. Fixed bound ≤300 seconds. This audit grants no Git, compiler, scheduling, review or production authority.

## Sources, authority and frozen dependencies

Read root AGENTS and the preserved proof-closure contract, goal-driven sprint rules, the Lean proof skill and both source/execution references, handoff protocol, exact R121 contract/current assignment, frozen source handoff, existing R119/R118 candidates and proof handoffs, and the exact parent definitions below. The fixed packet forbids Lean/Lake/checker execution, so the skill's normal verification procedure remains a future owner task; no environment was inspected or created.

Authoritative policy is `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2, SHA-256 `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`, together with `2026-10-11-yulang-inference-top-level-principles.md` §1.1. Concrete identity includes resolved arguments. Permission, actual inflow and residual remain distinct. An otherwise compatible `[signal, write]` argument is not rejected merely because the subtraction permission is `[signal]`; write remains outward. The accepted algorithm and source language are unchanged.

Original parent `YulangClosure.SourceProblem.InferenceSoundness`, `Contracts.lean:128`, SHA-256 `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`, is the proposition definition:

```text
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

`docs/yulang-whole-proof-closure-ja.md` §§1,3–4, SHA-256 `17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5`, retains all accepted source constructors, original lexical scope and one shared witness. Its opening birth-level SCC correction remains effective. This research integration manuscript is not semantic authority for new implementation behavior.

Fresh `sha256sum` matched these direct dependency bytes:

| Dependency | SHA-256 |
| --- | --- |
| R121 source handoff `effect-permission-consumer-premises-r121-source.md` | `b016a0249755607b698c20c0516821b1119d01dd44f7daf1c4d5d9cf18fb09f1` |
| `PermissionMemberWitnessR119.lean` | `f0d3d9c51a270b19f24acaf6edecec0885dda1fd1b2718db88dd4105db6a343f` |
| R119 proof handoff `effect-permission-member-witness-r119-proof.md` | `cd7f488faa9bc3ae5670fa3dfc3ab050a19e0ec8f772a5003f0125bf6b891c6d` |
| `NativePermissionDecoderR118.lean` | `2ebb7797c683b2bbf51d746f89d58d9abc4be66b5520fe6c0f4c6007a70d82ab` |
| R118 proof handoff `effect-permission-decoder-to-lean-r118-proof.md` | `fa4fcadbf028846469897aa815df4f58a9daeff58740f04891efde651edf6e79` |
| `ComputationPermissionEntryR39.lean` | `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e` |
| `InternalPermissionIncidenceR45.lean` | `9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f` |
| `SuppressionPermissionR116.lean` | `2aed350468964d90d8d83714177fff77d477e3df0846ae23150194bd76270e3a` |

Source baseline `d177c46ec61fcadd70a3d587c2f8934f6bc91f46` and R120 composed receiver SHA-256 `108a50b5ed8aaa4813fa42ec4372d72dab4f67d4a158e7f551b8672ca3b9f470` are inherited frozen-source identities, not freshly reconstructed here. No Rust source, patch or immutable Git blob was read by this lane.

## Exact existing declaration and smallest application

At `PermissionMemberWitnessR119.lean:57`, the written source declaration is:

```lean
theorem indexed_read_member (xs : List Id) (member : Nat) (family : Id)
    (read : xs[member]? = some family) : family ∈ xs
```

Its fully qualified name is `YulangClosure.PermissionMemberWitnessR119.indexed_read_member`. The surrounding section declares `{Id : Type} [DecidableEq Id]`; the exact elaborated implicit-parameter list has not been printed. Its source proof performs list/index induction: the empty-list case contradicts `read`, index zero identifies the head, and a successor index reduces to the tail. There is no search, decoder, permission constructor, pointer, owner or source-language premise in this written statement. No membership fact is assumed.

For already authenticated Lean values `permission : ComputationPermissionEntryR39.Permission Id`, `k : Nat` and `providerFamily : Id`, the only substantive local premise needed is:

```text
read : permission.concrete[k]? = some providerFamily
```

The existing declaration can be used directly as the expression:

```lean
YulangClosure.PermissionMemberWitnessR119.indexed_read_member
  permission.concrete k providerFamily read
```

This is a proposed specialization of existing source, not a newly checked expression. Its conclusion is `providerFamily ∈ permission.concrete`. It needs neither `orderedSearch` nor `search_index_read`; it does not need `same_record_search_read`, R118 `readFamily`/`readPermission`, native endpoint coordinates, registration uniqueness, R39 `prepare`/`permissionFor`, or R45 `extract` to derive this local list consequence. Those source facts can still be necessary for the full consumer/source theorem. If the available Lean read names a separate `consumedFamily`, an independently established `consumedFamily = providerFamily` is additionally needed to rewrite the read; the actual frozen Rust guard compares the indexed result directly with the captured provider family, so its intended interpretation can target `providerFamily` directly.

`same_record_search_read` has the stronger conclusion joining searched and consumed families and uses a successful `orderedSearch` premise. `selected_retained_member` also packages native/retained reads. Neither is needed to obtain membership alone. R118 `decode_member` instead inverts its candidate recursive `contains`/any transcription; R121's actual indexed-read expression does not by itself establish that older `decode` success equation. Reusing `indexed_read_member` avoids inventing another equivalent theorem or assuming that equation.

## Source premise and precise missing interpretation

The frozen R121 source handoff derives, under ordinary Rust operation meanings and control continuing beyond the entire rejecting guard:

```text
m.and_then(|k| p.concrete.get(k)) = Some(f)
```

Here `p` is the actual captured permission record, `m` the actual optional concrete-member index, and `f` the full captured provider-family reference. This implies that `m = Some(k)` for an in-range actual index and that the indexed element compares equal to `f`. An earlier true disjunct short circuits and returns `None`, so a skipped read cannot supply this premise. The successful read alone does not establish success of the whole guard or containing consumer. The separate pointer guard and unique registration selection bind the selected inventory record to this captured record; payload equality cannot replace that pointer test.

**First missing premise for this local application:** established correspondence must identify this very Rust permission/vector with `permission.concrete`, identify its actual `usize` with the same Lean `k`, identify the full resolved `SourceEffectId` value compared with `f` with the same Lean `providerFamily`, and justify that this successful Rust `Option`/`get`/reference-value-equality evaluation yields the exact Lean equation `permission.concrete[k]? = some providerFamily`. The read equation on an arbitrarily chosen equal-looking model vector is insufficient. Record identity, stable borrow/state association, vector order/length/elements and the actual family equality must be covered at their operational owners. No such interpretation is defined or established by the inspected R118/R119 modules or frozen source handoff.

This is a missing application premise, not a proposed `FaithfulDecoder` axiom, assumed relation or new semantics. Writing it as a theorem hypothesis would preserve the gap. R121 therefore ends **`NO_AUTHENTICATED_LOCAL_TRACE`**. The primary/private source correspondence owner must supply concrete operation/identity interpretation evidence under an authorized packet before this direct application can become a source result.

## Discriminators and parent application

- `[4,9,9]`, provider 9: both indices 1 and 2 satisfy the indexed value equation, so either supplies the same membership conclusion. First search selects 1; changing 1 to 2 refutes an inference from successful local read to first occurrence. It neither refutes membership nor proves that a mutated witness is reachable through safe capture. The distinction survives even though the Lean membership proposition forgets which occurrence supplied it.
- `None`, out-of-range, empty vectors and an in-range unequal family do not yield the successful indexed-read premise. In `[4,9,9]`, index 0 reads 4 and cannot supply membership of 9 by this read. No case has been executed or kernel-evaluated here.
- A different record with an equal vector can prove a Lean membership fact about that vector, but cannot establish the actual consumer's same-record pointer relation. Registration 7 at packed slot 0, permission member 1, native member 0 and full family 9 remain separate coordinates. Native reads and all owner/state/batch/operation checks remain additional obligations.
- Full `.position`/projection/request/index transport correspondence still matters to the stronger first-match/full trace obligation `R119-AUTHENTICATE-MEMBER-TRACE-1`. The reduced dependency applies only to the local membership conclusion and retires none of that stronger claim.

The direct conditional consequence reaches the membership-shaped conclusion of `YulangClosure.SuppressionPermissionR116.selected_endpoint_member`; it does not instantiate its R39 constructor equations, `SelectedSource`, `operationMatch`, or provider-endpoint identity. R39 `Valid` explicitly includes absence of the registration in the PRE-state. POST-state membership cannot establish that absence or reconstruct `Action::FormalEntry` and its original annotation row. R118's written `post_state_is_not_prepare_input` keeps this obstruction explicit and remains unchecked.

To transport an established local membership fact to an R45 certificate, `YulangClosure.InternalPermissionIncidenceR45.accepted_payload` already gives `out.permission = probe.permission` under the exact `extract e q probe = some out` premise. This additionally needs the actual local permission identified with that same `probe.permission`; R121 supplies neither extraction nor its `OwnerReads`/identity premises. R116 `internal_certificate_member` remains unapplied. R45 extraction, R114 admission transport, R111 compile gate, original `InferenceSoundness`, source/native correspondence, whole effect hygiene and production remain OPEN. No accepted source constructor, shared witness, quantifier or native behavior was restricted.

## Checks, failure evidence and STOP

Actual commands were read-only `cat`, `sed`, `rg`, `sha256sum` and `apply_patch` writing only this leased handoff. All final dependency hashes matched, exit 0. An initial read guessed nonexistent `PermissionStateBindingR118.lean` and `effect-permission-state-binding-r118-proof.md` locators and exited 1; focused file discovery corrected them to the actual R118 paths above. Batched output truncation was followed by focused reads of the material authority/parent declarations. These were locator/output issues, not Lean diagnostics.

Pinned metadata was read: `leanprover/lean4:v4.35.0`, library `YulangClosure`, project arguments `-j1 -M1024`, manifest packages `[]`. No toolchain/version command or executable checker was invoked. Actual Lean version, elaborated/printed theorem types, goals/diagnostics, kernel acceptance and **all complete axiom lists are NOT RUN / UNKNOWN**. Embedded R118/R119 `#check` and `#print axioms` lines are future commands, not observed receipts. No new Lean declaration, project axiom, `sorry`, bypass or root import was written.

Resource bound ≤300 seconds; actual CPU/RSS/exact elapsed telemetry UNKNOWN, no resource probe. No compiler/build/test, environment/cache/worktree/scratch/temp/generated output, source reconstruction, Git operation, background process or descendant. Only this handoff was written; existing Lean/source/shared records were unchanged. Writes **STOPPED** after this revision. Return its frozen SHA-256 externally, then primary obtains fresh independent review and decides integration.

Next evidence request under unchanged `R119-AUTHENTICATE-MEMBER-TRACE-1`: authenticate the actual same-record indexed-read interpretation described above, with duplicate index 1→2, different-record and absent/out-of-range discriminators; keep first-match/full transport and R39 PRE reconstruction separate. Repeating list-membership lemmas cannot supply the missing evidence.
