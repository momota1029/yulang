# R128 proof handoff — revision 2, frozen

Assignment `R128-PROOF-1`; worker `/root/r128_permission_borrow_proof`; sole author, no descendants. Outcome: **kernel-accepted standalone local operational model; source correspondence OPEN; independent review PENDING**. Revision 1 was acknowledged by the primary at SHA-256 `2c19e1db4fd5b112107e27dad07e25419f276765809c4d455061fe88ca227717`; its failure narrative and complete initial stdout remain below as historical evidence. No self-certification or parent closure is claimed.

## Amended authority, dependencies and representation correction

Resumed explicitly under contract r2 `tasks/agent-loop/sprints/effect-permission-borrow-operational-foundation-20261102-r128-r2.md`, SHA-256 `7102e4fedd44aa6d1fd59511043e8655f487f30d5a1b252263d9d7d4852b0803`, manifest r3 `434211f70b380de57c3106e9e995c9465351789820397e5b9a20b8cff69f9d88`. Both actual files were read and freshly SHA-256 matched, exit 0. Exact leases remained the same two outputs. Primary resume allowed ≤120 seconds additional active work and at most two further native checks; no budgets reset.

The initial candidate incorrectly represented a family as a declaration plus argument list. The immutable R128 source handoff and amended contract establish the actual Rust SourceEffectId field inventory as module plus declaration, with no argument field. Revision 2 corrects `Family ModuleKey SourceNodeKey` to exactly `{ module : ModuleKey, declaration : SourceNodeKey }`, over arbitrary opaque key domains; operations quantify explicit `[DecidableEq ModuleKey] [DecidableEq SourceNodeKey]`. Concrete Nat keys occur only in discriminators. Rust arguments remain outside this representation, with any needed interpretation still OPEN. The initial mismatch is preserved here and in historical r1; it is not represented as a tactic-only repair.

Frozen source handoff `tasks/agent-loop/inbox/effect-permission-borrow-operational-foundation-r128-source.md` was read under manifest r3, expected SHA-256 `42c9db25645a5e54146027ff474546cce06048d63e2a4752f8cff3f52f375323`. It pins SourceEffectId owner `d177c46ec61fcadd70a3d587c2f8934f6bc91f46:crates/yu-hir/src/module/source_annotation.rs`, SHA-256 `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f`. No Rust file/blob was opened by this proof lane. This is attachment evidence, not a source-to-model theorem. Original parent/source sections, scope and previous dependency hashes are retained in historical r1 below.

## Accepted declarations, actual checks and full axiom results

Changed Lean path `notes/theory/lean/YulangClosure/PermissionBorrowOperationalFoundationR128.lean`, SHA-256 `2042c8ee50c8123e93857ee0eab9e95c9eab5d47d63a649ff4552568a47507d7`, 13869 bytes; sole import `Std`. No other project module was built or imported. Fully qualified prefix for every name below: `YulangClosure.PermissionBorrowOperationalFoundationR128`.

| Audited theorem | Final complete axiom set |
| --- | --- |
| `step_preserves` | `[propext]` |
| `trace_preserves` | `[propext]` |
| `search_first` | `[propext, Quot.sound]` |
| `indexed_member` | `[propext]` |
| `consumer_exact_member` | `[propext, Quot.sound]` |
| `capture_exact` | `[propext, Quot.sound]` |
| `captured_trace_copy` | `[propext, Quot.sound]` |
| `captured_consumer_original_member` | `[propext, Quot.sound]` |
| `duplicate_discriminator` | `[propext]` |
| `unequal_module_same_declaration` | `[]` |

All exact elaborated types and full #print axioms outputs are in the final invocation block below. Native Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release. Same direct command on all three invocations, from `notes/theory/lean`:

```text
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M768 YulangClosure/PermissionBorrowOperationalFoundationR128.lean
```

| Invocation | Native exit | Measured seconds | Result |
| --- | --- | --- | --- |
| 1, initial contract | 1 | 4.582810527004767 | parser/elaboration failure; recovery sorryAx, invalid |
| 2, resumed r2/r3 | 1 | 0.7150449030013988 | constructor cases exposed 4 vs 5 / 3 vs 4 pattern arity; invalid |
| 3, final allowed | 0 | 0.7536799049994443 | all 10 roots accepted; no warnings or errors |

Total native check time **6.051535335005610 seconds**. Both resumed check slots are exhausted, so no further execution is authorized even though time remains numerically under the ≤175.417189473-second amended total. All subprocesses used explicit 90-second timeout. Full stdout/stderr for each invocation is retained below; wrapper exit 0 never substitutes for native exit. Parser/tactic repairs only beyond authorized family correction: reserved identifier rename; dependent constructor-pattern arities; consumer location substitution before heap-read inversion; capture case reflexivity; concrete discriminator reduction; unused-section-variable/simp cleanup. No hypotheses, conclusions, transition meanings or source scope were changed.

## Model coverage and parent application

For arbitrary opaque identity key types and every finite heap size n, a live token refers to a `Fin n` location and allocation identity. `Step.write` permits update/deletion/replacement only at locations unequal to every live shared token; `Step.borrow` reads a real record with matching allocation and adds a token; `Step.idle` preserves the state. `trace_preserves` inducts over all constructors of `Trace` and derives the unchanged heap read and token membership. Borrow stability is not a supplied local law.

`consumer_exact_member` derives selected-location equality, read of the exact guarded record, matching allocation and full family membership solely from actual `consume = some r`. `capture_exact` derives the first matching read and absence at every smaller index from actual recursive search. `captured_trace_copy` combines actual capture, the live-borrow trace and concrete request field copies to yield the same original/current record, the same copied index and FirstAt result, and actual successful consumption. `captured_consumer_original_member` additionally identifies any successful selected consumer output with the original pre-trace record. Their substantive premises are capture evaluation and permitted Trace (plus consumer success where stated); no membership/indexed-read/first-position/decoder/pointer/simulation law is assumed.

`duplicate_discriminator` checks that two copies of complete family `{module := 0, declaration := 9}` capture index 0, while independent local indexed consumers at 0 and 1 both return the same record; index 1 is not FirstAt. `unequal_module_same_declaration` checks that `{module := 0, declaration := 9}` differs from `{module := 1, declaration := 9}`, and searching `[the first, the second]` for the second yields index 1. Thus membership alone proves no first position, and declaration-only equality is insufficient.

Represented: absent slots, empty/missing-family searches, optional/out-of-range consumer indices, complete module/declaration equality, order/duplicates, arbitrary unrelated heap writes including deletion/replacement, further shared borrows and stutter, exact location/allocation guards and concrete copies. Omitted: token release, resize/relocation, interior mutation, registration uniqueness/packed inventory selection, native view/member, complete source/formal/operation guards, actual machine reachability and Rust simulation. The theorem range is explicitly the interval with live shared borrows; no source feature is removed from the original parent.

The accepted local theorem now replaces the previously unproved model-level stability and consumer implication. Applying it to the original parent still first requires the concrete SAME Rust record/vector/location/family/index operational interpretation and a simulation into these permitted transitions. The primary source/native correspondence owner retains that first missing bridge; the source handoff's eight exact equations are not silently assumed true. `SourceProblem.InferenceSoundness` remains the unchanged forall/existential statement shown in historical r1, with all original source constructors, scopes and shared witnesses.

## Exact residual source equations and owners

Let D interpret complete Rust SourceEffectId values and V_t(p) the original ordered concrete vector in live record p. These proposed names are not defined decoders or new theorem assumptions.

1. **Identity**: `D(a)=D(b) ↔ (a.module==b.module ∧ a.declaration==b.declaration)`, including Arc inner-value/module-key and SourceNodeKey equality; clones preserve D. The local Family pair now has the correct field inventory, but this correspondence remains OPEN.
2. **Publication**: model retained list is exactly `map D(row.concrete)` after actual ordered clone publication, preserving length/order/duplicates and exact record fields. R39 PRE Action/absence and symbolic-helper provenance remain separate source-constructor obligations.
3. **Borrow/heap**: actual full-vector borrow and captured live record referent map to this same finite slot/allocation and complete vector; equal slice starting addresses alone do not establish length/provenance. Actual lifetime/aliasing/mutation/rollback steps simulate Step over the live interval. Rust pointer address equality does not establish allocation history or temporal stability by itself.
4. **Native family**: actual indexed native view/member and full operation guards produce D(f), with faithful usize conversion; coordinate identity never substitutes for family identity.
5. **Search**: actual `.position` on that same vector equals `orderedSearch V_capture(p) D(f)` including least index, None, equality and iterator/index behavior.
6. **Copy**: actual projection/request/reference-inventory copies preserve `(p, optional index, f, packed slot, native view/member)` exactly; model copies do not prove those Rust assignments/ref validity.
7. **Selection/guard**: actual unique registration and packed-index lookup plus current sized-record pointer equality select the same p; additional source/native guards have their own interpretation. Equal payload records do not establish same location.
8. **Read**: actual Option/and_then/get/reference-equality success yields `V_consume(p)[N(k)]? = some D(f)` for the SAME retained optional index and record; conversion, vector bounds/contents and compared full value are authenticated. First-position transport also uses equations 3,5,6; local membership uses the actual read and record interpretation.

Owners: primary's source/native correspondence lane for 1,3–8; source-constructor/proof lane for 2 and R39 PRE witness. With these supplied, `captured_consumer_original_member` gives same-record membership. R45 certificate use further requires actual `extract e q probe = some out`, its OwnerReads/Identity and identification of this record with `probe.permission`; accepted_payload then transports membership to out.permission. R114 transport, original A/B, source/native inference, full effect hygiene, principality/termination and production remain OPEN. No installation/compile action is implied; R111 capped verifier and Cargo 0/1 unchanged.

## Resource and final freeze receipt

No generated `.olean`/cache/project outputs requested, no Lake/helper/build, test, Cargo/compiler, dependency installation, source copy, scratch/temp, Git mutation, shared-state write, child or third-party contact. Direct Std-only source checks were the entire execution surface. Read-only source scan for forbidden declarations/bypasses is reported externally with final hashes. Exact initial assignment wall/CPU/RSS remains UNKNOWN; no telemetry probe or budget reset. Continuation is bounded by the primary's explicit ≤120-second active-work cap. Both allowed resumed checks are consumed. No check/output process or descendant remains. Only these two leased files changed. Writes **STOPPED** after this revision; fresh independent review and integration remain primary-owned.

## Historical revision 1 and immutable execution evidence

The following narrative describes the superseded initial failure and initial incorrect argument-bearing Family. It is preserved for failure history, not as the current representation or current kernel status. The final invocation's printed types/axioms govern current checker evidence.

# R128 proof handoff — revision 1

Assignment `R128-PROOF-1`, worker `/root/r128_permission_borrow_proof`, sole author, no descendants. Requested model/effort inherited from primary; effective runtime model/effort metadata UNKNOWN. Primary NEW_TASK supplies the assignment/activity receipt. Outcome: **constructed local operational candidate; CHECK FAILED; no root closure**. Independent review NOT RUN. Finite lane bound ≤600 seconds; no further proof/check invocation after the first failure under the frozen contract stop condition.

## Authority and source scope

Read root AGENTS, preserved operating map, goal-driven sprint rules, current state/handoff protocol, proof skill with sources/execution references, frozen R128 contract/manifest, R118/R119 written definitions and R120/R121/R127 proof/source handoffs. R128 contract SHA-256 `4f4c71e44ce17a8123a0d4f8bbc4f3e10f253e64d4d3fa0411b4c3059afff451`; manifest r1 SHA-256 `3d067a53f428f18d33b291313e7db6a654ae70271f29af51921cf339d39eb827`; baseline `3f90fa0b741e1365afb3a4108184cec6f487d4da`; immutable Rust baseline inherited `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`. Every non-Rust manifest input was freshly SHA-256 matched (all 16 MATCH, exit 0); Rust working files were not read.

Original sources actually inspected: authoritative annotation-effect-hygiene policy `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2; top-level inference principles §1.1; original preservation manuscript `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3; fixed Value-birth-level correction `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6; whole-proof manuscript §§1,3–4. Research manuscripts do not grant semantic authority. The original reference paper is located by the preservation manuscript at `/home/momota1029/rust/simple-sub-reference-paper.pdf`; that paper was not read in this local fragment packet and supplies no asserted theorem premise here.

Exact original parent at `Contracts.lean:128`, `YulangClosure.SourceProblem.InferenceSoundness`, remains the proposition definition:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

`SourceScopedCoverage`, `PrincipalCoverage`, `NativeCorrespondence`, `InferenceTermination` remain separate. Preserve all supported source constructors, complete Call/effects, lexical scopes, generalization/use and the same shared witness. Annotation permission stays distinct from actual inflow and residual; `[signal,write]` remains admitted at the otherwise compatible `[signal]` argument, with write outward. No source-domain restriction is introduced by this local model.

Direct inspected Lean dependencies (read only; candidate has no project imports): R118 `2ebb7797c683b2bbf51d746f89d58d9abc4be66b5520fe6c0f4c6007a70d82ab`; R119 `f0d3d9c51a270b19f24acaf6edecec0885dda1fd1b2718db88dd4105db6a343f`; Contracts `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`. R120 proof `2ce7eaba1483c4f9d5c190977421717125aa55b37c5764ee75b7b834d2da9415`; R121 proof `c9d331b6b4aa5f25892fe2041821a5c7eb9330241c955b2746a6858ca580b575`; R127 proof `ba7dd374ee88778c6034461fd9ea93aac9cd0e084e53aa2de670143deb4f0e64`. Those previous receipts do not establish checked roots or Rust simulation.

Primary later notified that SourceEffectId ownership needs manifest r2 before source-field reliance. Acknowledged. The generic abstract Family construction makes no Rust field-identity claim; all attachment equations below remain OPEN. No unpinned SourceEffectId source was read.

## Candidate model and represented cases

Sole Lean output is `notes/theory/lean/YulangClosure/PermissionBorrowOperationalFoundationR128.lean`, namespace `YulangClosure.PermissionBorrowOperationalFoundationR128`.

`Family Arg` retains a declaration identity and the entire ordered list of arbitrary complete argument values, under decidable equality. It does not claim that a numeric spelling or projection decodes Rust identity. `Record` contains allocation/owner/state/batch/registration plus the ordered concrete list. `State Arg n` is a finite heap `Fin n → Option (Record Arg)` and explicit shared-borrow tokens carrying location and allocation. Different locations stay distinct even for equal payloads. Allowed transitions: stutter; read an existing record to add a shared token; write/delete/replace any slot only when every live token has a different location. Tokens remain live throughout this interval. There is no release, resize, relocation, use-after-release, interior mutability or whole Rust machine simulation.

Capture reads that slot, recursively searches the ordered list, builds the token and optional member index. `capturedState` registers the token. `copyRequest`/`copyAgain` construct actual field copies. Consumer first checks selected location equals captured location, then allocation identity, then binds the optional index to the actual record read and compares the full family. Registration-unique inventory selection, native view/member, source/formal/operation guards are not represented by this consumer; selected is its input. No assumed membership, FirstAt law, indexed-read equation, faithful decoder or pointer-equality premise is present.

Intended roots: `step_preserves` and `trace_preserves` derive stable heap reads/live tokens by transition induction; `search_first` establishes indexed equality and every earlier index unequal; `consumer_exact_member` inverts the actual consumer; `capture_exact` inverts capture; `captured_trace_copy` joins first capture, live borrow trace and two concrete copies; `captured_consumer_original_member` identifies the successful record with the original; `duplicate_discriminator` separates first capture at 0 from successful local reads at both indices of `[9,9]`. Exact printed elaboration types and axiom results are retained below. Recovery declarations with `sorryAx` are invalid and are not delivered as proofs.

## Actual execution, failure and precise repair handoff

Pinned metadata read: `leanprover/lean4:v4.35.0`, `YulangClosure`, no external packages, project flags `-j1 -M1024` (not used). Read-only `elan which lean` exited 0 and resolved the installed native path; it warned `failed to query latest release, using existing version 'leanprover/lean4:v4.35.0'`. No installation occurred. Native `lean --version` exited 0:

```text
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
```

One direct source check used `-j1 -M768` and a Python subprocess timeout of 90 seconds. Native exit **1**, elapsed **4.582810527004767 seconds**; aggregate checker allowance remaining ≤175.417 seconds, subject to primary reauthorization of the failure stop boundary. The Python wrapper itself exited 0 because it recorded the child failure; the Lean result is unequivocally failure. No Lake/default build/helper: the bundled skill checker builds project modules, prohibited by this contract. No `.olean` option or generated/cache output was requested.

Material first error is reserved binder `at` at line 44, preventing `Step` and then `Trace` from elaborating. Downstream errors expose actual goals: consumer simplification rewrites `selected` to `q.token.location` before using `found`; preserve/normalize the heap-read equation at that location before simplifying. `capture_exact`'s case split has already reduced the heap-read goal to reflexivity; use `rfl` there. Duplicate examples' record/capture equalities lack DecidableEq instances; reduce definitions to reflexivity instead of relying on generic `decide`, or derive the required structural equality instances. `indexed_member` has an unused DecidableEq section variable warning. These are unresolved mechanical repair recommendations, not checked repairs. No explicit `sorry`, `admit`, project axiom or checker bypass was authored, but failed declarations have Lean recovery `sorryAx` and cannot count as evidence.

`search_first` prints axioms `[propext, Quot.sound]`; `indexed_member` prints `[propext]` in this failed file invocation. Every other root prints `sorryAx` (with additional standard axioms where shown). A nonzero whole-file check prevents reporting the artifact as kernel accepted. Complete unedited stdout/stderr follows; it contains every root's #check and #print axioms output.

## Parent application and exact open equations

The candidate would reduce the local borrowed-record obligation to a concrete transition simulation, if repaired and independently reviewed. It does not yet establish that reduction as a checked root and closes no original parent premise. Required source attachment, owned by primary's Rust/native correspondence lane, remains:

1. A representation of the actual permission allocation and selected inventory reference by the SAME `Fin n` slot and allocation identity, including state/batch/owner and valid live borrow; actual finite heap contents map to the complete original record/vector.
2. Exact family equality: interpret every field and resolved argument of the actual SourceEffectId comparison, under manifest r2's owner, by the same `Family Arg` value and full argument interpretation. No erased spelling or integer coordinate substitute.
3. Constructor vector equation: model concrete list equals every element of the retained source `row.concrete.iter().cloned()` copy, with original length, order and duplicate positions. Empty/symbolic-only source admission remains permitted, although no successful retained capture follows there.
4. Borrow equation: actual `concrete: &permission.concrete` denotes this same record/vector allocation and lifetime; capture slice-start-address comparison alone supplies neither full slice length nor provenance. Its successful guard is not assumed to establish this equation.
5. Search equation: actual `.position(|family| family == provider_family)` executes the recursive `orderedSearch` on that exact retained list and returns this same optional usize/index; conversion must preserve bounds and numeric index.
6. Transition equation: every actual mutation/allocation/rollback/copy step between capture and use refines `Step` during the live borrow. In particular no alias can mutate/replace/move/deallocate this selected record; relocation/borrow release cannot be silently omitted from a claimed Rust simulation.
7. Copy equation: actual projection fields, request fields and copied borrowed inventory retain exactly the captured location/allocation/family/member; reference copying is not record-payload copying.
8. Consumer equation: successful unique-registration/packed-index lookup identifies the SAME selected location; successful `std::ptr::eq` and remaining guards map to this location/allocation guard; actual Option/and_then/get/reference-value comparison equals `consume` at this very heap and request. Registration, packed slot, native endpoint member and concrete member remain separate.

Under a repaired checked consumer theorem and these independently established equations, the local conclusion reaches R119's indexed membership shape on the SAME record. R45 certificate transport additionally requires actual `extract e q probe = some out` and exact local permission = `probe.permission`; R45 `accepted_payload` then supplies `out.permission = probe.permission`. R39 PRE constructor `Action::FormalEntry`, original annotation row, absent registration, `prepare` and `permissionFor` remain separately OPEN at source-constructor owner. Post membership cannot reconstruct them. R114 transport, complete native correspondence, original A/B/source soundness/effect hygiene and production remain OPEN. R111 capped verifier/Cargo allowance remains untouched.

## Writes and finite stop

Only the two exact leased paths were written. No scratch/temp/source materialization, dependency install, cache/build/olean, compiler/Cargo/test, Git mutation, child, third-party contact or shared-state write occurred. No verification subprocess remains. CPU/RSS telemetry UNKNOWN; no resource/storage probe. Artifact must remain candidate/unaccepted pending mechanical repair under a versioned stop-condition change, full successful direct audit and fresh independent review. Writes STOPPED after the final handoff update; no descendants or generated leases remain. Frozen Lean artifact SHA-256: `0580a122666185beffb2d97acf7d1f033f7205268e1afcb06e9f07bcc86f3f51`; bytes: 12226. The handoff's own frozen hash is returned externally.

## Complete first invocation evidence

```text
Command: /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M768 YulangClosure/PermissionBorrowOperationalFoundationR128.lean
CWD: notes/theory/lean
Exit: 1
Elapsed seconds: 4.582810527004767
STDOUT:
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:44:29: error: unexpected token 'at'; expected '_' or identifier
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:50:31: error: Function expected at
  Step
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  u

Hint: The identifier `Step` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:53:35: error: Function expected at
  Step
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  s

Hint: The identifier `Step` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:58:12: error: unexpected token 'at'; expected command
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:62:36: error: Function expected at
  Trace
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  s

Hint: The identifier `Trace` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:103:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.PermissionBorrowOperationalFoundationR128.indexed_member`:
  [DecidableEq Arg]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Arg] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:163:11: error: unsolved goals
case pos.none
Arg : Type
n : Nat
inst✝ : DecidableEq Arg
s : State Arg n
selected : Fin n
q : Request Arg n
r : Record Arg
loc : selected = q.token.location
found : s.heap selected = none
ok :
  ((s.heap q.token.location).bind fun r =>
      if r.allocation = q.token.allocation then
        (q.member.bind fun k => r.concrete[k]?).bind fun f => if f = q.family then some r else none
      else none) =
    some r
⊢ selected = q.token.location ∧
    s.heap q.token.location = some r ∧ r.allocation = q.token.allocation ∧ q.family ∈ r.concrete
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:170:17: error: unsolved goals
case pos.some.none
Arg : Type
n : Nat
inst✝ : DecidableEq Arg
s : State Arg n
selected : Fin n
q : Request Arg n
r : Record Arg
loc : selected = q.token.location
actual : Record Arg
found : s.heap selected = some actual
identity : actual.allocation = q.token.allocation
k : Nat
m : q.member = some k
read : actual.concrete[k]? = none
ok :
  ((s.heap q.token.location).bind fun r =>
      if r.allocation = q.token.allocation then r.concrete[k]?.bind fun f => if f = q.family then some r else none
      else none) =
    some r
⊢ selected = q.token.location ∧
    s.heap q.token.location = some r ∧ r.allocation = q.token.allocation ∧ q.family ∈ r.concrete
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:174:16: error: Type mismatch: After simplification, term
  ok
 has type
  ((s.heap q.token.location).bind fun r =>
      if r.allocation = q.token.allocation then r.concrete[k]?.bind fun f => if f = q.family then some r else none
      else none) =
    some r
but is expected to have type
  actual = r
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:178:12: error: unsolved goals
case neg
Arg : Type
n : Nat
inst✝ : DecidableEq Arg
s : State Arg n
selected : Fin n
q : Request Arg n
r : Record Arg
loc : selected = q.token.location
actual : Record Arg
found : s.heap selected = some actual
identity : actual.allocation = q.token.allocation
k : Nat
m : q.member = some k
f : Family Arg
read : actual.concrete[k]? = some f
equal : ¬f = q.family
ok :
  ((s.heap q.token.location).bind fun r =>
      if r.allocation = q.token.allocation then r.concrete[k]?.bind fun f => if f = q.family then some r else none
      else none) =
    some r
⊢ selected = q.token.location ∧
    s.heap q.token.location = some r ∧ r.allocation = q.token.allocation ∧ q.family ∈ r.concrete
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:179:6: error: unsolved goals
case neg
Arg : Type
n : Nat
inst✝ : DecidableEq Arg
s : State Arg n
selected : Fin n
q : Request Arg n
r : Record Arg
loc : selected = q.token.location
actual : Record Arg
found : s.heap selected = some actual
identity : ¬actual.allocation = q.token.allocation
ok :
  ((s.heap q.token.location).bind fun r =>
      if r.allocation = q.token.allocation then
        (q.member.bind fun k => r.concrete[k]?).bind fun f => if f = q.family then some r else none
      else none) =
    some r
⊢ selected = q.token.location ∧
    s.heap q.token.location = some r ∧ r.allocation = q.token.allocation ∧ q.family ∈ r.concrete
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:163:34: warning: This simp argument is unused:
  found

Hint: Omit it from the simp argument list.
  [apply] simp [consume, loc] at ok

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:167:38: warning: This simp argument is unused:
  found

Hint: Omit it from the simp argument list.
  [apply] simp [consume, loc, identity, m] at ok

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:167:45: warning: This simp argument is unused:
  identity

Hint: Omit it from the simp argument list.
  [apply] simp [consume, loc, found, m] at ok

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:170:40: warning: This simp argument is unused:
  found

Hint: Omit it from the simp argument list.
  [apply] simp [consume, loc, identity, m, read] at ok

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:170:47: warning: This simp argument is unused:
  identity

Hint: Omit it from the simp argument list.
  [apply] simp [consume, loc, found, m, read] at ok

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:170:60: warning: This simp argument is unused:
  read

Hint: Omit it from the simp argument list.
  [apply] simp [consume, loc, found, identity, m] at ok

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:178:34: warning: This simp argument is unused:
  found

Hint: Omit it from the simp argument list.
  [apply] simp [consume, loc, identity, m, read, equal] at ok

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:178:41: warning: This simp argument is unused:
  identity

Hint: Omit it from the simp argument list.
  [apply] simp [consume, loc, found, m, read, equal] at ok

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:178:54: warning: This simp argument is unused:
  read

Hint: Omit it from the simp argument list.
  [apply] simp [consume, loc, found, identity, m, equal] at ok

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:178:60: warning: This simp argument is unused:
  equal

Hint: Omit it from the simp argument list.
  [apply] simp [consume, loc, found, identity, m, read] at ok

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:179:28: warning: This simp argument is unused:
  found

Hint: Omit it from the simp argument list.
  [apply] simp [consume, loc, identity] at ok

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:179:35: warning: This simp argument is unused:
  identity

Hint: Omit it from the simp argument list.
  [apply] simp [consume, loc, found] at ok

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:195:19: error: Application type mismatch: The argument
  found
has type
  s.heap loc = some r
but is expected to have type
  some r = some r
in the application
  And.intro found
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:201:31: error: Function expected at
  Trace
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (capturedState s c)

Hint: The identifier `Trace` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:205:60: error: unsolved goals
Arg : Type
n : Nat
inst✝ : DecidableEq Arg
x✝ : Sort u_1
Trace : x✝
s : State Arg n
loc : Fin n
f : Family Arg
c : Captured Arg n
ok : capture s loc f = some c
u : State Arg n
trace : sorry
r : Record Arg
k : Nat
found : s.heap loc = some r
token : c.token = { location := loc, allocation := r.allocation }
family : c.family = f
member : c.member = some k
first : FirstAt r.concrete f k
⊢ ∃ r k,
    s.heap loc = some r ∧
      u.heap loc = some r ∧
        (copyAgain (copyRequest c)).member = some k ∧
          FirstAt r.concrete f k ∧ consume u loc (copyAgain (copyRequest c)) = some r
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:221:31: error: Function expected at
  Trace
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (capturedState s c)

Hint: The identifier `Trace` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:245:13: error: failed to synthesize
  Decidable
    (capture duplicateState 0 nine =
      some { token := { location := 0, allocation := 12 }, family := nine, member := some 0 })

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:245:24: error: failed to synthesize
  Decidable (consume duplicateState 0 (localRequest 0) = some duplicateRecord)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:245:35: error: failed to synthesize
  Decidable (consume duplicateState 0 (localRequest 1) = some duplicateRecord)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
@YulangClosure.PermissionBorrowOperationalFoundationR128.step_preserves : ∀ {Arg : Type} {n : Nat} {x : Sort u_1}
  {Step : x} (t : YulangClosure.PermissionBorrowOperationalFoundationR128.Token n)
  {s u : YulangClosure.PermissionBorrowOperationalFoundationR128.State Arg n},
  t ∈ s.borrows → ∀ (step : sorry), t ∈ u.borrows ∧ u.heap t.location = s.heap t.location
'YulangClosure.PermissionBorrowOperationalFoundationR128.step_preserves' depends on axioms: [sorryAx]
@YulangClosure.PermissionBorrowOperationalFoundationR128.trace_preserves : ∀ {Arg : Type} {n : Nat} {x : Sort u_1}
  {Trace : x} (t : YulangClosure.PermissionBorrowOperationalFoundationR128.Token n)
  {s u : YulangClosure.PermissionBorrowOperationalFoundationR128.State Arg n},
  t ∈ s.borrows → ∀ (trace : sorry), t ∈ u.borrows ∧ u.heap t.location = s.heap t.location
'YulangClosure.PermissionBorrowOperationalFoundationR128.trace_preserves' depends on axioms: [sorryAx]
@YulangClosure.PermissionBorrowOperationalFoundationR128.search_first : ∀ {Arg : Type} [inst : DecidableEq Arg]
  (xs : List (YulangClosure.PermissionBorrowOperationalFoundationR128.Family Arg))
  (f : YulangClosure.PermissionBorrowOperationalFoundationR128.Family Arg) (k : Nat),
  YulangClosure.PermissionBorrowOperationalFoundationR128.orderedSearch xs f = some k →
    YulangClosure.PermissionBorrowOperationalFoundationR128.FirstAt xs f k
'YulangClosure.PermissionBorrowOperationalFoundationR128.search_first' depends on axioms: [propext, Quot.sound]
@YulangClosure.PermissionBorrowOperationalFoundationR128.indexed_member : ∀ {Arg : Type} [DecidableEq Arg]
  (xs : List (YulangClosure.PermissionBorrowOperationalFoundationR128.Family Arg)) (k : Nat)
  (f : YulangClosure.PermissionBorrowOperationalFoundationR128.Family Arg), xs[k]? = some f → f ∈ xs
'YulangClosure.PermissionBorrowOperationalFoundationR128.indexed_member' depends on axioms: [propext]
@YulangClosure.PermissionBorrowOperationalFoundationR128.consumer_exact_member : ∀ {Arg : Type} {n : Nat}
  [inst : DecidableEq Arg] (s : YulangClosure.PermissionBorrowOperationalFoundationR128.State Arg n) (selected : Fin n)
  (q : YulangClosure.PermissionBorrowOperationalFoundationR128.Request Arg n)
  (r : YulangClosure.PermissionBorrowOperationalFoundationR128.Record Arg),
  YulangClosure.PermissionBorrowOperationalFoundationR128.consume s selected q = some r →
    selected = q.token.location ∧
      s.heap q.token.location = some r ∧ r.allocation = q.token.allocation ∧ q.family ∈ r.concrete
'YulangClosure.PermissionBorrowOperationalFoundationR128.consumer_exact_member' depends on axioms: [propext,
 sorryAx,
 Quot.sound]
@YulangClosure.PermissionBorrowOperationalFoundationR128.capture_exact : ∀ {Arg : Type} {n : Nat}
  [inst : DecidableEq Arg] (s : YulangClosure.PermissionBorrowOperationalFoundationR128.State Arg n) (loc : Fin n)
  (f : YulangClosure.PermissionBorrowOperationalFoundationR128.Family Arg)
  (c : YulangClosure.PermissionBorrowOperationalFoundationR128.Captured Arg n),
  YulangClosure.PermissionBorrowOperationalFoundationR128.capture s loc f = some c →
    ∃ r k,
      s.heap loc = some r ∧
        c.token = { location := loc, allocation := r.allocation } ∧
          c.family = f ∧
            c.member = some k ∧ YulangClosure.PermissionBorrowOperationalFoundationR128.FirstAt r.concrete f k
'YulangClosure.PermissionBorrowOperationalFoundationR128.capture_exact' depends on axioms: [propext,
 sorryAx,
 Quot.sound]
@YulangClosure.PermissionBorrowOperationalFoundationR128.captured_trace_copy : ∀ {Arg : Type} {n : Nat}
  [inst : DecidableEq Arg] {x : Sort u_1} {Trace : x}
  (s : YulangClosure.PermissionBorrowOperationalFoundationR128.State Arg n) (loc : Fin n)
  (f : YulangClosure.PermissionBorrowOperationalFoundationR128.Family Arg)
  (c : YulangClosure.PermissionBorrowOperationalFoundationR128.Captured Arg n),
  YulangClosure.PermissionBorrowOperationalFoundationR128.capture s loc f = some c →
    ∀ (u : YulangClosure.PermissionBorrowOperationalFoundationR128.State Arg n) (trace : sorry),
      ∃ r k,
        s.heap loc = some r ∧
          u.heap loc = some r ∧
            (YulangClosure.PermissionBorrowOperationalFoundationR128.copyAgain
                    (YulangClosure.PermissionBorrowOperationalFoundationR128.copyRequest c)).member =
                some k ∧
              YulangClosure.PermissionBorrowOperationalFoundationR128.FirstAt r.concrete f k ∧
                YulangClosure.PermissionBorrowOperationalFoundationR128.consume u loc
                    (YulangClosure.PermissionBorrowOperationalFoundationR128.copyAgain
                      (YulangClosure.PermissionBorrowOperationalFoundationR128.copyRequest c)) =
                  some r
'YulangClosure.PermissionBorrowOperationalFoundationR128.captured_trace_copy' depends on axioms: [propext,
 sorryAx,
 Quot.sound]
@YulangClosure.PermissionBorrowOperationalFoundationR128.captured_consumer_original_member : ∀ {Arg : Type} {n : Nat}
  [inst : DecidableEq Arg] {x : Sort u_1} {Trace : x}
  (s : YulangClosure.PermissionBorrowOperationalFoundationR128.State Arg n) (loc : Fin n)
  (f : YulangClosure.PermissionBorrowOperationalFoundationR128.Family Arg)
  (c : YulangClosure.PermissionBorrowOperationalFoundationR128.Captured Arg n),
  YulangClosure.PermissionBorrowOperationalFoundationR128.capture s loc f = some c →
    ∀ (u : YulangClosure.PermissionBorrowOperationalFoundationR128.State Arg n) (trace : sorry) (selected : Fin n)
      (r : YulangClosure.PermissionBorrowOperationalFoundationR128.Record Arg),
      YulangClosure.PermissionBorrowOperationalFoundationR128.consume u selected
            (YulangClosure.PermissionBorrowOperationalFoundationR128.copyRequest c) =
          some r →
        s.heap loc = some r ∧ f ∈ r.concrete
'YulangClosure.PermissionBorrowOperationalFoundationR128.captured_consumer_original_member' depends on axioms: [propext,
 sorryAx]
YulangClosure.PermissionBorrowOperationalFoundationR128.duplicate_discriminator : YulangClosure.PermissionBorrowOperationalFoundationR128.capture
      YulangClosure.PermissionBorrowOperationalFoundationR128.duplicateState 0
      YulangClosure.PermissionBorrowOperationalFoundationR128.nine =
    some
      { token := { location := 0, allocation := 12 },
        family := YulangClosure.PermissionBorrowOperationalFoundationR128.nine, member := some 0 } ∧
  YulangClosure.PermissionBorrowOperationalFoundationR128.consume
        YulangClosure.PermissionBorrowOperationalFoundationR128.duplicateState 0
        (YulangClosure.PermissionBorrowOperationalFoundationR128.localRequest 0) =
      some YulangClosure.PermissionBorrowOperationalFoundationR128.duplicateRecord ∧
    YulangClosure.PermissionBorrowOperationalFoundationR128.consume
          YulangClosure.PermissionBorrowOperationalFoundationR128.duplicateState 0
          (YulangClosure.PermissionBorrowOperationalFoundationR128.localRequest 1) =
        some YulangClosure.PermissionBorrowOperationalFoundationR128.duplicateRecord ∧
      ¬YulangClosure.PermissionBorrowOperationalFoundationR128.FirstAt
          YulangClosure.PermissionBorrowOperationalFoundationR128.duplicateRecord.concrete
          YulangClosure.PermissionBorrowOperationalFoundationR128.nine 1
'YulangClosure.PermissionBorrowOperationalFoundationR128.duplicate_discriminator' depends on axioms: [propext, sorryAx]

STDERR:

```

## Resumed invocation 2 (r2 contract / r3 manifest)

```text
Command: /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M768 YulangClosure/PermissionBorrowOperationalFoundationR128.lean
Exit: 1
Elapsed seconds: 0.7150449030013988
STDOUT:
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:57:2: error: Too many variable names provided at alternative `borrow`: 5 provided, but 4 expected
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:57:45: error: Application type mismatch: The argument
  List.mem_cons_of_mem other ?m.99
has type
  ?m.97 ∈ other :: ?m.98
but is expected to have type
  t ∈ { heap := s✝.heap, borrows := s :: s✝.borrows }.borrows
in the application
  And.intro (List.mem_cons_of_mem other ?m.99)
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:58:2: error: Too many variable names provided at alternative `write`: 4 provided, but 3 expected
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:59:17: warning: `if_neg` has been deprecated: Use `ite_eq_right` instead

Hint: Replace the deprecated name:
  i̵f̵_̵n̵e̵g̵i̲t̲e̲_̲e̲q̲_̲r̲i̲g̲h̲t̲
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:59:25: error(lean.unknownIdentifier): Unknown identifier `free`
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:169:40: warning: This simp argument is unused:
  identity

Hint: Omit it from the simp argument list.
  [apply] simp [consume, found, m] at ok

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
YulangClosure/PermissionBorrowOperationalFoundationR128.lean:178:40: warning: This simp argument is unused:
  found

Hint: Omit it from the simp argument list.
  [apply] simp only

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
@YulangClosure.PermissionBorrowOperationalFoundationR128.step_preserves : ∀ {ModuleKey SourceNodeKey : Type} {n : Nat}
  (t : YulangClosure.PermissionBorrowOperationalFoundationR128.Token n)
  {s u : YulangClosure.PermissionBorrowOperationalFoundationR128.State ModuleKey SourceNodeKey n},
  t ∈ s.borrows →
    YulangClosure.PermissionBorrowOperationalFoundationR128.Step s u →
      t ∈ u.borrows ∧ u.heap t.location = s.heap t.location
'YulangClosure.PermissionBorrowOperationalFoundationR128.step_preserves' depends on axioms: [sorryAx]
@YulangClosure.PermissionBorrowOperationalFoundationR128.trace_preserves : ∀ {ModuleKey SourceNodeKey : Type} {n : Nat}
  (t : YulangClosure.PermissionBorrowOperationalFoundationR128.Token n)
  {s u : YulangClosure.PermissionBorrowOperationalFoundationR128.State ModuleKey SourceNodeKey n},
  t ∈ s.borrows →
    YulangClosure.PermissionBorrowOperationalFoundationR128.Trace s u →
      t ∈ u.borrows ∧ u.heap t.location = s.heap t.location
'YulangClosure.PermissionBorrowOperationalFoundationR128.trace_preserves' depends on axioms: [sorryAx]
@YulangClosure.PermissionBorrowOperationalFoundationR128.search_first : ∀ {ModuleKey SourceNodeKey : Type}
  [inst : DecidableEq ModuleKey] [inst_1 : DecidableEq SourceNodeKey]
  (xs : List (YulangClosure.PermissionBorrowOperationalFoundationR128.Family ModuleKey SourceNodeKey))
  (f : YulangClosure.PermissionBorrowOperationalFoundationR128.Family ModuleKey SourceNodeKey) (k : Nat),
  YulangClosure.PermissionBorrowOperationalFoundationR128.orderedSearch xs f = some k →
    YulangClosure.PermissionBorrowOperationalFoundationR128.FirstAt xs f k
'YulangClosure.PermissionBorrowOperationalFoundationR128.search_first' depends on axioms: [propext, Quot.sound]
@YulangClosure.PermissionBorrowOperationalFoundationR128.indexed_member : ∀ {ModuleKey SourceNodeKey : Type}
  (xs : List (YulangClosure.PermissionBorrowOperationalFoundationR128.Family ModuleKey SourceNodeKey)) (k : Nat)
  (f : YulangClosure.PermissionBorrowOperationalFoundationR128.Family ModuleKey SourceNodeKey), xs[k]? = some f → f ∈ xs
'YulangClosure.PermissionBorrowOperationalFoundationR128.indexed_member' depends on axioms: [propext]
@YulangClosure.PermissionBorrowOperationalFoundationR128.consumer_exact_member : ∀ {ModuleKey SourceNodeKey : Type}
  {n : Nat} [inst : DecidableEq ModuleKey] [inst_1 : DecidableEq SourceNodeKey]
  (s : YulangClosure.PermissionBorrowOperationalFoundationR128.State ModuleKey SourceNodeKey n) (selected : Fin n)
  (q : YulangClosure.PermissionBorrowOperationalFoundationR128.Request ModuleKey SourceNodeKey n)
  (r : YulangClosure.PermissionBorrowOperationalFoundationR128.Record ModuleKey SourceNodeKey),
  YulangClosure.PermissionBorrowOperationalFoundationR128.consume s selected q = some r →
    selected = q.token.location ∧
      s.heap q.token.location = some r ∧ r.allocation = q.token.allocation ∧ q.family ∈ r.concrete
'YulangClosure.PermissionBorrowOperationalFoundationR128.consumer_exact_member' depends on axioms: [propext, Quot.sound]
@YulangClosure.PermissionBorrowOperationalFoundationR128.capture_exact : ∀ {ModuleKey SourceNodeKey : Type} {n : Nat}
  [inst : DecidableEq ModuleKey] [inst_1 : DecidableEq SourceNodeKey]
  (s : YulangClosure.PermissionBorrowOperationalFoundationR128.State ModuleKey SourceNodeKey n) (loc : Fin n)
  (f : YulangClosure.PermissionBorrowOperationalFoundationR128.Family ModuleKey SourceNodeKey)
  (c : YulangClosure.PermissionBorrowOperationalFoundationR128.Captured ModuleKey SourceNodeKey n),
  YulangClosure.PermissionBorrowOperationalFoundationR128.capture s loc f = some c →
    ∃ r k,
      s.heap loc = some r ∧
        c.token = { location := loc, allocation := r.allocation } ∧
          c.family = f ∧
            c.member = some k ∧ YulangClosure.PermissionBorrowOperationalFoundationR128.FirstAt r.concrete f k
'YulangClosure.PermissionBorrowOperationalFoundationR128.capture_exact' depends on axioms: [propext, Quot.sound]
@YulangClosure.PermissionBorrowOperationalFoundationR128.captured_trace_copy : ∀ {ModuleKey SourceNodeKey : Type}
  {n : Nat} [inst : DecidableEq ModuleKey] [inst_1 : DecidableEq SourceNodeKey]
  (s : YulangClosure.PermissionBorrowOperationalFoundationR128.State ModuleKey SourceNodeKey n) (loc : Fin n)
  (f : YulangClosure.PermissionBorrowOperationalFoundationR128.Family ModuleKey SourceNodeKey)
  (c : YulangClosure.PermissionBorrowOperationalFoundationR128.Captured ModuleKey SourceNodeKey n),
  YulangClosure.PermissionBorrowOperationalFoundationR128.capture s loc f = some c →
    ∀ (u : YulangClosure.PermissionBorrowOperationalFoundationR128.State ModuleKey SourceNodeKey n),
      YulangClosure.PermissionBorrowOperationalFoundationR128.Trace
          (YulangClosure.PermissionBorrowOperationalFoundationR128.capturedState s c) u →
        ∃ r k,
          s.heap loc = some r ∧
            u.heap loc = some r ∧
              (YulangClosure.PermissionBorrowOperationalFoundationR128.copyAgain
                      (YulangClosure.PermissionBorrowOperationalFoundationR128.copyRequest c)).member =
                  some k ∧
                YulangClosure.PermissionBorrowOperationalFoundationR128.FirstAt r.concrete f k ∧
                  YulangClosure.PermissionBorrowOperationalFoundationR128.consume u loc
                      (YulangClosure.PermissionBorrowOperationalFoundationR128.copyAgain
                        (YulangClosure.PermissionBorrowOperationalFoundationR128.copyRequest c)) =
                    some r
'YulangClosure.PermissionBorrowOperationalFoundationR128.captured_trace_copy' depends on axioms: [propext,
 sorryAx,
 Quot.sound]
@YulangClosure.PermissionBorrowOperationalFoundationR128.captured_consumer_original_member : ∀
  {ModuleKey SourceNodeKey : Type} {n : Nat} [inst : DecidableEq ModuleKey] [inst_1 : DecidableEq SourceNodeKey]
  (s : YulangClosure.PermissionBorrowOperationalFoundationR128.State ModuleKey SourceNodeKey n) (loc : Fin n)
  (f : YulangClosure.PermissionBorrowOperationalFoundationR128.Family ModuleKey SourceNodeKey)
  (c : YulangClosure.PermissionBorrowOperationalFoundationR128.Captured ModuleKey SourceNodeKey n),
  YulangClosure.PermissionBorrowOperationalFoundationR128.capture s loc f = some c →
    ∀ (u : YulangClosure.PermissionBorrowOperationalFoundationR128.State ModuleKey SourceNodeKey n),
      YulangClosure.PermissionBorrowOperationalFoundationR128.Trace
          (YulangClosure.PermissionBorrowOperationalFoundationR128.capturedState s c) u →
        ∀ (selected : Fin n)
          (r : YulangClosure.PermissionBorrowOperationalFoundationR128.Record ModuleKey SourceNodeKey),
          YulangClosure.PermissionBorrowOperationalFoundationR128.consume u selected
                (YulangClosure.PermissionBorrowOperationalFoundationR128.copyRequest c) =
              some r →
            s.heap loc = some r ∧ f ∈ r.concrete
'YulangClosure.PermissionBorrowOperationalFoundationR128.captured_consumer_original_member' depends on axioms: [propext,
 sorryAx,
 Quot.sound]
YulangClosure.PermissionBorrowOperationalFoundationR128.duplicate_discriminator : YulangClosure.PermissionBorrowOperationalFoundationR128.capture
      YulangClosure.PermissionBorrowOperationalFoundationR128.duplicateState 0
      YulangClosure.PermissionBorrowOperationalFoundationR128.nine =
    some
      { token := { location := 0, allocation := 12 },
        family := YulangClosure.PermissionBorrowOperationalFoundationR128.nine, member := some 0 } ∧
  YulangClosure.PermissionBorrowOperationalFoundationR128.consume
        YulangClosure.PermissionBorrowOperationalFoundationR128.duplicateState 0
        (YulangClosure.PermissionBorrowOperationalFoundationR128.localRequest 0) =
      some YulangClosure.PermissionBorrowOperationalFoundationR128.duplicateRecord ∧
    YulangClosure.PermissionBorrowOperationalFoundationR128.consume
          YulangClosure.PermissionBorrowOperationalFoundationR128.duplicateState 0
          (YulangClosure.PermissionBorrowOperationalFoundationR128.localRequest 1) =
        some YulangClosure.PermissionBorrowOperationalFoundationR128.duplicateRecord ∧
      ¬YulangClosure.PermissionBorrowOperationalFoundationR128.FirstAt
          YulangClosure.PermissionBorrowOperationalFoundationR128.duplicateRecord.concrete
          YulangClosure.PermissionBorrowOperationalFoundationR128.nine 1
'YulangClosure.PermissionBorrowOperationalFoundationR128.duplicate_discriminator' depends on axioms: [propext]
YulangClosure.PermissionBorrowOperationalFoundationR128.unequal_module_same_declaration : { module := 0,
      declaration := 9 } ≠
    { module := 1, declaration := 9 } ∧
  YulangClosure.PermissionBorrowOperationalFoundationR128.orderedSearch
      [{ module := 0, declaration := 9 }, { module := 1, declaration := 9 }] { module := 1, declaration := 9 } =
    some 1
'YulangClosure.PermissionBorrowOperationalFoundationR128.unequal_module_same_declaration' does not depend on any axioms

STDERR:

```

## Final allowed invocation 3 (r2 contract / r3 manifest)

```text
Command: /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M768 YulangClosure/PermissionBorrowOperationalFoundationR128.lean
Exit: 0
Elapsed seconds: 0.7536799049994443
STDOUT:
@YulangClosure.PermissionBorrowOperationalFoundationR128.step_preserves : ∀ {ModuleKey SourceNodeKey : Type} {n : Nat}
  (t : YulangClosure.PermissionBorrowOperationalFoundationR128.Token n)
  {s u : YulangClosure.PermissionBorrowOperationalFoundationR128.State ModuleKey SourceNodeKey n},
  t ∈ s.borrows →
    YulangClosure.PermissionBorrowOperationalFoundationR128.Step s u →
      t ∈ u.borrows ∧ u.heap t.location = s.heap t.location
'YulangClosure.PermissionBorrowOperationalFoundationR128.step_preserves' depends on axioms: [propext]
@YulangClosure.PermissionBorrowOperationalFoundationR128.trace_preserves : ∀ {ModuleKey SourceNodeKey : Type} {n : Nat}
  (t : YulangClosure.PermissionBorrowOperationalFoundationR128.Token n)
  {s u : YulangClosure.PermissionBorrowOperationalFoundationR128.State ModuleKey SourceNodeKey n},
  t ∈ s.borrows →
    YulangClosure.PermissionBorrowOperationalFoundationR128.Trace s u →
      t ∈ u.borrows ∧ u.heap t.location = s.heap t.location
'YulangClosure.PermissionBorrowOperationalFoundationR128.trace_preserves' depends on axioms: [propext]
@YulangClosure.PermissionBorrowOperationalFoundationR128.search_first : ∀ {ModuleKey SourceNodeKey : Type}
  [inst : DecidableEq ModuleKey] [inst_1 : DecidableEq SourceNodeKey]
  (xs : List (YulangClosure.PermissionBorrowOperationalFoundationR128.Family ModuleKey SourceNodeKey))
  (f : YulangClosure.PermissionBorrowOperationalFoundationR128.Family ModuleKey SourceNodeKey) (k : Nat),
  YulangClosure.PermissionBorrowOperationalFoundationR128.orderedSearch xs f = some k →
    YulangClosure.PermissionBorrowOperationalFoundationR128.FirstAt xs f k
'YulangClosure.PermissionBorrowOperationalFoundationR128.search_first' depends on axioms: [propext, Quot.sound]
@YulangClosure.PermissionBorrowOperationalFoundationR128.indexed_member : ∀ {ModuleKey SourceNodeKey : Type}
  (xs : List (YulangClosure.PermissionBorrowOperationalFoundationR128.Family ModuleKey SourceNodeKey)) (k : Nat)
  (f : YulangClosure.PermissionBorrowOperationalFoundationR128.Family ModuleKey SourceNodeKey), xs[k]? = some f → f ∈ xs
'YulangClosure.PermissionBorrowOperationalFoundationR128.indexed_member' depends on axioms: [propext]
@YulangClosure.PermissionBorrowOperationalFoundationR128.consumer_exact_member : ∀ {ModuleKey SourceNodeKey : Type}
  {n : Nat} [inst : DecidableEq ModuleKey] [inst_1 : DecidableEq SourceNodeKey]
  (s : YulangClosure.PermissionBorrowOperationalFoundationR128.State ModuleKey SourceNodeKey n) (selected : Fin n)
  (q : YulangClosure.PermissionBorrowOperationalFoundationR128.Request ModuleKey SourceNodeKey n)
  (r : YulangClosure.PermissionBorrowOperationalFoundationR128.Record ModuleKey SourceNodeKey),
  YulangClosure.PermissionBorrowOperationalFoundationR128.consume s selected q = some r →
    selected = q.token.location ∧
      s.heap q.token.location = some r ∧ r.allocation = q.token.allocation ∧ q.family ∈ r.concrete
'YulangClosure.PermissionBorrowOperationalFoundationR128.consumer_exact_member' depends on axioms: [propext, Quot.sound]
@YulangClosure.PermissionBorrowOperationalFoundationR128.capture_exact : ∀ {ModuleKey SourceNodeKey : Type} {n : Nat}
  [inst : DecidableEq ModuleKey] [inst_1 : DecidableEq SourceNodeKey]
  (s : YulangClosure.PermissionBorrowOperationalFoundationR128.State ModuleKey SourceNodeKey n) (loc : Fin n)
  (f : YulangClosure.PermissionBorrowOperationalFoundationR128.Family ModuleKey SourceNodeKey)
  (c : YulangClosure.PermissionBorrowOperationalFoundationR128.Captured ModuleKey SourceNodeKey n),
  YulangClosure.PermissionBorrowOperationalFoundationR128.capture s loc f = some c →
    ∃ r k,
      s.heap loc = some r ∧
        c.token = { location := loc, allocation := r.allocation } ∧
          c.family = f ∧
            c.member = some k ∧ YulangClosure.PermissionBorrowOperationalFoundationR128.FirstAt r.concrete f k
'YulangClosure.PermissionBorrowOperationalFoundationR128.capture_exact' depends on axioms: [propext, Quot.sound]
@YulangClosure.PermissionBorrowOperationalFoundationR128.captured_trace_copy : ∀ {ModuleKey SourceNodeKey : Type}
  {n : Nat} [inst : DecidableEq ModuleKey] [inst_1 : DecidableEq SourceNodeKey]
  (s : YulangClosure.PermissionBorrowOperationalFoundationR128.State ModuleKey SourceNodeKey n) (loc : Fin n)
  (f : YulangClosure.PermissionBorrowOperationalFoundationR128.Family ModuleKey SourceNodeKey)
  (c : YulangClosure.PermissionBorrowOperationalFoundationR128.Captured ModuleKey SourceNodeKey n),
  YulangClosure.PermissionBorrowOperationalFoundationR128.capture s loc f = some c →
    ∀ (u : YulangClosure.PermissionBorrowOperationalFoundationR128.State ModuleKey SourceNodeKey n),
      YulangClosure.PermissionBorrowOperationalFoundationR128.Trace
          (YulangClosure.PermissionBorrowOperationalFoundationR128.capturedState s c) u →
        ∃ r k,
          s.heap loc = some r ∧
            u.heap loc = some r ∧
              (YulangClosure.PermissionBorrowOperationalFoundationR128.copyAgain
                      (YulangClosure.PermissionBorrowOperationalFoundationR128.copyRequest c)).member =
                  some k ∧
                YulangClosure.PermissionBorrowOperationalFoundationR128.FirstAt r.concrete f k ∧
                  YulangClosure.PermissionBorrowOperationalFoundationR128.consume u loc
                      (YulangClosure.PermissionBorrowOperationalFoundationR128.copyAgain
                        (YulangClosure.PermissionBorrowOperationalFoundationR128.copyRequest c)) =
                    some r
'YulangClosure.PermissionBorrowOperationalFoundationR128.captured_trace_copy' depends on axioms: [propext, Quot.sound]
@YulangClosure.PermissionBorrowOperationalFoundationR128.captured_consumer_original_member : ∀
  {ModuleKey SourceNodeKey : Type} {n : Nat} [inst : DecidableEq ModuleKey] [inst_1 : DecidableEq SourceNodeKey]
  (s : YulangClosure.PermissionBorrowOperationalFoundationR128.State ModuleKey SourceNodeKey n) (loc : Fin n)
  (f : YulangClosure.PermissionBorrowOperationalFoundationR128.Family ModuleKey SourceNodeKey)
  (c : YulangClosure.PermissionBorrowOperationalFoundationR128.Captured ModuleKey SourceNodeKey n),
  YulangClosure.PermissionBorrowOperationalFoundationR128.capture s loc f = some c →
    ∀ (u : YulangClosure.PermissionBorrowOperationalFoundationR128.State ModuleKey SourceNodeKey n),
      YulangClosure.PermissionBorrowOperationalFoundationR128.Trace
          (YulangClosure.PermissionBorrowOperationalFoundationR128.capturedState s c) u →
        ∀ (selected : Fin n)
          (r : YulangClosure.PermissionBorrowOperationalFoundationR128.Record ModuleKey SourceNodeKey),
          YulangClosure.PermissionBorrowOperationalFoundationR128.consume u selected
                (YulangClosure.PermissionBorrowOperationalFoundationR128.copyRequest c) =
              some r →
            s.heap loc = some r ∧ f ∈ r.concrete
'YulangClosure.PermissionBorrowOperationalFoundationR128.captured_consumer_original_member' depends on axioms: [propext,
 Quot.sound]
YulangClosure.PermissionBorrowOperationalFoundationR128.duplicate_discriminator : YulangClosure.PermissionBorrowOperationalFoundationR128.capture
      YulangClosure.PermissionBorrowOperationalFoundationR128.duplicateState 0
      YulangClosure.PermissionBorrowOperationalFoundationR128.nine =
    some
      { token := { location := 0, allocation := 12 },
        family := YulangClosure.PermissionBorrowOperationalFoundationR128.nine, member := some 0 } ∧
  YulangClosure.PermissionBorrowOperationalFoundationR128.consume
        YulangClosure.PermissionBorrowOperationalFoundationR128.duplicateState 0
        (YulangClosure.PermissionBorrowOperationalFoundationR128.localRequest 0) =
      some YulangClosure.PermissionBorrowOperationalFoundationR128.duplicateRecord ∧
    YulangClosure.PermissionBorrowOperationalFoundationR128.consume
          YulangClosure.PermissionBorrowOperationalFoundationR128.duplicateState 0
          (YulangClosure.PermissionBorrowOperationalFoundationR128.localRequest 1) =
        some YulangClosure.PermissionBorrowOperationalFoundationR128.duplicateRecord ∧
      ¬YulangClosure.PermissionBorrowOperationalFoundationR128.FirstAt
          YulangClosure.PermissionBorrowOperationalFoundationR128.duplicateRecord.concrete
          YulangClosure.PermissionBorrowOperationalFoundationR128.nine 1
'YulangClosure.PermissionBorrowOperationalFoundationR128.duplicate_discriminator' depends on axioms: [propext]
YulangClosure.PermissionBorrowOperationalFoundationR128.unequal_module_same_declaration : { module := 0,
      declaration := 9 } ≠
    { module := 1, declaration := 9 } ∧
  YulangClosure.PermissionBorrowOperationalFoundationR128.orderedSearch
      [{ module := 0, declaration := 9 }, { module := 1, declaration := 9 }] { module := 1, declaration := 9 } =
    some 1
'YulangClosure.PermissionBorrowOperationalFoundationR128.unequal_module_same_declaration' does not depend on any axioms

STDERR:

```
