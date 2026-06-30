# ChatGPT Pro consultation follow-up answer: Evidence VM direct state route proof

## 1. Short verdict

はい。前の回答で意図していた順序は、基本的には次である。

```text
Do not enable request-free route-specific DirectStateGet/Set yet.
First make RuntimeStateHandlerFrame participate in captured continuations.
Then return to Stage D route proof and direct execution.
```

ただし、これは「Stage D の proof 設計を後回しにする」という意味ではない。今やるべきことは次の 2 本立てである。

```text
Stage C execution safety:
  continuation が RuntimeStateHandlerFrame snapshot/fork を持つようにする

Stage D static proof:
  generic-fallback / legacy_bridge / no-candidate-handler から direct-ready へ進めるための
  KnownStateOperationRouteProof を plan に追加する
```

現在の状態、つまり

```text
known operation candidate hit: 800 / 400
active runtime state frame hit: 800 / 400
operation object execution: generic-fallback
visibility: legacy_bridge=true
reject: no-candidate-handler
direct_effect_calls: 0
```

では、Stage D の request-free direct execution を default enable するにはまだ足りない。`active_state_frame` が存在することは重要な runtime observation だが、それ単体は routing proof ではない。direct execution には、少なくとも次の 2 つが必要である。

```text
1. この operation call が、どの known state handler instance を見るべきかという static/dynamic route proof
2. その handler frame が captured continuation / multi-shot resume で正しく snapshot/fork されるという runtime semantics
```

Stage C は 2 を固める作業で、Stage D は 1 を固める作業である。順序としては、Stage C の canary を入れてから Stage D を有効化するのが安全だねぇ。

---

## 2. Missing proof, stated precisely

今ある runtime fact はこうである。

```text
at runtime:
  a known operation candidate is forced
  a matching active state frame exists
  dynamic hit count matches expected get/set count
```

足りない proof はこうである。

```text
For this concrete operation call site O,
under the current marker/provider/hygiene semantics,
O is allowed to bypass generic request allocation and access exactly
state frame F for known state handler plan P.
```

もう少し分解すると、Stage D の direct-ready proof は次を同時に証明する必要がある。

```text
operation identity:
  O is a compiler-certified local-state operation call, not arbitrary user code

handler meaning:
  target handler H has KnownHandlerPlan::State P

operation role:
  O is P.get or P.set, not merely a path ending with get/set

route visibility:
  O is within the dynamic/lexical route where H is visible and not blocked

hygiene:
  marker/provider/callback/delayed boundaries do not invalidate the route

runtime frame:
  the active frame selected at execution is the frame for P/H in the current branch

continuation semantics:
  if O runs inside a captured continuation branch, the frame it sees is that branch's fork
```

`legacy_bridge=true` はこの proof ではない。`legacy_bridge` は「現行 generic route machinery に任せればたぶん既存 semantics で扱える」という橋であり、「request-free にしてよい」という permission ではない。

したがって、`generic-fallback + legacy_bridge + active frame hit` だけで DirectStateGet/Set に進めるのは避けるべきである。

---

## 3. Stage C の exact runtime rule

今回いちばん重要な区別はここである。

```text
Do not snapshot all active state frames when a request is created.
Snapshot only the state frames whose handler boundary is crossed by the request continuation.
```

これが、質問の Case 1 と Case 2 を分ける exact rule になる。

### Case 1: state handler outside nondet/list handler

```yulang
{
  my $x = 0
  my ys = {
    my b = each [true, false]
    &x = $x + 1
    $x
  }.list
  (ys, $x)
}
```

ここでは state handler は nondet/list handler の外側にある。`each` request は inner nondet/list handler に捕まるので、outer state catch boundary を crossed しない。

したがって、nondet が捕まえる continuation に outer state frame snapshot を入れてはいけない。

```text
request created under active state frame x
but request is handled before crossing x's known-state catch
=> no state snapshot for x in this continuation
=> x remains shared across nondet branches
=> ([1, 2], 2)
```

このため、request creation 時に `active_state_handler_frames` を丸ごと snapshot する設計は不正である。これをやると Case 1 が `[1, 1]` 的な fork semantics に寄ってしまう。

### Case 2: state handler inside continuation captured by outer multi-shot handler

```text
outer multi-shot handler resumes k twice
state handler is inside k
first resume mutates local state
second resume should start from captured state
```

この場合、operation request は inner known-state catch boundary を越えて outer handler に向かう。つまり、request continuation は known-state catch の body continuation を含む。

したがって、`defer_catch_body(catch_expr, ...)` でその known-state catch を越える瞬間に snapshot を作る。

```text
request crosses known-state catch C
=> continuation segment for C is appended
=> snapshot frame for C is wrapped around that segment
=> each resume forks snapshot
=> branch mutations do not leak across multi-shot resumes
```

これが exact rule である。

```text
snapshot when crossing a known-state catch boundary,
not when creating a request,
not for every active frame,
not merely because a frame is active.
```

---

## 4. Where should `RuntimeStateHandlerFrame` snapshots be stored?

推奨は、新しい continuation wrapper を追加することだねぇ。

```rust
enum EvidenceContinuationFrame {
    StateFrames {
        snapshots: SmallVec<[RuntimeStateHandlerFrameSnapshot; 1]>,
        inner: EvidenceContinuation,
    },
    CatchBody {
        catch_expr: ExprId,
        arms: Rc<[control_vm::CatchArm]>,
        env: Env,
        tail: EvidenceContinuation,
    },
    // existing frames...
}
```

既存構造に合わせて `inner` を持てないなら、概念的に同じものを `EvidenceContinuation::state_frames(snapshots, continuation)` helper として実装すればよい。

`CatchBody` の中に `state_snapshot: Option<_>` を埋める案も動くが、意味が少し狭くなる。今回の本質は「この continuation segment を state frames の下で resume する」なので、`StateFrames` wrapper の方が読みやすい。

`EvidenceRequest` 本体に snapshots を持たせるのは避ける。request 全体の snapshot にすると、request creation 時点の active state frames を全部保存したくなり、Case 1 を壊しやすい。

### Data structure

```rust
#[derive(Clone)]
struct RuntimeStateHandlerFrameSnapshot {
    catch_expr: ExprId,
    plan_id: EvidenceVmKnownHandlerPlanId,
    state_def: DefId,
    state: SharedValue,
    source_frame_id: RuntimeStateFrameId,
    state_scope_id: RuntimeStateScopeId,
}

struct RuntimeStateHandlerFrame {
    catch_expr: ExprId,
    plan_id: EvidenceVmKnownHandlerPlanId,
    state_def: DefId,
    state: SharedValue,
    frame_id: RuntimeStateFrameId,
    state_scope_id: RuntimeStateScopeId,
}
```

`frame_id` は dynamic entry ごとに新しくなる runtime id。`state_scope_id` は escaped `StateRef` の remap に備えた logical scope id である。Stage C だけなら `frame_id` なしでも動くかもしれないが、recursive re-entry / escaped ref / debugging を考えると入れておく方が後で詰まらない。

---

## 5. Where should the snapshot be created?

`defer_catch_body` が正しい場所である。

理由は、ここが「request がこの catch boundary を越えて外側の handler に向かう」と分かる点だからである。request creation 時では早すぎる。`append_request_continuation` の汎用処理では、どの known-state catch を越えたのかという意味が薄くなる。

推奨形はこうである。

```rust
fn defer_catch_body(
    &mut self,
    catch_expr: ExprId,
    arms: Rc<[control_vm::CatchArm]>,
    env: &Env,
    request: EvidenceRequest,
) -> EvidenceRequest {
    let snapshot = self.snapshot_known_state_frame_for_crossed_catch(catch_expr);

    let mut env = self.clone_env(env);
    if let Some(snapshot) = &snapshot {
        // compatibility only: frame is truth, env shadow is legacy fallback support
        env = self.shadow_known_state_env(env, snapshot.state_def, snapshot.state.clone());
    }

    let catch_cont = EvidenceContinuation::catch_body(
        catch_expr,
        arms,
        env,
        EvidenceContinuation::identity(),
    );

    let cont = if let Some(snapshot) = snapshot {
        EvidenceContinuation::state_frames(smallvec![snapshot], catch_cont)
    } else {
        catch_cont
    };

    self.append_request_continuation(request, cont)
}
```

Snapshot helper:

```rust
fn snapshot_known_state_frame_for_crossed_catch(
    &mut self,
    catch_expr: ExprId,
) -> Option<RuntimeStateHandlerFrameSnapshot> {
    if !self.runtime_context.catch_has_known_state_handler(catch_expr) {
        return None;
    }

    let Some(index) = self.active_state_handler_frames
        .iter()
        .rposition(|frame| frame.catch_expr == catch_expr)
    else {
        self.stats.known_state_frame_snapshot_missing_frame += 1;
        return None;
    };

    let frame = &self.active_state_handler_frames[index];
    self.stats.known_state_frame_snapshots += 1;

    Some(RuntimeStateHandlerFrameSnapshot {
        catch_expr: frame.catch_expr,
        plan_id: frame.plan_id,
        state_def: frame.state_def,
        state: frame.state.clone(),
        source_frame_id: frame.frame_id,
        state_scope_id: frame.state_scope_id,
    })
}
```

`rposition` が重要である。同じ `catch_expr` が recursion で複数 active になった場合、越えているのは最も内側の dynamic instance だからである。

---

## 6. Wrap, do not append after

`defer_catch_body` で state snapshot を使うなら、必ず既存 continuation segment を **wrap** する。

```text
correct:
  StateFrames(snapshot) {
    CatchBody(... original continuation segment ...)
  }

wrong:
  CatchBody(... original continuation segment ...)
  then StateFrames(snapshot)
```

質問中の懸念通り、append after は遅すぎる。direct state get/set は resumed continuation の途中で発生するので、その時点ですでに state frame が active でなければならない。

Resume algorithm:

```rust
fn resume_state_frames(
    &mut self,
    snapshots: &[RuntimeStateHandlerFrameSnapshot],
    inner: EvidenceContinuation,
    value: SharedValue,
) -> EvidenceResult {
    let old_len = self.active_state_handler_frames.len();
    let forked = self.fork_state_frame_snapshots(snapshots);

    self.push_restored_state_frames(&forked);
    let result = self.resume_continuation(inner, value);

    match result {
        EvidenceResult::Value(value) => {
            self.pop_known_state_frames(old_len);
            EvidenceResult::Value(value)
        }
        EvidenceResult::Request(request) => {
            // The dynamic scope did not finish; preserve current state for later resume.
            let updated = self.snapshot_state_frame_suffix(old_len);
            self.pop_known_state_frames(old_len);
            let request = self.append_request_continuation(
                request,
                EvidenceContinuation::state_frames(updated, EvidenceContinuation::identity()),
            );
            EvidenceResult::Request(request)
        }
    }
}
```

この `Request` case が大事である。`StateFrames` は単なる「push して inner を一回走らせるだけ」の frame ではなく、marker/provider frame と同じような dynamic scope frame として振る舞う必要がある。inner continuation がまた request を出して外に出るなら、現在の state を再 snapshot して request continuation に戻す。

これをしないと、resume 中にさらに effect が起きた時に state frame が失われる。

---

## 7. Nested known-state handler ordering

Snapshot は active stack order を保つ。

```text
active_state_handler_frames:
  [outer, middle, inner]

snapshot group:
  [outer, middle, inner]   // push order

pop order:
  inner, middle, outer
```

ただし、`defer_catch_body(catch_expr)` で捕まえる基本単位は「その catch に対応する nearest active frame」でよい。nested known-state catches は request propagation 中にそれぞれの `defer_catch_body` を通るので、自然に continuation wrapper が積まれる。

例:

```text
request inside S2 inside S1 goes to outer handler

cross S2:
  append StateFrames(S2_snapshot) { CatchBody(S2) }

cross S1:
  append StateFrames(S1_snapshot) { CatchBody(S1) }
```

resume 時には continuation composition に従って outer frame が先に active になり、その内側で inner frame が active になる。結果として stack order は元の dynamic nesting と一致する。

将来、1 つの catch が複数 known state frames を張るようになるなら、その catch entry で push した frame range を記録して、range を active order で snapshot する。

```rust
struct KnownStateCatchFrameRange {
    catch_expr: ExprId,
    start: usize,
    end: usize,
}
```

今の `known_state_handlers_by_catch: Option<_>` に近い構造なら、nearest single frame capture で十分だと思うよ〜。

---

## 8. On resume: push frame, env-shadow, counters

### 8.1 Push onto `active_state_handler_frames`

はい。snapshot frames は resume 中に `active_state_handler_frames` へ push する。

DirectStateGet/Set も late catch-boundary direct get/set も、runtime state frame を truth として見るべきである。

### 8.2 Env-shadow compatibility

はい。ただし env-shadow は compatibility layer であり、truth ではない。

Stage B で `set` が old env-shadow slot も更新しているなら、Stage C の restored frame でも同じ互換性を保つ方が安全である。

推奨:

```text
when creating CatchBody env in defer_catch_body:
  clone env
  if state snapshot exists:
    shadow state_def with snapshot.state

when resuming StateFrames:
  push RuntimeStateHandlerFrame as truth
  optionally install scope_state_shadow for state_def as compatibility
```

`set` 時には今まで通り active frame を更新し、compat shadow も更新する。もし shadow update ができない箇所があるなら、counter を入れて generic fallback へ落とす。

```text
known_state_frame_shadow_resume_installs
known_state_frame_shadow_resume_missing
known_state_frame_shadow_update_fallbacks
```

### 8.3 Counters

`known_state_frame_entries/exits` は catch entry/exit の数を意味するなら、resume restore では増やさない方が読みやすい。別 counters にする。

```text
known_state_frame_entries              // real catch entry
known_state_frame_exits                // real catch exit
known_state_frame_snapshots            // crossing known-state catch
known_state_frame_forks                // resume restores forked frames
known_state_frame_resume_entries       // restored dynamic frame push
known_state_frame_resume_exits         // restored dynamic frame pop
known_state_frame_resume_request_rewraps
known_state_frame_snapshot_missing_frame
known_state_frame_snapshot_max_depth
known_state_frame_multishot_forks
```

こうしておくと、real handler entry と continuation branch restore が混ざらない。

---

## 9. How this avoids breaking shared state outside nondet/list

壊さないための rule は 1 行で言える。

```text
A state frame is forked only if the request continuation crosses that state handler boundary.
```

Case 1 では nondet/list handler が `each` を内側で捕まえる。outer state handler boundary は crossed しない。だから snapshot/fork されない。outer state frame は active なままで、nondet branches は同じ state frame を見る。

```text
outer state frame x active
nondet captures/resumes continuation inside list handler
x frame is not in captured continuation
branch 1 mutates x -> 1
branch 2 sees same x -> 2
final x -> 2
```

Case 2 では request が state handler boundary を越えて outer multi-shot handler に捕まる。だから state frame は continuation の一部として snapshot される。

```text
outer handler captures k that includes inner state handler C
request crosses C
C snapshot stored in k
resume k #1 -> fork C snapshot -> mutation local to branch
resume k #2 -> fork C snapshot again -> starts from captured state
```

この rule は algebraic effect の dynamic extent と一致している。

---

## 10. Minimal Stage C canary before Stage D

まず質問の 2 ケースをそのまま canary にするべきである。

### C1: state outside nondet/list remains shared

```yulang
use std::control::nondet::*

{
  my $x = 0
  my ys = {
    my b = each [true, false]
    &x = $x + 1
    $x
  }.list
  (ys, $x)
}
```

Expected:

```text
run roots [([1, 2], 2)]
```

Counters should show:

```text
known_state_frame_snapshots: 0 for the nondet continuation crossing
known_state_frame_forks: 0 for x
```

The exact global count may not be 0 if surrounding runtime creates other requests, so the test can be more robust by adding a deep counter keyed by catch/plan or by comparing branch behavior.

### C2: state inside outer multi-shot captured continuation forks

Pseudo source:

```yulang
outer_multi_shot_twice {
  my $x = 0
  &x = $x + 1
  $x
}
```

Expected conceptual result:

```text
[1, 1]
```

not:

```text
[1, 2]
```

If Yulang has a convenient nondet-style outer handler that captures a continuation outside the state handler, use that. The point is that the request must cross the known-state catch before being handled.

Counters:

```text
known_state_frame_snapshots >= 1
known_state_frame_forks >= 2 for two resumes
known_state_frame_multishot_forks >= 1
```

### C3: mutation before capture is captured

```text
state starts 0
set to 10
outer operation captures continuation crossing state catch
resume twice
both branches start from 10
```

Expected:

```text
[11, 11]
```

not `[11, 12]`, not `[1, 1]`.

### C4: nested state handlers preserve order

```text
outer x
inner x or y
request crosses both
resume twice
inner and outer snapshots restore independently
```

Expected: no cross-write, no same-family collision.

### C5: request during resumed state scope rewraps current state

This catches the `StateFrames` wrapper Request case.

```text
resume branch enters restored state frame
set x = 1
then throws another effect before leaving state scope
outer handler resumes that later
state should still be x = 1 in that continuation
```

Counter:

```text
known_state_frame_resume_request_rewraps > 0
```

This canary is easy to miss, and it is exactly where a one-shot push/pop wrapper loses state.

---

## 11. Is active frame hit + KnownOperationPlan still insufficient for Stage D?

Yes. Still insufficient if the operation object remains:

```text
generic-fallback
legacy_bridge=true
no-candidate-handler
```

Reason:

```text
active frame hit proves only that a compatible frame happens to be on the stack.
It does not prove that this operation call is allowed to access it.
```

A wrong implementation could pass the same active-frame check in cases like:

```text
same operation path/name but different hygienic family
blocked route
callback boundary
provider shadowing
generic user ref that happens to call an operation with same shape
```

Therefore, active-frame hit is a runtime guard, not a route proof.

The route proof must be a plan object created before runtime execution. Runtime guard then confirms the proof's dynamic assumptions.

---

## 12. Exact proof object for Stage D

The candidate shape in the question is close. I would shape it like this:

```rust
#[derive(Debug, Clone, PartialEq, Eq)]
struct KnownStateOperationRouteProof {
    operation_expr: ExprId,
    apply: ExprId,
    callee: ExprId,

    plan_id: EvidenceVmKnownHandlerPlanId,
    catch_expr: ExprId,
    handler_id: u32,
    role: RuntimeEvidenceKnownStateOperationKind, // Get | Set

    source: KnownStateOperationRouteProofSource,
    visibility: KnownStateOperationVisibilityProof,
    payload: KnownStateOperationPayloadProof,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum KnownStateOperationRouteProofSource {
    CompilerLocalVar {
        synthetic_var: SyntheticLocalVarId,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum KnownStateOperationVisibilityProof {
    CleanKnownStateCatch {
        catch_expr: ExprId,
        plan_id: EvidenceVmKnownHandlerPlanId,
        handler_id: u32,
        no_delayed_boundary: bool,
        no_callback_boundary: bool,
        no_blocking_marker: bool,
    },

    ExistingAllowedSet {
        allowed_set_id: EvidenceVmAllowedSetId,
        handler_id: u32,
    },

    ProviderGrant {
        demand_slot_id: u32,
        provider_slot_id: u32,
        handler_id: u32,
        hygiene_baseline: EvidenceProviderHygieneBaseline,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum KnownStateOperationPayloadProof {
    UnitPayloadForGet,
    SingleValuePayloadForSet,
}
```

For the current local-ref case, the first usable variant should be `CleanKnownStateCatch`. Do not begin with `ProviderGrant` unless the existing provider machinery can produce a clean grant proof without dirty dynamic scope.

`ExistingAllowedSet` is useful if the normal operation object route starts producing real `candidate_handler`. But your current blocker is `no-candidate-handler`, so the missing concept is specifically `CleanKnownStateCatch` / compiler-certified known-state operation route.

### Why `CleanKnownStateCatch` is not source-name matching

It is not based on source path strings. It is based on compiler/specialize identity:

```text
synthetic local var id
known state handler plan id
operation call expr id
operation role from certificate
catch expr id
handler object id for the known state get/set arm
```

The compiler generated both the handler and the operation call sites. The proof says: this operation call is one of the generated accesses for this generated local state handler, and the Evidence VM verified that the call is inside the handler's clean dynamic region.

---

## 13. Where should this proof be produced?

### 13.1 Lowering

Lowering should not produce the final route proof. It should produce stable facts.

```rust
struct SyntheticLocalVarStateAccess {
    synthetic_var: SyntheticLocalVarId,
    apply: ExprId,
    callee: ExprId,
    role: StateGetOrSet,
}
```

and existing state handler certificate:

```rust
struct SyntheticLocalVarStateHandlerCertificate {
    synthetic_var: SyntheticLocalVarId,
    handler_expr: ExprId,
    state_def: DefId,
    family: EffectFamilyId,
    get_op: OperationId,
    set_op: OperationId,
}
```

Lowering knows it created these nodes, but it should not decide marker/provider hygiene alone.

### 13.2 Specialize / runtime evidence surface

This is where the facts should be carried without losing identity.

```rust
struct RuntimeEvidenceKnownStateAccessSurface {
    synthetic_var: SyntheticLocalVarId,
    apply: ExprId,
    callee: ExprId,
    role: StateGetOrSet,
    handler_expr: ExprId,
}
```

If current `RuntimeEvidenceSurface` already carries known state handlers but not individual access call sites, add this. This is the missing bridge from `KnownOperationPlan` candidate to a target handler without path matching.

### 13.3 Evidence VM object plan

Evidence VM should produce the final `KnownStateOperationRouteProof` by joining:

```text
known state handler plan P
+ known state access surface A
+ handler object ids for P.get/P.set
+ control/evidence boundary analysis for A.apply -> P.catch_expr
```

Plan-time acceptance:

```text
A.synthetic_var matches P.source.synthetic_var
A.handler_expr == P.handler or maps to same known-state catch
A.role selects P.get_handler_id or P.set_handler_id
A.apply/callee match actual operation call object
no delayed/callback/blocking boundary invalidates the clean catch route
payload shape matches role
```

If accepted:

```rust
EvidenceVmKnownOperationPlan {
    direct_ready: true,
    reject: None,
    route_proof: Some(KnownStateOperationRouteProof { ... }),
}

EvidenceVmOperationObjectPlan {
    execution: EvidenceVmOperationExecutionPlan::DirectStateGet { proof_id }
    // or DirectStateSet { proof_id }
}
```

If not accepted, keep `GenericFallback` and retain reject reason.

### 13.4 Runtime route lookup

Runtime should not invent the proof. It should only look up proof by `(apply, callee)` or `operation_expr` and run guards.

```text
runtime lookup:
  direct_state_operation_for_call(apply, callee) -> proof_id
```

### 13.5 Catch entry / active frame stack

Catch entry creates the dynamic frame. It is not a route proof producer.

It supplies runtime guard material:

```text
active frame with plan_id/catch_expr/state_scope_id
current state value
branch/fork identity
```

---

## 14. How to move from `no-candidate-handler` to direct-ready

Do not try to coerce the existing generic operation object into having `candidate_handler` from active frame hit. Instead, add an explicit known-state access route source.

Current problem:

```text
operation object has no candidate_handler
because generic route model does not know this local generated access targets the generated state handler
```

Fix:

```text
lowering/specialize carries SyntheticLocalVarStateAccess
Evidence VM joins it with KnownHandlerPlan::State
Evidence VM creates KnownStateOperationRouteProof
KnownOperationPlan no longer rejects no-candidate-handler for certified local state access
```

New reject taxonomy:

```text
no-candidate-handler
  means: neither normal route nor known-state access route exists

no-known-state-access-proof
  means: known operation candidate exists, but no compiler/surface access identity

known-state-access-handler-mismatch
  means: access synthetic var does not match known handler plan

known-state-access-boundary-unsafe
  means: delayed/callback/blocked boundary prevents clean route
```

For current compiler-generated local refs, `candidate_handler` may remain absent in the old field, but `KnownStateOperationRouteProof` supplies a direct target. That is fine. Do not overload `candidate_handler` if it means only normal provider/allowed-set route.

---

## 15. Where direct execution should run

Direct execution should replace the exact point where generic effect request would be materialized, not payload evaluation.

Given the current flow mentions effect thunk creation and later force producing a request, the safest position is:

```text
when forcing the effect thunk / materializing the operation request
```

not at raw effect-op application, unless effect-op application is already where payload has been evaluated under existing semantics.

The invariant is:

```text
payload evaluation order must be identical to the generic path.
DirectStateGet/Set only replaces request allocation + handler dispatch.
```

A good runtime shape is:

```rust
enum PendingEffectExecution {
    Generic { path, payload, continuation, ... },
    DirectStateGet { proof_id, payload_expr_or_value, continuation, ... },
    DirectStateSet { proof_id, payload_expr_or_value, continuation, ... },
}
```

or as continuation frames:

```rust
EvidenceContinuationFrame::DirectStateOperationPayload {
    proof_id: KnownStateOperationRouteProofId,
    role: StateGetOrSet,
    apply: ExprId,
    callee: ExprId,
}
```

For `set`, payload must be evaluated first. If payload evaluation yields a request, append the direct-state payload continuation frame exactly like the generic path would append an apply/request frame. When payload finally becomes a value, run guard + write.

For `get`, if the generic operation call evaluates a unit payload, still evaluate it. Do not skip unit/payload evaluation unless the IR proves it is a pure literal unit and existing semantics permit that shortcut.

---

## 16. Runtime algorithm for direct `get`

Plan-time state:

```rust
EvidenceVmOperationExecutionPlan::DirectStateGet { proof_id }
```

Runtime:

```rust
fn execute_direct_state_get(
    &mut self,
    proof_id: KnownStateOperationRouteProofId,
    payload: SharedValue,
    fallback: GenericOperationFallback,
) -> EvidenceResult {
    let proof = self.runtime_context.known_state_route_proof(proof_id);

    if !matches!(proof.role, StateGet) {
        self.stats.direct_state_guard_reject_wrong_role += 1;
        return self.execute_generic_operation(fallback, payload);
    }

    if !self.payload_matches_get(&proof.payload, &payload) {
        self.stats.direct_state_guard_reject_payload += 1;
        return self.execute_generic_operation(fallback, payload);
    }

    let Some(frame_index) = self.find_visible_state_frame(proof) else {
        self.stats.direct_state_guard_reject_missing_frame += 1;
        return self.execute_generic_operation(fallback, payload);
    };

    if !self.known_state_visibility_guard_holds(proof) {
        self.stats.direct_state_guard_reject_visibility += 1;
        return self.execute_generic_operation(fallback, payload);
    }

    self.stats.direct_effect_calls += 1;
    self.stats.direct_state_get_calls += 1;
    self.stats.direct_state_frame_hits += 1;

    let value = self.active_state_handler_frames[frame_index].state.clone();
    EvidenceResult::Value(value)
}
```

Frame lookup:

```rust
fn find_visible_state_frame(&self, proof: &KnownStateOperationRouteProof) -> Option<usize> {
    self.active_state_handler_frames
        .iter()
        .rposition(|frame| {
            frame.plan_id == proof.plan_id
                && frame.catch_expr == proof.catch_expr
                && frame.state_scope_matches_current_branch()
        })
}
```

Do not look up only by operation path. Do not select the first active frame with a matching family name.

---

## 17. Runtime algorithm for direct `set`

`set` differs from `get` only in payload and write order.

```rust
fn execute_direct_state_set(
    &mut self,
    proof_id: KnownStateOperationRouteProofId,
    new_value: SharedValue,
    fallback: GenericOperationFallback,
) -> EvidenceResult {
    let proof = self.runtime_context.known_state_route_proof(proof_id);

    if !matches!(proof.role, StateSet) {
        self.stats.direct_state_guard_reject_wrong_role += 1;
        return self.execute_generic_operation(fallback, new_value);
    }

    if !self.payload_matches_set(&proof.payload, &new_value) {
        self.stats.direct_state_guard_reject_payload += 1;
        return self.execute_generic_operation(fallback, new_value);
    }

    let Some(frame_index) = self.find_visible_state_frame(proof) else {
        self.stats.direct_state_guard_reject_missing_frame += 1;
        return self.execute_generic_operation(fallback, new_value);
    };

    if !self.known_state_visibility_guard_holds(proof) {
        self.stats.direct_state_guard_reject_visibility += 1;
        return self.execute_generic_operation(fallback, new_value);
    }

    self.active_state_handler_frames[frame_index].state = new_value.clone();
    self.update_state_env_shadow_if_present(proof.state_def(), new_value);

    self.stats.direct_effect_calls += 1;
    self.stats.direct_state_set_calls += 1;
    self.stats.direct_state_frame_hits += 1;

    EvidenceResult::Value(self.unit_value())
}
```

Payload evaluation order:

```text
1. evaluate set payload exactly as generic path
2. if payload evaluation raises request, suspend with DirectStateSetPayload frame
3. only after payload is value, run guard
4. only after guard succeeds, write frame.state
5. return unit
```

Guard failure after payload evaluation should not drop the payload. It should build the same generic operation request with that payload.

---

## 18. Runtime guard checklist

Necessary guards:

```text
proof exists for this operation call
role matches operation execution variant
payload shape/arity matches role
active state frame with plan_id + catch_expr exists
active frame is the nearest visible dynamic instance for that known state handler
visibility proof is still valid
provider grant, if used, is clean
no blocked/delayed/callback unsafe route is being bypassed
```

Where these are available:

```text
proof exists / role / payload:
  Evidence VM object plan / runtime context table

active frame:
  active_state_handler_frames

nearest visible dynamic instance:
  reverse stack lookup by plan_id/catch_expr/state_scope_id

hygiene proof:
  plan-time KnownStateOperationVisibilityProof
  plus runtime provider grant check if route kind is ProviderGrant

blocked/delayed/callback:
  plan-time reject; no DirectStateGet/Set variant emitted
```

For the first implementation, I would only enable direct route for `CleanKnownStateCatch` with no provider dirtiness. Keep `ProviderGrant` direct route as a later extension.

---

## 19. Guard failure fallback rules

Use fallback, not runtime error, for expected dynamic guard misses.

```text
missing active frame:
  counter + generic request fallback

visibility guard fails:
  counter + generic request fallback

payload mismatch:
  counter + generic request fallback

wrong role / proof table corruption:
  debug_assert + counter + generic fallback in release

known impossible invariant broken in debug:
  debug assertion is okay
```

Do not silently return an incorrect value. Do not panic in release unless the generic path would also be impossible. Fallback keeps Stage D rollable.

Plan-time failures should not produce `DirectStateGet/Set` at all.

```text
blocked route:
  plan reject, GenericFallback

delayed/callback unsafe:
  plan reject, GenericFallback

no known-state access surface:
  plan reject, GenericFallback
```

---

## 20. Required counters

### Stage C counters

```text
known_state_frame_snapshots
known_state_frame_snapshot_missing_frame
known_state_frame_snapshot_max_depth
known_state_frame_forks
known_state_frame_multishot_forks
known_state_frame_resume_entries
known_state_frame_resume_exits
known_state_frame_resume_request_rewraps
known_state_frame_resume_value_exits
known_state_frame_shadow_resume_installs
known_state_frame_shadow_resume_missing
```

### Stage D plan counters

```text
plan_known_operation_route_proofs
plan_known_operation_state_direct_ready_gets
plan_known_operation_state_direct_ready_sets
plan_known_operation_reject_no_known_state_access_surface
plan_known_operation_reject_handler_mismatch
plan_known_operation_reject_role_mismatch
plan_known_operation_reject_boundary_unsafe
plan_known_operation_reject_payload_shape
plan_known_operation_reject_legacy_bridge_only
```

### Stage D runtime counters

```text
direct_state_get_calls
direct_state_set_calls
direct_state_frame_hits
direct_state_frame_misses
direct_state_guard_reject_missing_frame
direct_state_guard_reject_visibility
direct_state_guard_reject_provider_dirty
direct_state_guard_reject_payload
direct_state_guard_reject_wrong_role
direct_state_generic_fallbacks
direct_state_payload_request_suspends
direct_state_payload_request_resumes
```

Keep existing counters too:

```text
direct_effect_calls
known_state_direct_gets
known_state_direct_sets
known_operation_state_get_candidate_hits
known_operation_state_set_candidate_hits
known_operation_state_get_active_frame_hits
known_operation_state_set_active_frame_hits
```

Expected after Stage D:

```text
direct_effect_calls > 0
plan_known_operation_state_direct_ready_gets == static get call site count
plan_known_operation_state_direct_ready_sets == static set call site count
direct_state_get_calls == dynamic get count
direct_state_set_calls == dynamic set count
late known_state_direct_gets/sets decrease for the same operations
```

---

## 21. Staged implementation plan with rollback points

### C0: Add snapshot data types and no-op debug output

Add structs and formatting only.

Rollback:

```text
unused data types, no behavior change
```

### C1: Snapshot on known-state catch crossing

Modify `defer_catch_body`:

```text
if catch_expr has known state plan and active frame exists:
  snapshot nearest frame for catch_expr
  wrap CatchBody in StateFrames(snapshot)
else:
  existing behavior
```

Gate:

```text
YULANG_VM_STATE_FRAME_CONTINUATION_SNAPSHOTS=0/1
```

Rollback:

```text
gate off -> existing CatchBody continuation only
```

### C2: Resume `StateFrames` wrapper

Implement push/fork/pop around inner continuation.

Important:

```text
if inner returns Request, rewrap request with updated StateFrames snapshot before popping
```

Rollback:

```text
gate off
```

### C3: Env-shadow compatibility

Install shadow when creating CatchBody env and while restoring frame if current runtime needs it.

Rollback:

```text
shadow install off, frame remains truth
```

### C4: Canaries

Add C1-C5 canaries above. Do not proceed to Stage D until these pass with compare-control.

### D0: Add known-state access surface

Lowering/specialize carries operation access identity:

```text
synthetic var id
apply
callee
role
handler expr
```

No behavior change.

Rollback:

```text
ignore surface
```

### D1: Build `KnownStateOperationRouteProof` plan-only

Evidence VM joins access surface with known handler plan and boundary analysis.

No runtime direct execution yet.

Rollback:

```text
print proof but keep GenericFallback
```

### D2: Runtime lookup + guarded fallback

Add runtime table and guard functions, but initially run guard in shadow mode only.

```text
if proof would direct and guard hits:
  increment shadow hit
else:
  increment shadow reject
still execute generic path
```

Rollback:

```text
shadow disabled
```

### D3: Enable DirectStateGet only

`get` is simpler because it does not write state.

Acceptance:

```text
compare-control match
direct_state_get_calls == expected dynamic get count
no missing frame / visibility reject in representative local-ref case
Stage C canaries still pass
```

Rollback:

```text
DirectStateGet gate off -> generic request
```

### D4: Enable DirectStateSet

Only after set payload order canary exists.

Acceptance:

```text
compare-control match
direct_state_set_calls == expected dynamic set count
assignment payload effect order preserved
Stage C canaries still pass
```

Rollback:

```text
DirectStateSet gate off
```

### D5: Remove late path reliance for direct-ready operations

Late catch-boundary direct get/set remains fallback for non-direct-ready cases. Do not delete it until direct route has broad canary coverage.

---

## 22. Things not to do

### 22.1 Do not snapshot all active frames at request creation

This breaks state-outside-nondet shared behavior.

### 22.2 Do not use active frame existence as proof

Active frame hit is a guard. It is not permission.

### 22.3 Do not treat `legacy_bridge=true` as direct visibility

Legacy bridge is not request-free proof. Add `KnownStateOperationRouteProof` instead.

### 22.4 Do not match source path strings

No `std.control.var`, no path suffix `get`/`set`, no source variable name, no benchmark path.

### 22.5 Do not append state frames after the original continuation

Wrap the continuation segment. State must be active during resumed code.

### 22.6 Do not bypass payload evaluation

Direct state op replaces request allocation, not payload evaluation.

### 22.7 Do not turn local refs into raw VM cells

State belongs to continuation-aware state frames. `StateRef` is a token, not storage.

### 22.8 Do not direct user/file/projected refs

Unless they later get their own certificates, they remain generic.

### 22.9 Do not add marker-stack-empty shortcuts

If provider/hygiene proof is missing, fallback. A dynamic “stacks are empty” shortcut is too weak and tends to miss the real hot path anyway.

---

## 23. Final answer to the numbered questions

### 1. Where should snapshots be stored?

In a new `EvidenceContinuationFrame::StateFrames` wrapper, or equivalent `EvidenceContinuation::state_frames(snapshots, inner)` continuation node. Do not store snapshots directly on `EvidenceRequest` as a global request property.

### 2. Where should the snapshot be created?

In `defer_catch_body`, when a request crosses a known-state catch boundary. Not at request creation. Not in generic `append_request_continuation` unless it receives an explicit snapshot from `defer_catch_body`.

### 3. Wrap or append after?

Wrap. `StateFrames(snapshot) { CatchBody(...) }`. Appending after is too late for direct state get/set during the resumed continuation.

### 4. Nested known-state handler ordering?

Preserve active stack order: push outer-to-inner, pop inner-to-outer. In the current one-known-state-per-catch shape, capture the nearest active frame for the crossed `catch_expr`; nested catches are captured as request propagation crosses each catch.

### 5. On resume, what to do?

Push forked snapshot frames onto `active_state_handler_frames` for the duration of the resumed continuation. Install env-shadow compatibility if needed, but keep frame as truth. Use separate snapshot/fork/resume counters, not only existing entry/exit counters.

### 6. How avoid breaking shared state outside nondet/list?

Do not snapshot active frames merely because they are active. Snapshot only when the request continuation crosses that state handler's catch boundary. State outside nondet/list is not crossed by inner nondet request, so it remains shared.

### 7. Minimal canary before Stage D?

Add both ordering cases: state outside nondet/list yields `([1, 2], 2)`, and state inside an outer multi-shot captured continuation forks per resume. Also add request-during-restored-state rewrap canary.

### 8. Is active frame hit + KnownOperationPlan still insufficient?

Yes. If operation remains `generic-fallback` / `legacy_bridge=true` / `no-candidate-handler`, direct execution is not justified. Active frame hit is guard evidence, not route proof.

### 9. What exact proof object is needed?

Add `KnownStateOperationRouteProof`, built from compiler/specialize known-state access identity joined with `KnownHandlerPlan::State` and boundary/hygiene analysis. This proof moves compiler-certified local state operations from `no-candidate-handler` to direct-ready without path matching.

---

## 24. Summary

The safe path is:

```text
Stage C:
  snapshot state frames only when request crosses their known-state catch boundary
  store snapshots as continuation wrappers
  wrap, do not append after
  fork on resume
  rewrap if resumed continuation emits another request

Stage D:
  add explicit KnownStateOperationRouteProof
  do not rely on active frame hit or legacy_bridge
  execute direct get/set only after payload evaluation
  fallback generically on guard failure
```

This preserves both required semantics:

```text
state outside nondet/list:
  shared across branches

state inside captured continuation:
  forked per resumed branch
```

and it gives a clean route from the current 66ms late-direct state to real request-free `DirectStateGet/Set` without source-name/path matching or raw local cells.
