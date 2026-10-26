# PAPER-VIEW-EXPOSURE-20261026/r1 — outcome

Status: ENDED_ACCEPTED_RESEARCH_RESULT. The fixed bounded outcome is accepted; original parent gates remain OPEN.
Baseline `2f9b5a2a1255563dcc9567953be1374b0662acb1`, branch `yulang3`.
Contract SHA-256 `40a4a48f6ee071c215b8f689b5d010bbced5a38a24803a5ec0908a6987dee172`.

## Original parent and before/after

The parent remains Lean execution safety for the entire declared source language, original inference A/B and concrete source/native correspondence. No supported language case or original quantifier is removed. Before this sprint, the actual computation judgment had no expose constructor and the frozen R63 witness could not step in the connected executor. R63's accepted old-judgment obstruction was preserved and pushed in `2f9b5a2a1255563dcc9567953be1374b0662acb1` before this sprint.

After this sprint, the real judgment admits exposure and its mutual type/term transport/support and graph weakening proofs handle it. The new connected fallback takes `force (view metadata (delay body))` to `expose metadata body`, retaining exact metadata, body and arbitrary existing let stack. Previous successful transitions have priority. Generic successful-step preservation and the same-witness typed/context/erasure theorem are constructed and independently checker-accepted. R62's entire dependency cone rebuilds under the extended real judgment. Applying the result to the original R63 unit witness establishes a typed first step.

The next expose state still has no outgoing step, proved explicitly by `expose_not_dispatched`. Full View execution is therefore OPEN, including result-path metadata, request/continuation remainder, active expose frames, nested views and Call/View. R62 finite constructor observation/guard/source realization, R23, whole-language safety, source/native, inference A/B and production remain OPEN. This bounded advance cannot certify progress, Bad-exclusion or whole-language safety.

## Implementation/source evidence

Registered implementer `/root/view_exposure_native` traced the frozen `machine.rs::consume` -> `Receiving::execution` -> `execute_with_substitution` -> `RootCompReturn`, including request observations, frame capture and fresh-occurrence replay. These are concrete identity/lifecycle equations. No Rust edit is authorized within this sprint (`NO_SAFE_CODE_SLICE`).

Primary accepts the exact native equations and the unproved mapping, and rejects the native report's stronger impossibility wording. The inspected fields lack an established correspondence to paper χ; that does not prove Image/Boundary chains cannot encode one. Proposed distinct-path falsifiers are not instantiated counterexamples. No source-generated metadata derivation was provided. Native handoff worker identity is authoritatively `/root/view_exposure_native` by actual collaboration handle, despite its internal worker-ID UNKNOWN entry; effective runtime metadata remains UNKNOWN.

## Checks, failures and provenance

Proof author `/root/vep`: 8 calls, 72.440866556 checker seconds. Calls 3/5 rebuilt the actual dependency component; calls 4/6/7/8 failed and remain failures. Code repair addressed symbolic stack reduction. The final worker audit parsed private numeric names incorrectly and emitted only 110 public declarations.

Primary `/root`: independent source copy, four calls, 81.327363459 checker seconds, all exit 0. Actual Lean 4.35.0 / Lake 5.0.0-src+eb6cafb; fixed no-package project; one heavyweight process, LEAN_NUM_THREADS=1, -j1 -M1024, per-process120s. Primary scratch audit resolves actual runtime Names by user name and source module and passes them through mkIdent to #check/#print axioms. Exact source-declaration enumeration and full audit:119 = Syntax4 + TypingSubstitution35 + TermSubstitution51 + GraphWeakening16 + ViewExecution13, including9private and5inline-attribute theorems. Axioms:5empty,9[propext],105[propext,Quot.sound]. All13 new-module theorems use[propext,Quot.sound]. No project axiom or sorryAx.

Thirty frozen input pins match baseline/working tree. Exactly five isolated source files differ; recursive internal cone22 modules passes supplemental static scan. Complete type/axiom transcript and all process/capture identities are preserved in primary receipt. All worker16 and primary8 captures match their recorded hashes/lengths. A Python manifest-schema TypeError during primary bookkeeping was corrected; no Lean/source change resulted. Importing the validator generated an unleased primary-owned Python bytecode file at `.agents/skills/yulang-lean-proofs/scripts/__pycache__/check_lean.cpython-312.pyc`; after validator cessation, primary removed exactly that file. This output-scope deviation did not modify reviewed source/receipts. No blanket cleanup occurred.

No default target build, root-import integration, repository Lean source edit, Rust/Cargo, tests, manifest/dependency change or expected-output change occurred. The source candidate is preserved below as a complete reconstructible patch against the pinned baseline. Read-only forward `git apply --check` on the repository baseline and reverse `git apply --reverse --check` on the primary candidate both passed.

## Review and adjudication

Fresh non-author `/root/ver` reviewed the exact frozen five-source component and primary audit without checker runs or writes. Receipt `tasks/agent-loop/inbox/paper-view-exposure-20261026-review.md`, SHA-256 `053437dc1b031cfc0c241cbb6df51eb367a357d422c8e8a651cc5a4fa3a07515`, has no BLOCKING/major/minor finding. Primary adjudicates ACCEPTED for the exposure-entry/structural bridge and limited native equations. Native encoding impossibility claims are excluded. The reviewer checked all24 capture hashes and preserved the separate worker failures/primary success. Reviewer STOPPED, no descendants. This closes the fixed bounded sprint outcome, not the original parent theorem or production gate.

## Remaining owner and next boundary

Primary owns routing `PAPER-VIEW-EXPOSURE-NATIVE-META-01`: establish the paper/native metadata representation and producer, and source-justified request exposure/continuation replay/result transfer operations. For the concrete resulting state, first exhibit the correct transition from `expose metadata (ret unit)` without assuming result-path metadata equals entry metadata. Reuse actual source equations; require a concrete discriminating trace or constructive relation, not field-name absence.

The unchanged parent remains OPEN. Subsequent source integration requires a separate exact lease and bounded integration verification envelope; no promotion is implied by this record checkpoint.

## Runtime and leases

Both producers delivered STOPPED/writes-stopped/no-descendant receipts. Primary checker completed. Fresh reviewer delivered STOPPED/no-writes/no-descendants receipt. Effective runtime UUID/model/effort and exact total active work UNKNOWN, with no unobserved duration returned to budget. Source intake approximated190/240seconds; proof allowance1800, primary1260, reviewer300; no budget renewal. Nine historical UNKNOWN reservations retain their quarantined paths and global slots. Resolved R63-rebuild workers/leases alone were archived to `history/20261026-r63-rebuild-resolved.json`; current state remains the sole mutable queue.

## Artifact identities

- `tasks/agent-loop/inbox/paper-view-exposure-20261026-native.md`: `3f3660eb29930a1f6ed71f27e49efc4a0dc740a0354bd248028c5287b5549c65`.
- `tasks/agent-loop/inbox/paper-view-exposure-20261026.md`: `b688bb816e91465df6656443b2ea111bb12fa0539f674fbcee1f4166ef7783cf`.
- `tasks/agent-loop/inbox/paper-view-exposure-20261026-primary.md`: `6ae8d8f04aa8ab65f5996d0ea12e3be47fe6fbda2243d85b320542c13226ce1f`.
- `tasks/agent-loop/history/20261026-r63-rebuild-resolved.json`: `8eb3beb761d7606b31f0b8e2ce7ee0b8c4d3e73b6c65d4d139e2d0231f5b0d0f`.

Source output SHA-256 (same bytes in both copies):

```text
d3a10c0891b0518fef7ed6e02c899b996d3ac6de618e07bddde11c89ef616bfe  notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean
cb0941ef8842551da53fbf2b14cca181c10849178288de29cef1145f1d575cc7  notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean
d2dde517343a18b03a8fb0fe113b1d0fceeef2751f53792ef39886d8ed5e9c94  notes/theory/lean/YulangClosure/PaperTermSubstitution.lean
5fcb0334dfa77c3385f5f460669e36578a01642a54d17e357c072fd012fc73fe  notes/theory/lean/YulangClosure/PaperExecutionGraphWeakening.lean
e7c6c959d2bcc780ca7198aae09a0368f4d98625001bdfe5b8f8c259c9cb3f85  notes/theory/lean/YulangClosure/PaperViewExecution.lean
```

## Sprint-end dispatcher and checkpoint

Reused `/root/goal_next_sprint_dispatch` returned STOPPED with no writes/checkers/descendants/Git. It independently rehashed contract and four receipts, recommended closing only the fixed bounded research outcome and preserving the complete five-file patch. Primary adopts that recommendation. No new sprint, source lease, semantic approval or budget renewal is issued.

The beyond-envelope proposal is constructive source/native correspondence for Force normal leave: follow actual Image/Boundary producers and consumers, construct the representation map and prove the transfer diagram commutes. A concrete pair of constructed source paths collapsing improperly to one native representation, or an actual transfer-equation mismatch, would falsify a proposed map. Field-name absence and an assumed map are insufficient. This next proposal has not launched workers or changed semantics.

This checkpoint contains exactly current state, contract/outcome, four sprint receipts and the contract's R63 resolved-history archive. Full branch/index/outbound-range review and ordinary push remain primary Git duties after this immutable receipt freeze. The checkpoint SHA is the containing commit, recoverable with `git log -1 --format=%H -- tasks/agent-loop/sprints/paper-view-exposure-20261026-r1-outcome.md`; the final user receipt reports the actual pushed SHA. Repository sources remain the original baseline; the recoverable candidate is the embedded patch.

The following completed leases leave compact current state only after acceptance and cessation. Historical UNKNOWN reservations are untouched; there are no retained child workers recorded RUNNING. Exact frozen temporary artifacts remain under primary custody for reproduction.

```json
{
  "workspaces": {
    "VE-proof": "/tmp/yulang-paper-view-exposure-20261026/proof",
    "VE-primary": "/tmp/yulang-paper-view-exposure-20261026/primary",
    "VEp": "/tmp/yulang-paper-view-exposure-20261026/proof/notes/theory/lean",
    "VEv": "/tmp/yulang-paper-view-exposure-20261026/primary/notes/theory/lean"
  },
  "resolved_leases": [
    {
      "path": "tasks/agent-loop/inbox/paper-view-exposure-20261026.md",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "tasks/agent-loop/inbox/paper-view-exposure-20261026-primary.md",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "tasks/agent-loop/inbox/paper-view-exposure-20261026-review.md",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "tasks/agent-loop/sprints/paper-view-exposure-20261026-r1.md",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "tasks/agent-loop/sprints/paper-view-exposure-20261026-r1-outcome.md",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "tasks/agent-loop/history/20261026-r63-rebuild-resolved.json",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "tasks/agent-loop/inbox/paper-view-exposure-20261026-native.md",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VEp/YulangClosure/PaperExecutionSyntax.lean",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VEp/YulangClosure/PaperExecutionTypingSubstitution.lean",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VEp/YulangClosure/PaperTermSubstitution.lean",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VEp/YulangClosure/PaperExecutionGraphWeakening.lean",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VEp/YulangClosure/PaperViewExecution.lean",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VEp/.lake/ExposureAudit.lean",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VEp/.lake/ExposureProbe.lean",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VEp/.lake/build",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-proof/lake-build",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-proof/run_call.py",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-proof/process-manifest.json",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-proof/proof-checks.txt",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-proof/call-01.stdout",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-proof/call-01.stderr",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-proof/call-02.stdout",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-proof/call-02.stderr",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-proof/call-03.stdout",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-proof/call-03.stderr",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-proof/call-04.stdout",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-proof/call-04.stderr",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-proof/call-05.stdout",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-proof/call-05.stderr",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-proof/call-06.stdout",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-proof/call-06.stderr",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-proof/call-07.stdout",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-proof/call-07.stderr",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-proof/call-08.stdout",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-proof/call-08.stderr",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VEv/YulangClosure/PaperExecutionSyntax.lean",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VEv/YulangClosure/PaperExecutionTypingSubstitution.lean",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VEv/YulangClosure/PaperTermSubstitution.lean",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VEv/YulangClosure/PaperExecutionGraphWeakening.lean",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VEv/YulangClosure/PaperViewExecution.lean",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VEv/.lake/ExposureAudit.lean",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VEv/.lake/ExposureProbe.lean",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VEv/.lake/build",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-primary/lake-build",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-primary/run_call.py",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-primary/process-manifest.json",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-primary/proof-checks.txt",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-primary/call-01.stdout",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-primary/call-01.stderr",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-primary/call-02.stdout",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-primary/call-02.stderr",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-primary/call-03.stdout",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-primary/call-03.stderr",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-primary/call-04.stdout",
      "owner": "/root",
      "state": "FROZEN"
    },
    {
      "path": "VE-primary/call-04.stderr",
      "owner": "/root",
      "state": "FROZEN"
    }
  ],
  "authors": {
    "proof": "/root/vep",
    "native": "/root/view_exposure_native",
    "primary": "/root",
    "review": "/root/ver",
    "dispatcher": "/root/goal_next_sprint_dispatch"
  },
  "cessation": "All named children delivered STOPPED, no descendants; proof/primary checkers completed. Runtime model/effort/session UUID UNKNOWN. Exact source/scratch bytes retained frozen under primary custody; no UNKNOWN lease reclaimed."
}
```

## Exact source patch against baseline

The patch bytes inside this fence end with a newline; SHA-256 `504f4638df3304fdd02bd2469eed2fc1891a5780ae8a336587e20464e08bcb4f`.

```diff
--- a/notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean
+++ b/notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean
@@ -831,6 +831,10 @@
     | absurd {value resultType} :
         PaperValueTyped declarations graphTypes environment value .bottom →
         PaperComputationTyped declarations graphTypes environment (.absurd value) resultType
+    /-- Exposure preserves the body type under the same shared contexts. -/
+    | expose {metadata body resultType} :
+        PaperComputationTyped declarations graphTypes environment body resultType →
+        PaperComputationTyped declarations graphTypes environment (.expose metadata body) resultType
     | fail {reason ty} :
         PaperComputationTyped declarations graphTypes environment (.fail reason) ty
 
--- a/notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean
+++ b/notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean
@@ -456,6 +456,9 @@
     (by intro declarations graphTypes environment value resultType hvalue ihValue σ
         simpa only [mapPaperComputation, subst] using
           PaperComputationTyped.absurd (resultType := subst σ resultType) (ihValue σ))
+    (by intro declarations graphTypes environment metadata body resultType hbody ihBody σ
+        simpa only [mapPaperComputation] using
+          (PaperComputationTyped.expose (metadata := mapViewMetadata σ metadata) (ihBody σ)))
     (by intro declarations graphTypes environment reason ty σ; simpa [mapPaperComputation, subst] using PaperComputationTyped.fail)
     (by intro declarations graphTypes environment owners binder body responseType resultType hbody ihBody σ
         have ihBody := ihBody σ
--- a/notes/theory/lean/YulangClosure/PaperTermSubstitution.lean
+++ b/notes/theory/lean/YulangClosure/PaperTermSubstitution.lean
@@ -67,6 +67,7 @@
     | .perform op ts v => .perform op ts (renameTermValue f v)
     | .template n ts vs => .template n ts (vs.attach.map fun ⟨v,hv⟩ => renameTermValue f v)
     | .request op p k => .request op (renameTermValue f p) (renameTermValue f k)
+    | .expose metadata body => .expose metadata (renameTermComputation f body)
     | .fail r => .fail r
     | c => c
   termination_by c => sizeOf c
@@ -223,6 +224,9 @@
     (by intro declarations graphTypes environment value resultType hvalue ihValue target f h
         simpa only [renameTermComputation] using
           PaperComputationTyped.absurd (resultType := resultType) (ihValue target f h))
+    (by intro declarations graphTypes environment metadata body resultType hbody ihBody target f h
+        simpa only [renameTermComputation] using
+          (PaperComputationTyped.expose (metadata := metadata) (ihBody target f h)))
     (by intro declarations graphTypes environment reason ty target f h
         simpa only [renameTermValue_record_eq, renameTermValue, renameTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.fail)
     (by intro declarations graphTypes environment owners binder body responseType resultType hbody ihBody target f h
@@ -292,6 +296,7 @@
     | .perform op ts v => .perform op ts (replaceTermValue rho v)
     | .template n ts vs => .template n ts (vs.attach.map fun ⟨v,hv⟩ => replaceTermValue rho v)
     | .request op p k => .request op (replaceTermValue rho p) (replaceTermValue rho k)
+    | .expose metadata body => .expose metadata (replaceTermComputation rho body)
     | .fail r => .fail r
     | c => c
   termination_by c => sizeOf c
@@ -461,6 +466,9 @@
     (by intro declarations graphTypes environment value resultType hvalue ihValue target rho h
         simpa only [replaceTermComputation] using
           PaperComputationTyped.absurd (resultType := resultType) (ihValue target rho h))
+    (by intro declarations graphTypes environment metadata body resultType hbody ihBody target rho h
+        simpa only [replaceTermComputation] using
+          (PaperComputationTyped.expose (metadata := metadata) (ihBody target rho h)))
     (by intro declarations graphTypes environment reason ty target rho h
         simpa only [replaceTermValue_record_eq, replaceTermValue, replaceTermComputation, List.attach_map_val, List.map_nil, List.map_cons] using PaperComputationTyped.fail)
     (by intro declarations graphTypes environment owners binder body responseType resultType hbody ihBody target rho h
@@ -496,6 +504,7 @@
     | .split v _ b => supportedTermValue v && supportedTermComputation b
     | .unionCase v _ l _ r => supportedTermValue v && supportedTermComputation l && supportedTermComputation r
     | .template _ _ vs => vs.attach.all fun ⟨v,hv⟩ => supportedTermValue v
+    | .expose _ body => supportedTermComputation body
     | .fail _ => true
     | _ => false
   termination_by c => sizeOf c
@@ -636,6 +645,8 @@
         simpa only [supportedTermComputation] using ihValue)
     (by intro declarations graphTypes environment value resultType hvalue ihValue
         simpa only [supportedTermComputation] using ihValue)
+    (by intro declarations graphTypes environment metadata body resultType hbody ihBody
+        simpa only [supportedTermComputation] using ihBody)
     (by intro declarations graphTypes environment reason ty
         simp_all [supportedTermValue, supportedTermComputation, List.all_eq_true]
         all_goals assumption)
--- a/notes/theory/lean/YulangClosure/PaperExecutionGraphWeakening.lean
+++ b/notes/theory/lean/YulangClosure/PaperExecutionGraphWeakening.lean
@@ -89,6 +89,8 @@
         exact PaperComputationTyped.chooseRight (ihValue new hpres))
     (by intro declarations graphTypes environment value resultType hvalue ihValue new hpres
         exact PaperComputationTyped.absurd (ihValue new hpres))
+    (by intro declarations graphTypes environment metadata body resultType hbody ihBody new hpres
+        exact PaperComputationTyped.expose (ihBody new hpres))
     (by intro declarations graphTypes environment reason ty new hpres; exact PaperComputationTyped.fail)
     (by intro declarations graphTypes environment owners binder body responseType resultType hbody ihBody new hpres; exact PaperContinuationTyped.continuation (ihBody new hpres))
     derivation new hpres
--- /dev/null
+++ b/notes/theory/lean/YulangClosure/PaperViewExecution.lean
@@ -0,0 +1,171 @@
+import YulangClosure.PaperHeapExecution
+
+/-!
+Manuscript :485–493 exposure entry, with corrected V1/V4/V5 shared contexts.
+The existing syntax and actual typing judgment retain arbitrary metadata.
+Only Force of a view-wrapped literal Delay is added to the connected executor.
+Return-path and request/continuation metadata transfer remain unspecified here;
+no exposure completion, full View progress, guard, or native correspondence is claimed.
+-/
+namespace YulangClosure.PaperTypes.PaperViewExecution
+
+open PaperCoreControl
+
+/-- The exact body derivation is recovered without changing any shared context. -/
+theorem force_view_delay_inversion {d g e metadata body result}
+    (ht : PaperComputationTyped d g e (.force (.view metadata (.delay body))) result) :
+    PaperComputationTyped d g e body result := by
+  cases ht with
+  | force hv =>
+      cases hv with
+      | view hv =>
+          cases hv with
+          | delay hb => exact hb
+
+/-- Force/View enters exposure with the same metadata and suspended body. -/
+def forceViewStep : Computation → Option Computation
+  | .force (.view metadata (.delay body)) => some (.expose metadata body)
+  | _ => none
+
+theorem forceViewStep_preservation {d g e head next result}
+    (ht : PaperComputationTyped d g e head result)
+    (hs : forceViewStep head = some next) :
+    PaperComputationTyped d g e next result := by
+  cases head with
+  | force operand =>
+      cases operand with
+      | view metadata value =>
+          cases value with
+          | delay body =>
+              have he : Computation.expose metadata body = next := Option.some.inj hs
+              cases he
+              exact .expose (force_view_delay_inversion ht)
+          | _ => simp [forceViewStep] at hs
+      | _ => simp [forceViewStep] at hs
+  | _ => simp [forceViewStep] at hs
+
+/-- Every previous successful connected transition retains priority. -/
+def controlStep (d : DeclarationTable) (binder : TermName) (s : State) : Option State :=
+  match PaperExtendedExecution.controlStep d binder s with
+  | some next => some next
+  | none => (forceViewStep s.head).map (fun next => ⟨next, s.stack⟩)
+
+inductive ControlStepEvidence (d : DeclarationTable) (binder : TermName) :
+    State → State → Prop where
+  | existing {s next} : PaperExtendedExecution.ControlStepEvidence d binder s next →
+      ControlStepEvidence d binder s next
+  | exposure {head next stack} : forceViewStep head = some next →
+      ControlStepEvidence d binder ⟨head, stack⟩ ⟨next, stack⟩
+
+theorem controlStep_extends {d binder s next}
+    (hs : PaperExtendedExecution.controlStep d binder s = some next) :
+    controlStep d binder s = some next := by
+  simp only [controlStep, hs]
+
+theorem controlStep_evidence {d binder s next}
+    (hs : controlStep d binder s = some next) : ControlStepEvidence d binder s next := by
+  cases ho : PaperExtendedExecution.controlStep d binder s with
+  | some old =>
+      have he : old = next := Option.some.inj (by simpa only [controlStep, ho] using hs)
+      cases he
+      exact .existing (PaperExtendedExecution.controlStep_evidence ho)
+  | none =>
+      have hx : (forceViewStep s.head).map (fun c => (⟨c, s.stack⟩ : State)) = some next := by
+        simpa only [controlStep, ho] using hs
+      obtain ⟨c, hc, he⟩ := Option.map_eq_some_iff.mp hx
+      cases he
+      exact .exposure hc
+
+theorem evidence_preservation {d g e s next result binder}
+    (hd : PaperTemplateExecution.BodiesTyped d)
+    (ht : StateTyped d g e s result) (hs : ControlStepEvidence d binder s next) :
+    StateTyped d g e next result := by
+  cases hs with
+  | existing ho => exact PaperExtendedExecution.evidence_preservation hd ht ho
+  | exposure hb =>
+      obtain ⟨a, hh, hf⟩ := ht
+      exact ⟨a, forceViewStep_preservation hh hb, hf⟩
+
+theorem preservation {d g e s next result binder}
+    (hd : PaperTemplateExecution.BodiesTyped d)
+    (ht : StateTyped d g e s result) (hs : controlStep d binder s = some next) :
+    StateTyped d g e next result := evidence_preservation hd ht (controlStep_evidence hs)
+
+/-- Existing principal/context evidence and the concrete new entry under lets. -/
+inductive ComputationStep (d : DeclarationTable) (binder : TermName) :
+    Computation → Computation → Prop where
+  | existing {head next} : PaperExtendedExecution.ComputationStep d binder head next →
+      ComputationStep d binder head next
+  | exposure {head next} : forceViewStep head = some next → ComputationStep d binder head next
+  | underLet {head next body} : ComputationStep d binder head next →
+      ComputationStep d binder (.letE head body) (.letE next body)
+
+theorem plug_step {d binder head next} (hs : ComputationStep d binder head next)
+    (stack : List Computation) :
+    ComputationStep d binder (plug stack head) (plug stack next) := by
+  induction stack generalizing head next with
+  | nil => exact hs
+  | cons body rest ih => exact ih (.underLet hs)
+
+theorem evidence_erasure {d binder s next} (hs : ControlStepEvidence d binder s next) :
+    erase s = erase next ∨ ComputationStep d binder (erase s) (erase next) := by
+  cases hs with
+  | existing ho =>
+      cases PaperExtendedExecution.evidence_erasure ho with
+      | inl he => exact .inl he
+      | inr hp => exact .inr (.existing hp)
+  | @exposure head next stack hb => exact .inr (plug_step (.exposure hb) stack)
+
+theorem erasure {d binder s next} (hs : controlStep d binder s = some next) :
+    erase s = erase next ∨ ComputationStep d binder (erase s) (erase next) :=
+  evidence_erasure (controlStep_evidence hs)
+
+/-- Same arbitrary existing stack and exact metadata/body, without a table law. -/
+theorem controlStep_force_view_delay (d : DeclarationTable) (binder : TermName)
+    (metadata : ViewMetadata) (body : Computation) (stack : List Computation) :
+    controlStep d binder ⟨.force (.view metadata (.delay body)), stack⟩ =
+      some ⟨.expose metadata body, stack⟩ := by
+  cases stack <;> rfl
+
+/-- The same witnesses supply the actual step, typed result and erased context step.
+The new entry needs no code-table well-typedness or closedness assumption. -/
+theorem force_view_delay_control {d g e metadata body stack result binder}
+    (ht : StateTyped d g e ⟨.force (.view metadata (.delay body)), stack⟩ result) :
+    controlStep d binder ⟨.force (.view metadata (.delay body)), stack⟩ =
+      some ⟨.expose metadata body, stack⟩ ∧
+    StateTyped d g e ⟨.expose metadata body, stack⟩ result ∧
+    PaperComputationTyped d g e (erase ⟨.expose metadata body, stack⟩) result ∧
+    ControlStepEvidence d binder
+      ⟨.force (.view metadata (.delay body)), stack⟩ ⟨.expose metadata body, stack⟩ ∧
+    ComputationStep d binder
+      (erase ⟨.force (.view metadata (.delay body)), stack⟩)
+      (erase ⟨.expose metadata body, stack⟩) := by
+  obtain ⟨a, hh, hf⟩ := ht
+  have last : StateTyped d g e ⟨.expose metadata body, stack⟩ result :=
+    ⟨a, .expose (force_view_delay_inversion hh), hf⟩
+  exact ⟨controlStep_force_view_delay d binder metadata body stack, last,
+    erase_typed last, .exposure rfl, plug_step (.exposure rfl) stack⟩
+
+/-- Application to the original represented R63 witness, retaining arbitrary metadata. -/
+theorem original_obstruction_entry (d : DeclarationTable) (binder : TermName)
+    (metadata : ViewMetadata) :
+    controlStep d binder
+      ⟨.force (.view metadata (.delay (.ret (.literal .unit)))), []⟩ =
+      some ⟨.expose metadata (.ret (.literal .unit)), []⟩ ∧
+    StateTyped d [] [] ⟨.expose metadata (.ret (.literal .unit)), []⟩ (.base .unit) ∧
+    ComputationStep d binder
+      (.force (.view metadata (.delay (.ret (.literal .unit)))))
+      (.expose metadata (.ret (.literal .unit))) := by
+  have initial : StateTyped d [] []
+      ⟨.force (.view metadata (.delay (.ret (.literal .unit)))), []⟩ (.base .unit) :=
+    ⟨_, .force (.view (.delay (.ret .literal))), .nil⟩
+  obtain ⟨hs, ht, _, _, hp⟩ := force_view_delay_control (binder := binder) initial
+  exact ⟨hs, ht, hp⟩
+
+/-- This packet supplies no speculative result-path completion operation. -/
+theorem expose_not_dispatched (d : DeclarationTable) (binder : TermName)
+    (metadata : ViewMetadata) (body : Computation) (stack : List Computation) :
+    controlStep d binder ⟨.expose metadata body, stack⟩ = none := by
+  cases stack <;> rfl
+
+end YulangClosure.PaperTypes.PaperViewExecution
```
