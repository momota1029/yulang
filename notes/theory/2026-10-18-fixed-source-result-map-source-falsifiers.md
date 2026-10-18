# R22 fixed-source result map: independent source falsification

Status: FROZEN research-only source/native characterization; independent review pending.
Author: `/root/r22_result_map_falsifiers`; no descendants.
Baseline: primary-pinned `3436209db`, `research/simple-sub-intrusion`.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN; original conditions closed **0**.

## Objective, method, and evidence boundary

Independently inspect the exact admitted R20 local-g specimen's saved suffix and actual arm-result route, then compare returning the resumed response, discarding that intermediate result, and returning another provider. Inputs are the R22 contract, CLEAN R20 prefix/use analysis, frozen R21 options/falsifiers, and baseline runtime/source owners. This lane reads baseline Git objects so simultaneous observational runtime edits cannot enter its premises.

The result is a bounded manual characterization of existing native transitions. No source-qualified counterexample was obtained. R20's reported 18/18 run supplies admission/execution evidence only for its exact fixtures; none of the new mutations below inherits that admission. The characterization does not derive a new `Orig` constructor, typed field transport, source adequacy, or any original universal theorem. The constructive source proof belongs to the separate prover lane.

## Exact fixed specimen and identities

The source is exactly `operation_v1_local_binding_source()` in baseline `runtime_resume.rs:81–86`, built from `operation_v1_runtime_source("42", "next")`:

```yu
act outer:
    our next: () -> int
    our other: () -> int
act signal:
    our ping: () -> (int -> [outer] int)
my relay (thunk:[signal, outer] int) = catch thunk { outer::next(), _ -> 42, value -> value }
my main = relay { my g = catch signal::ping() { signal::ping(), k -> { my response: int -> [outer] int = \x -> outer::next(); my other_response: int -> [outer] int = \x -> outer::next(); k response }, v -> v }; g 0 }
```

Here `response` and `other_response` are distinct local definitions and Lambda occurrences, despite equal annotation/body text. If both initializers execute, `allocate` allocates separate value handles. Let r denote the actual response closure handle read by the exact argument Name, b the other closure, and o the actual containing execution owner at request selection. Numeric IDs, source byte ranges, actual template ordinal and dynamic trace are unobserved in this lane. The enclosing `g` initializer frame is outside the selected inner Catch delimiter.

## Actual saved suffix is empty; the template still has an owner

The following owner calculation uses baseline `machine.rs`, not the proposed R21 ResultMap clauses:

1. Evaluating the direct `signal::ping()` pushes `Frame::Callee`, then creates an operation invocation with `OperationResultConsumer`, `ReceiverReturn`, and `OperationPayload` (`645–658`, `995–1067`). The Unit argument has no intervening user suffix. `OperationPayload` creates an inert request carrier (`873–876`, `1789–1804`).
2. That carrier returns through `ReceiverReturn` first. Only after leaving the operation invocation does the popped `OperationResultConsumer` execute the carrier (`877`, `1070–1080`). `execute` initializes `PendingRequest.suffix = Vec::new()` (`1929–1964`). The consumer itself is therefore **not** a remaining saved suffix frame for this request.
3. The next frame is this direct scrutinee's `CatchReturn`, installed before scrutinee evaluation (`707–737`). Selection inspects it before unwinding any frame (`1550–1630`). On this exact successful route, no frame is appended to `request.suffix` before `capture_template`.
4. `capture_template` initializes `Hole`, adds no loop node for the empty suffix, then adds the mandatory containing `Owner` wrapper (`1314–1378`). Thus the native template is `Owner(o,Hole)`, not a zero-node template and not an arbitrary identity assumption about `A_decl`.
5. Shallow selection pops the selected delimiter and evaluates the operation arm (`1633–1684`). It does not save a `ForwardHandler` for this selected Catch. Consequently its ordinary `v -> v` arm does not execute when this raw continuation returns. A value-arm identity cannot be used to justify this leg; that arm is absent from the resumed route.

This distinguishes the raw suffix from the whole enclosing program continuation. The pending `Local(g)` and subsequent `g 0` remain below the selected delimiter; they are not part of k's saved raw suffix. In contrast, an actual nonempty scrutinee such as a Block that discards ping's result would add its own remaining frame(s). The direct-scrutinee v1 matcher does not certify that other shape (`candidate_source.rs:715–718`).

## Bounded actual-value preservation through the fixed arm

Assume the baseline accepted source/candidate, exact selected request/arm and k binder, an actual response evaluation yielding r with valid receiving view, and successful runtime validation/owner transitions. This is an explicit conditional native statement, not a proof that every decorated source state satisfies those premises.

`Frame::ResumeArgument` uses the received response and enters the retained template after pushing `ResumeReturn` (`748–818`). `TemplateNode::Owner` resolves/enters the original owner and pushes its return restoration; `Hole` sets `State::Return(response)` (`1381–1438`). Owner exit restores control while preserving `ReceivedValue`; `ResumeReturn` preserves it; `ReceiverReturn` preserves its value handle and view while presenting Value interface (`820–832`, `1070–1080`). No body or output provider is executed between this Hole and k's result for this saved template. These clauses quantify over any received r for which their runtime checks succeed; they are not inferred from the concrete scalar result 42.

In the fixed source the operation arm's Block final expression is this exact `k response`. `begin_local` executes the two callback initializers, then evaluates that final expression without inserting another result-producing expression (`1889–1927`). After k's return there is no pending arm binding or arm value-arm wrapper to replace r. The next enclosing `Local(g)` stores the actual `received.value` unchanged (`1099–1166`). The result map at this native value level is therefore r at the raw return, k result, actual arm result and installed g cell, conditional on the stated valid-transition premises. Later g consumption checks the exact resolved cell; invoking the closure is a subsequent computation, not an identity of its returned integer with r.

Native constraint owners keep distinct interfaces: the Block's `CandidateRelation::Group` child is its actual `final_expression` (`candidate_source.rs:1428–1441`); Catch slot 50 receives each actual arm endpoint (`1148–1168`); Install(g) installs the Catch root. None of these typed comparisons equates `R_response`, FreshUse S, `R_ping`, `R_k`, `R_catch` or the operation's `original` endpoint. A runtime handle equality does not identify those type endpoints or establish m0's typed incidence through them. In particular this result addresses the fixed value-origin route only; the annotation-root seam remains independently open.

## Discriminating mutations and admission ledger

Each mutation starts from the exact source above and changes only the indicated final arm suffix. These are source candidates, not established counterexamples.

| Case | Exact replacement of final `k response` | Value-origin distinction conditional on admitted execution | Actual evidence here |
| --- | --- | --- | --- |
| C0 fixed return | unchanged | k result and arm final result are r | Baseline fixture admission and receipt reported by R20; manual transition calculation above |
| C1 discard intermediate, return same response | `my ignored = k response; response` | k result is discarded into ignored; final resolved Name independently reads r. Same value does not make the ignored Apply the arm's final expression. | Parse/HIR/candidate/runtime UNVERIFIED |
| C2 discard intermediate, substitute provider | `my ignored = k response; other_response` | k still returns r; actual Block final Name returns distinct b, which is installed into g. Existence of h_arg(k,response) cannot justify r-origin at g. | Parse/HIR/candidate/runtime UNVERIFIED |
| C3 discard intermediate, return integer | `my ignored = k response; 0` | If evaluated, arm result is integer, not response closure; final `g 0` likely fails candidate typing/admission and must be checked rather than assumed accepted. | Parse/HIR/candidate/runtime UNVERIFIED |
| C4 saved suffix replaces response | Change scrutinee to a Block ending in another callback | Raw k itself may return the other provider, before arm finishing. This is outside the direct Apply scrutinee matched by current v1. | Hypothetical/original-open; no v1 admission claim |

The independently inspected matcher recursively searches arm bindings and final expression for the unique resolved k Apply (`candidate_source.rs:668–727`); this supports only a conditional shape calculation for C1–C3. It does not prove their full admission or receipt. R21 already identified C2 as an unexecuted candidate. R22's additional discriminator is the exact dynamic separation between the actual raw return and actual installed final provider, with a fixed suffix calculation. Repeating a toy model of `let ignored=K(r) in b` would leave source admission untouched and is not performed.

C0 and C2 intentionally keep both callbacks invoking `outer::next`. Both may consequently finish at integer 42. Scalar agreement is unable to distinguish provider origin. A different-provider run needs the actual distinct Lambda source occurrences and dynamic value handles; family/body/annotation equality is insufficient. Changing other_response to `outer::other` would add a separate behavior and admission change and is unnecessary for this discriminator.

## Minimal Luna-owned observation, if scheduled

Within the R22 reviewed observational code lease, add only C2 beside the intact C0 fixture. Construct it by a single replacement of `k response }` with `my ignored = k response; other_response }`, assert exactly one replacement, and retain the baseline source separately. For **each** source independently:

1. Record empty parse diagnostics, successful HIR lowering, exact candidate-mode HIR-error owner check, and the same-HIR `solve_operation_v1_research` result/conflicts and actual field-bound receipt. Stop and classify the first failing gate; do not repair admission or attach the original source's receipt to C2.
2. If admitted, construct `RuntimeProgram::evidence_for_operation_v1` and `RuntimeProgram::from_hir` from that source's own candidate/HIR. Run its raw Machine under the existing 30,000-step bound. Preserve actual Unavailable/Unhandled/noncompletion outcomes rather than requiring a successful Phase-R receipt.
3. Read the approved bounded observation trace: the captured template shape/order; actual response handle/site; actual raw resumed return; actual operation-arm final returned handle/site; installed g handle/source; actual closure invocation provider; completion. Compare dynamic handles separately from static occurrences. C0 predicts r throughout its pre-invocation value route. C2 predicts raw return r and final/install b, with r != b and distinct Lambda sites if that execution reaches those points.
4. Treat withholding of the specialized runtime receipt honestly. Its existing checks require the selected response closure at the exact later invocation; C2 may fail that receipt by design. That failure alone proves neither rejection of the source nor a result-origin counterexample. Only demonstrated admission plus actual divergent result-origin evidence can upgrade C2 from candidate.

This is one proposed exact check, not a run or instruction to enlarge the lease. Luna owns tests, review and any integration. The contract's focused target can include this observation only after its independent code review. No test/build/source edit occurs in this packet.

## Independence, omissions, resources, and parent application

Oracle independence is methodological: direct baseline frame-stack/transition inspection was performed independently of the constructive author and does not assume proposed ResultMap transitions. Shared premises are existing source meaning, baseline runtime correctness at the inspected owners, exact R20 admission report and resolved source identities. There is no independent executable oracle. No checker, generator, random seed/range, enumeration, mutation engine, Cargo/test/build, formatter, network, Git mutation, subagent or background work was run. Reads/searches/Git-object hashes and document writes only. Reserve/charge the assigned 600 seconds conservatively; exact active CPU accounting is unknown.

Omitted: actual modified-source admission and execution, complete source-to-decorated typed maps, arbitrary continuation suffixes, foreign providers, repeated resume/world/view changes, effect hygiene, m0-to-annotation incidence, field-specific capture/FreshUse acknowledgement, F1/FK1, full Call, soundness, principality and termination. The fixed native route does not prove all these premises or parent quantifiers. No original condition is closed here.

Recommended next action: consume this exact `Owner(o,Hole)`/actual-final-value characterization in the separate fixed-source proof and, only after independent observational-code review, have Luna run C0/C2 with fresh admission and actual handle/site evidence. If C2 admission fails, record that exact owner and leave it a candidate; do not substitute another unadmitted toy probe.

## Frozen input manifest

All source reads used `git show 3436209db:<path>` for the baseline runtime/source files. The following baseline hashes match the R22 contract where listed there; concurrent working-tree trace changes are not dependencies of this artifact.

```text
fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46 tools/inference-playground/src/runtime/machine.rs
194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3 tools/inference-playground/src/runtime/continuation.rs
484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11 tools/inference-playground/src/runtime/program.rs
3902e5071d9d2bc8bede6cc03fe74e224cf12627de7bcfc147ec850b9fd560bd tools/inference-playground/tests/runtime_resume.rs
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c crates/yu-solver/src/candidate_source.rs
1ab75dd2b5210068ce272de81e41ee42d38c57d41a3b8d193d11b4f1b3387ddd notes/theory/2026-10-18-fieldbound-prefix-and-use-construction.md
f97d6ca85b60a5eec8bc20d98fcdf75904551eaacbdc5084026289362681676a notes/design/2026-10-18-field-root-incidence-bridge-options.md
1e85ae26d7caf678a28ec2cafe59ca4c8f6186a9f07de6b00d5f426cf2efb699 notes/theory/2026-10-18-field-root-incidence-bridge-soundness.md
a881422001c4d3544e714a17f78681dc44e2360b204b6c362ea83a542908489e notes/theory/2026-10-18-field-root-incidence-source-falsifiers.md
85236a281bd8abaa90bf2b3d1a88163bfe1ad2d64a3a4113b64cd0c269eae56f tasks/agent-loop/sprints/fixed-source-result-map-existing-semantics-20261018-r22.md
```

Historical raw-capture and matched-Catch notes were read solely to preserve their conditional/control-versus-typed-interface limitations; neither is adopted as a new rule or used to fill an unsupplied typed result constructor. Writes stop after the companion handoff and final hash report. Review remains pending; no self-certification.
