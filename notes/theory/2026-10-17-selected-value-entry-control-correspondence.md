# Selected Value-entry control correspondence for the returned `step`

Date: 2026-10-17  
Status: **bounded source correspondence candidate; revision 3 after compiler-referee MAJOR repair**  
Sprint: `receive-checked-inlet-bridge-and-entry-control-20261017`, contract rev3  
Contract SHA-256: `91fa2981f48b907d6915c4dd3d1a939bfcb4704b4a3252ef9fac529478a1d7f2`  
Parent Goal: 型推論と実行器が証明込みで実装できるまで続ける

## 1. Claim and boundary

For the selected source

```yu
my apply f = { my step x = f x; step }
```

static source inspection supports this bounded control-order claim: on the
returned `step` closure's **Value-entry** path, the playground allocates the
whole argument as inert `Delay`, chooses entry from that lambda formal's own
annotation, places `ValueEntry` before running the delay, and binds the same
formal only after the delay returns. A pending Request during that force unwinds
the exact unfinished suffix, including `ValueEntry`; a captured continuation
can restore that frame before the eventual rebind and body evaluation. A
non-resuming handler abandons the suffix, and an unhandled request stops with
the suffix retained in its returned continuation handle.

This matches the phase order of the selected `Strict(I_x,x:A_x,R_c,IF_step)`
Value-entry constructor, conditional on its independent whole-carrier
admission, typed result/rebind and complete pending/resumption premises. This
is a **source control correspondence**, not a proof that the playground
runtime realizes every semantic descriptor observation. In particular it
does not establish original F2 admission, source `T`, native MODEL, arbitrary
`c₂`, full typed-view simulation, semantic Pure/Handler from Value/Computation,
or execution behavior by running the interpreter. No code lease follows.

## 2. Phase correspondence

| Selected `Strict` phase | HIR/runtime control path | Supported correspondence and limit |
|---|---|---|
| Formal and entry | `program.rs:382-402` copies the parameter ID and chooses `Value` exactly when that formal's own annotation has no effect row. Prior trace rev3 establishes the selected `step/x` HIR ID and closure owner. | Value-entry classification is annotation-owned. It does not establish semantic Pure/Handler or any original F2 view. |
| Whole argument prepared | `machine.rs:661-677` allocates an inert `ExecutableValue::Delay {code, environment}` after callee return. No argument prefix is evaluated before entry selection. `receiving.rs:114-129` gives the Delay its own view identity with inherited image/unknown status. | Corresponds to the not-yet-forced whole carrier. This only records the runtime object/view; it is not proof of `I_x` admission or `T_B_in`. |
| Designated Value-entry Force | `machine.rs:693-714` creates the invocation owner, pushes `ReceiverReturn`, then pushes `Frame::ValueEntry`, then executes the Delay. `execute` at `:1581-1586` enters its code/environment. | The unfinished body and formal binding are suspended while the entire delayed argument runs. This is the selected Value-entry Force phase; no formal is bound early. |
| Actual Force Return and rebind | `return_value` handles `Frame::ValueEntry` at `machine.rs:819-836`: it binds `Binder::Parameter(parameter)` to the actual received value/view and only then sets `State::Evaluate {body,...}`. | Matches the selected actual-result rebind followed by `R_c` body entry in order. It does not prove the semantic result typing, lawful action, or current-world inclusion. |
| Request during Force | Executing a request value at `machine.rs:1587-1606` records the actual declaration/payload/event/observations and enters `State::Request`. `propagate_request` at `:1367-1413` unwinds one frame at a time, retaining ordinary frames as `SavedFrame::Ordinary`. `ValueEntry` enters the unfinished suffix only when propagation crosses it before reaching a matching `CatchReturn`. | Preserves a pending path without asserting a Return/rebind. Each request sees only the runtime's actual observation set; this is not universal descriptor coverage. |
| Inner handler, no continuation | Stack bottom-to-top is `ReceiverReturn(step), ValueEntry(x), CatchReturn(inner), local work`. `propagate_request` examines the top matching `CatchReturn` before popping it (`:1235-1357`). | The saved/abandoned suffix contains only local work above the delimiter. `ValueEntry` and `ReceiverReturn` remain live. The handler arm's eventual Return reaches `ValueEntry`; `return_value` binds that returned value to `x` and evaluates the original step body (`:819-836`). Thus this inner non-resuming arm does not abandon the original body. |
| Inner handler, captured continuation | The same stack placement applies. `capture_template` stores the request suffix above `CatchReturn`, then selection pops that delimiter (`:1013-1082,1235-1357`). | The captured continuation excludes `ValueEntry` and `ReceiverReturn`. Resumption restores only the local suffix. When the handler arm eventually Returns its result, that result reaches the still-live `ValueEntry` and starts the body. The control restoration does not need to save or replay the outer entry frames. |
| Outer handler, no continuation | Stack bottom-to-top is `CatchReturn(outer), ReceiverReturn(step), ValueEntry(x), local work`. Propagation pops the ordinary work, `ValueEntry` and `ReceiverReturn` before reaching the outer delimiter (`:1367-1413`). | The suffix contains `ValueEntry` and the receiver boundary. Without a continuation, `abandon_suffix` abandons that unfinished invocation (`:1312-1315`); the handler arm's Return goes to the outer context and cannot enter the abandoned step body. |
| Outer handler, captured continuation | The same outer placement applies; propagation has crossed `ValueEntry` and the invocation boundary before selecting the handler. | The captured suffix contains the saved `ValueEntry` and receiver boundary as `Bind`/boundary nodes (`:1013-1082`; node forms in `continuation.rs:13-44`). Calling a continuation creates a response Delay and `ResumeArgument` (`:680-691`); response Return enters the saved template (`:575-601`), whose `Bind` nodes restore the suffix (`:1104-1107`). When the unfinished argument eventually Returns, restored `ValueEntry` binds the actual result and enters the original body. |
| Unhandled Request | `stop_unhandled_request` stores the accumulated suffix and returns `UnhandledRequest` with its continuation handle at `machine.rs:1415-1427`. | No completed force or body entry is asserted. The retained suffix contains `ValueEntry` only if propagation crossed that frame before exhausting the stack. Any later external continuation consumer is outside this correspondence. |

The runtime continuation template retains cloned frames and environment handles;
its `Bind` nodes do not run the saved frame early. The exact captured suffix is
delimiter-relative: a continuation captured by an inner handler has no
`ValueEntry` to restore because that frame remained live; one captured by an
outer handler restores `ValueEntry` because unwind crossed it. The previous
HIR trace establishes that the closure itself retains the same `step/x` formal
identity and captured lexical environment through allocation, local
return/alias and lookup. Combining those arguments links either the live or
restored ValueEntry binder to the original formal without candidate fresh-use
evidence transport.

## 3. Applied result and first remaining premises

The original runtime identity trace established *which* formal, closure and
environment are related. This trace adds *when* the returned closure forces,
rebinds, suspends and re-enters its body. It does not add a typed edge from the
original checked `I_x` to the runtime Delay view. In particular:

- `receiving.delay` copies an inherited image pointer/unknown bit; it does not
  enumerate the complete original `I_x` or `B_in` domain.
- Value entry does not call the Computation-entry `receiving.enter` path. The
  runtime's lack of that entry boundary is an implementation fact, not proof
  that every semantic Force interface is present or absent.
- Capturing/replaying these delimiter-relative runtime suffixes does not prove
  every independently admitted raw Resume, future use, observation, provider
  or context in selected `Strict`.
- The selected constructor's typed whole-carrier admission, result certificate,
  lawful rebind/action, current-world correspondence and invocation return
  remain inputs. The original F2 VIEW/CHECK source laws remain OPEN.

Thus the first broken **join for a full erasure theorem** is semantic evidence:
no pinned source rule maps the original `I_x`/`B_in` whole-carrier domain and
all typed pending/return observations to the runtime Delay view and these
operational transitions. The control order itself shows no counterexample on
the selected path. This is not a source-qualified counterexample to original
F2 and does not authorize enforcing SAT or adding runtime evidence.

`NO_SAFE_CODE_SLICE` remains justified: the inspected runtime owners already
preserve the selected entry/rebind/suffix order, while the absent join is the
original source-owned admission/typing law. If a later source bridge supplies
that premise and exposes a real implementation mismatch, Luna can scope a
separate minimal change with a concrete falsifier. No provisional code or test
is needed to choose the missing semantics now.

## 4. Source and dependency pins

All twenty contract revision-2 dependencies matched before this lane began.
The directly consumed runtime owners matched these exact current hashes:

```text
b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748  tools/inference-playground/src/runtime/program.rs
b8f15e4617a9d66940183c7327499ff8a2beb1e9cae2abb997137fc1ca464b82  tools/inference-playground/src/runtime/machine.rs
194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3  tools/inference-playground/src/runtime/continuation.rs
8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9  tools/inference-playground/src/runtime/receiving.rs
b65cfd7200e459c9448438ec979ffeb9eddb35c282600349cebe7ddf3b759bbb  tools/inference-playground/src/lib.rs
86c95b67c5dcb6fb03ed706838b6bde5da70639f53ba8594a85121821aa23ab5  notes/design/2026-10-17-receive-checked-inlet-view-check-bridge.md
f46ff320be6e018122c8e7dff149259bc6a4f4f1944f5920d4798b49e8c81a9d  tasks/agent-loop/inbox/20261017-receive-checked-inlet-view-check-bridge.md
```

Inherited HIR formal provenance is pinned by the full dependency manifest and
review receipt in the sprint contract. The source read remained within these
pins. No tests, build, probe, runtime execution, expected-output change, compiler
edit or scratch file was used. This revision is Luna's source-lane correction,
not its independent review.
