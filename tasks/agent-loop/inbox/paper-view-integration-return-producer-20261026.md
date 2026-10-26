# Frozen source producer handoff: PAPER-VIEW-INTEGRATION-RETURN-PRODUCER-20261026/r1

## Receipt and scope

Author/worker: `/root/vip_source`, assigned registered `implementer`; requested model/effort Luna/high defaults; observed model/effort/session metadata UNKNOWN. No descendants. ACTIVE receipt was sent to Luna before source work. This frozen handoff is the source-lane result for contract SHA-256 `eefcbdb006a269073151148b34bdde88fde39b6b3fdfdfae3b1c993b25d9a3f7`, baseline `aee0a705ece848ec917abd08c1618af6b8dc8252`.

Sole authored paths are this handoff and `notes/theory/2026-10-26-force-return-producer-correspondence.md`. No Rust/HIR/compiler/Lean source was edited. No checker, test, Cargo, build, runtime probe, formatter, Git mutation, nested CLI, or child assignment was used. Source packet allowance was 600 active seconds; estimated source inspection and drafting was about 300 seconds. Process/checker/probe usage was 0. No scratch/generated paths were created. Writer stopped after these two files were frozen.

## Outcome and parent application

Constructed the actual source/native lifecycle for the existing concrete Function-valued result fixture:

```text
HIR relay formal + owned annotation tree
  -> program Lambda root_schema at program.rs:819–850
  -> RootCompSchema::original_parameter
  -> closure invocation and Receiving::enter
  -> exact Execute formal consume opens C
  -> delayed argument evaluates actual lambda W
  -> RootCompReturn closes C execution and preserves W's exact result record
  -> outer result/cache/forwarding preserves W; later Call selects closure by value
```

The fixture at `machine.rs:3115–3145` covers concrete `int -> int` plus symbolic, forwarding, captured and replayed result records. It asserts preservation of actual `(value, interface, view, dispatch)` at RootCompReturn; it was read but not rerun. C is the RootComp view of the consumed delayed argument, and W is the actual returned lambda's result view. They are distinct same-execution owners; no value/pointer identity equation was substituted.

HIR retains annotation owner/position, nested Function argument/result tree, formal ID/source key/range/scope, lambda/body owner/occurrence, and member header/root-formal data. Thus the previous native report's “no fields encode χ” conclusion is rejected. The first exact missing output is the **source result-edge exporter from `RootCompSchema::original_parameter` / program Lambda and member-template construction**: they export the raw `(SourceSite, LocalSourceParameter)` schema and code/body but no source-owned same-execution result slot/instance connecting nested `C.result`, actual producer W and W's typed interface/body-result derivation. `RootCompReturn` closes the exact execution and preserves W; it emits no `C.result` transport. Later Callee dispatch selects the actual closure but does not open W's complete typed view. This is an exact absent current operation, not an impossibility proof: the retained owner/formal/body tree and Image/Boundary chains might support a derivation.

Effectful nested-result annotation is retained as raw input only. The source form `thunk:[] (int -> [io] int)` plus an actual `io`-performing returned function and a later complete Call under a source `io` consumer is a useful discriminator for the next owner derivation. An annotation alone is not an inferred T/profile, producer instance, or proof of an edge.

Reuse `ReturnView(C,W) = M_W* W union_tagged M_C* V_C` and the established FL12 frontier criterion. Current direct result preservation identifies W's actual record, but does not prove all W paths map by identity. C's entry image does not establish `M_C` over `C.result`; no concrete frontier equality can be claimed because the result-edge batch is not exported and later Call does not open the complete W view. FL12 and the parent theorem remain OPEN.

## Artifacts and exact source evidence

Author artifact: `notes/theory/2026-10-26-force-return-producer-correspondence.md`.

Direct source hashes match the frozen contract: program.rs `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907`; machine.rs `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e`; receiving.rs `57b1664e26f137e6425731dde2bb1f1559170d9914f5be7a0f17fae3a8555e26`; source_annotation.rs `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f`; local_source.rs `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1`; source_role.rs `d16945ae153d25cdadea9e9071cdfc2ab73925b46d92e598a0e18e5d60f4d3e3`; source_identity.rs `4bd5fa4066a1fd445a9757374c44d602decd1d791a394cd81c6066efa063fb23`.

Additional evidence reused: `notes/theory/2026-10-16-runtime-function-result-source-construction.md` §§3–5; `notes/theory/2026-10-16-runtime-function-result-view-projection.md` §3 and §§4–5; `notes/theory/2026-10-25-force-local-applicability.md`; `tasks/agent-loop/sprints/paper-view-exposure-20261026-r1-outcome.md`; `tasks/agent-loop/inbox/paper-view-exposure-20261026-native.md`. The native lifecycle equations were reused; the overstrong field-name impossibility inference was rejected by primary's prior outcome.

Exact source paths and line locators, unresolved premises, and the concrete same-execution account are in the authored note. No proof/checker evidence was produced by this source packet.

## Open TODOs and next in-envelope step

1. Source result/elimination owner: derive the typed `C.result` edge and actual W producer/result descriptor from the retained owner/formal/body tree and its real source instance. Keep C/W, owner, source tags and nested effect positions distinct. Falsifier/consumer: use a nested effectful returned callable and compare its later complete Call against an otherwise matching pure result under an `io` consumer.
2. Program Lambda/member constructor owner: export the derived producer-specific result descriptor without inventing source T/profile from annotation shape.
3. Runtime source/native owner: relate that exported edge to the actual RootCompReturn record and identify how later Call opens/observes the same W view across full invocation and its designated result consumer. Any changed code requires a new exact lease from Luna.

The original parent is still full inference/executor soundness over the unchanged A/B/source domain with concrete source/native correspondence. It remains OPEN, as do source instance/profile construction, semantic approval for the full result transport, complete Call, symbolic/captured/replayed generality, R62/R23 and production. This packet establishes no safe Rust slice; Rust remains `NO_SAFE_CODE_SLICE`. No source restriction, diagnostic, expectation, natural inference, or semantics changed.

Handoff ID: `PAPER-VIEW-INTEGRATION-RETURN-PRODUCER-20261026/r1-source`. No self-certification is claimed.

Frozen correspondence note SHA-256: `914fdcd19eb512247bd347cf8d82acd6aa4d2348351faaa74858671abd496a50`. The handoff's own SHA-256 is reported alongside the file by the worker receipt to avoid a self-referential hash.
