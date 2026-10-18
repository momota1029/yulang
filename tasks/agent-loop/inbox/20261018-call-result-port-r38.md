Sprint-ID / contract revision and SHA-256:
ordinary-call-result-owner-20261018-r38 / rev2 /
f119bf4f031ab8b28fd060921723ddb235bf208ff3b48a87bc169aa1b7fa0421

Assignment-ID / handoff revision:
R38-IMPLEMENT-PORT-CORRESPONDENCE / rev1

Parent gate / original theorem and scope locator:
Full Yulang inference/executor theorem with unchanged Simple-sub A/B, source
domain, recursive worlds, both frames, aliases, arbitrary W, complete
Call/effects, F1/FK1, N-Transport, soundness, principality and termination.
R38 rev2 §1; no parent condition closed.

Baseline / direct dependency hashes:
Baseline 887eed4370278cd9e789fb2b9b10ff58369da540.
candidate_call.rs e038ad0dfc4b12bd0d513d6cd6b2b062d8b33368bc1c0dcdef980d479
(unchanged); shadow_apply.rs input
5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb;
Call definition 20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c;
Generalize proof e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240;
synthesis A 71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992;
inference principles 7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81;
R37 closeout 5c1aa3ea9f653a73d5f7466f61f9cbc32bc641fcc56ac5eeed6ff3da201f1d44.

Role / worker / session / runtime receipt:
Implementation worker / session current-conversation-2026-10-18 /
assignment acknowledged by Luna. Requested Luna/high; observed model and
effort UNKNOWN.

Exact leased paths / authors:
Test-only section of crates/yu-solver/src/shadow_apply.rs, authored by
/root/r38_call_result_impl; notes/progress/2026-10-18-call-result-port-r38.md;
this inbox handoff. candidate_call.rs was inspected but not changed.

Outcome class:
source-native-evidence (test-only candidate; unexecuted).

Parent application:
For source `my loop y = loop y`, candidate execution ties the authentic Apply
occurrence to its ApplySourceInput.result component and NativeInterface.result;
the negative Function demand projects to the exact ordered argument,
argument-effect, invocation-effect and result children. This supplies focused
native port evidence only. `PendingCallSupplier::OriginalGenCall0` and the
unresolved premise set remain. The original result-description owner, scope
and complete ordered logical telescope remain open. Synthesis A stays intact:
the expression-body result is not conflated with an inert returned
computation-data interface, and no port is inferred from solved effect rows.
NativeInterface has no separate returned-provider/world port, so no provider
correspondence is claimed. Original theorem conditions remain 0 -> 0.

Source constructors -> constraints -> propagation -> consumer/native path:
LocalSource Apply and occurrence -> ApplySourceInput recipe incidence ->
admit_candidate_fact allocates invocation effect and negative Function demand,
retains NativeInterface -> candidate constraint propagates during
InferenceSession::execute -> test observes original four demand ports and
result endpoint. This is not a logical telescope or source typing derivation.

Artifact locators / hashes / review snapshot:
shadow_apply.rs d5e6b179fd4f6fbca579b0fa4d479d8bd11b520d774acbf27f414451c4691137.
Progress note notes/progress/2026-10-18-call-result-port-r38.md (hash recorded
after freeze by Luna). This handoff is frozen rev1; hash recorded after freeze
by Luna. No independent review yet.

Checks, coverage, omitted cases, budget:
`git diff --check -- crates/yu-solver/src/shadow_apply.rs` passed. No Cargo,
build, test, probe or formatter ran. New Rust test is unexecuted. Controls
mutate checking occurrence, substitute application effect for invocation
effect, substitute another Apply result endpoint, and substitute the callee
endpoint for NativeInterface.result. Provider/world identity and telescope
ordering are outside what this native record can represent. 900-second grant
fully charged; Astra0.

Next related step / TODO:
Fresh compiler review of frozen source occurrence, result endpoint and
four-port projection. Proof lane owns the original result-owner and ordered
telescope gap. Falsifier: an authentic source occurrence whose emitted demand
or retained result maps to a different Apply endpoint/port, or an observation
that accepts any listed substitution. Cargo remains gated by all applicable
clean reviews and Luna's separate launch receipt.

Mutual TODOs:
Proof owner: identify actual ordinary Call result introduction for q=loop y,
its scope, original ordered dependency telescope and typed field correspondence
to ApplySourceInput.result / NativeInterface.result; retain a complete Call
alternative falsifier. Native owner: if provider/world correspondence becomes
representable, supply a source-authenticated provider identity and distinguish
it from the body/result port before extending this test. This handoff grants no
writes outside the frozen leases.

Worker state / writes-stopped receipt / descendants:
STOPPED WRITING after the single leased owner test edit and two leased text
outputs; no descendants. Requested/observed model remains Luna/UNKNOWN.

Commit-ready / integration:
Pending fresh review and Luna adjudication; not commit-ready or independently
certified.
