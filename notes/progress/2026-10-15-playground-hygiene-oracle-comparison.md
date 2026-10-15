# Playground hygiene: actual frozen Oracle comparison

Date: 2026-10-15
Status: independently reviewed finite research observations; omitted-callback
behavior differs from the current selected outcome, with its shared cause unresolved
Review: fresh M2 `spec_auditor`; no blocking/major findings. One exact source
locator was corrected by the primary. No general semantic parity was certified.
Native source baseline: `e9790f96f154ef0ddf67cb45aa26a569148569d7`
Native worktree checkpoint at dispatch: `67b82c2ba68ac6e8fbf533575ea331223604b32d`
Oracle: clean detached `a58eefc31e22141574b6f20c6a5748151c6d79f1`, built by primary; no build by this worker

## Objective, governing sources, and claim class

Compare actual frozen Oracle check, polymorphic dump, and evidence-VM results
against native source admission/annotation conflicts on eight small source
families. This is finite characterization, not a theorem or production test.
Authority remains inference top-level principles §§1/3/4; annotation hygiene
integration §§1/1.1; directional protection §2.1; compose release's “Scope of the
operation.” Existing proofs retain their stated hypotheses. Oracle observations
do not override selected source behavior. No compiler, fixture, or expectation
was changed.

The independent reference is the actual frozen Oracle compiler and evidence VM,
not a model built from assumed transition rules. Both sides nevertheless share
the supplied source programs, language ancestry, built-in type spellings, and
human-selected observational context. Native has no runtime in this comparison.
Agreement on solving or annotations cannot establish runtime parity or hygiene.

## Valid observations

All eight Oracle source checks and polymorphic dumps exit 0. No syntax-error
input is counted as a comparison. “Native conflict” means IncompatibleEffect;
“unsupported” is candidate unavailability, not language rejection.

| Case | Oracle forced runtime | Native paired source |
| --- | --- | --- |
| 01 pure value Catch, answer annotated `[] int` | Exit 0, `run roots [1]` | Exit 0 |
| 02 direct signal Catch, answer annotated `[] int` | Exit 0, `run roots [1]` | Exit 1, effect conflict |
| 03 omitted callback relay | Exit 0, `run roots [1]` | Exit 0 |
| 04 annotated callback, answer annotated `[] int` | Exit 0, `run roots [1]` | Exit 1, unsupported |
| 05 annotated computation, answer annotated `[] int` | Exit 0, `run roots [1]` | Exit 1, effect conflict |
| 06 mixed signal/write computation, answer annotated `[write] int` | Exit 1, unhandled `write::emit` | Exit 1, effect conflict |
| 07 independent same-operation emission in outside arm | Exit 1, unhandled `signal::ping` | Exit 0 |
| 08 same family, different unhandled operation | Exit 1, unhandled `signal::pong` | Exit 0 |

The Oracle prints these actual relay schemes (formatting retained):

```text
03: (() -> ['a] 'b) -> ['a] 'b | int
04: (() -> [signal] int) -> int
05/06: int [signal; 'a] -> ['a] int
```

The runtime of 03 is unexpected relative to the selected omitted-callback
escape outcome. The symbolic scheme alone does not settle concrete event
handling. The source adjudication below preserves both observations and leaves
their exact shared runtime cause open; no user expectation is rewritten.
An additional Oracle check replacing 03's
binding by `our answer: [] int = relay signal::ping` also exits 0.

Root annotation placement was checked narrowly in the frozen source:
`lowering/body/mod.rs:2345` passes the original `computation` to
`body/methods.rs:192::connect_binding_annotation`, which passes
`effect: computation.effect` to `AnnConstraintLowerer::connect_computation`.
Thus this is an initializer annotation, rather than a later exported Name
lookup. The separately assigned Oracle owner audit, relayed by the primary,
establishes a comparability limit: `annotation/constraints.rs:529–536` supplies
`stack(inner, push-empty) <: actual_initializer_effect`; it supplies no reverse
`actual_initializer_effect <: empty` check for an empty row without a tail.
The no-tail return is at `:641–643`, and the empty push at `:674–681`.
Native's root annotation does check its initializer effect against an upper
effect. Identical root-row spelling therefore does not encode equivalent
purity requirements in these two tools. The acceptance differences in 02/05/06
are observations, not established compatibility bugs. Do not infer a pure
initializer from an Oracle `[] int` check or its exported `answer: int` dump.

Case 06 directly observes a surviving write request. Since execution stops at
that unhandled request, it does not observe a subsequent signal handling or
prove the exact complete residual. Cases 07/08 discriminate outside-arm and
operation identity at runtime without needing an effect-set interpretation of
the printed answer type. Native's conservative Catch forwarding explains its
known subtraction gap; these observations are not soundness counterexamples.

## Exact source adaptation and execution

`tools/research_playground_hygiene_oracle.py::sources` contains the complete,
deterministic source constructors for both dialects, including the auxiliary
03 annotation probe. Oracle uses `pub act`/`pub` operation visibility, `our`
exported bindings and colon Catch arms. Native uses `act`/`our` operation
visibility, `my` definitions and brace/comma Catch arms. Names, operations,
annotations, applications, binding order and arm bodies are retained.

Each valid runtime input appends a terminal `answer` expression to force the
same designated initializer/value. This is an observation adapter: native's
carrier cannot admit the top-level terminal expression and is only asked to
infer the corresponding definition source. Export visibility is not itself
claimed semantically equivalent outside these self-contained modules. Oracle
`our` was chosen to retain the designated definitions in its printed module
roots; it does not itself force execution. All referenced definitions remain
in the same self-contained module, and callback/formal lexical roles are
preserved. No general proof that changing export visibility preserves every
inferred hygiene profile is supplied. In particular, source adaptations and
root-row spelling do not justify an unrestricted semantic-parity claim.

The smallest unexpected Oracle source in this packet is:

```yu
pub act signal:
    pub ping: () -> int

our relay cb = catch cb():
    signal::ping(), _ -> 1
    v -> v
our answer = relay signal::ping

answer
```

It returned `run roots [1]`. No global minimality claim is made.

Executable locations and hashes:

```text
O=/tmp/yulang-hygiene-audit-my68a_85/target/debug/yulang
f44bc8e41bc70290314e166832fa2a66183390ad742de458a60d7aabd39492fe
N=/home/momota1029/rust/yulang/target/debug/yu-playground
ff9bbd6f0fb48200dcf691602547ab4020d0013e2b007b2493a2cc9a06293bed
```

For each case prefix P, exact command templates are:

```text
O --no-prelude --no-cache check P.oracle.yu
O --no-prelude --no-cache dump P.oracle.yu --poly
O --no-prelude --no-cache run --evidence-vm --print-roots P.oracle-runtime.yu
N P.native.yu
```

The manifests below retain fully expanded command arrays, exit codes, elapsed
times, source hashes, stdout/stderr paths and their complete hashes. Each child
has a 15-second timeout; logs are bounded to 256 KiB per stream. The following
reproduces the valid observations with the frozen binaries (33 CLI processes):

```sh
python3 tools/research_playground_hygiene_oracle.py
python3 tools/research_playground_hygiene_oracle.py --cases 03-omitted-callback-pure-check --steps oracle-check --budget 1
```

Setup outcomes deliberately excluded from runtime comparison: one `O --help`
call exited 2 after printing usage; the first two run calls used the definition
source without the terminal expression, exited 0 and printed `run roots []`.
Those calls do not observe values. The first two forced-root followups are
logged as `oracle-run-forced`; they are the valid runtime rows for 01/02.
No unsuccessful attempt is silently replaced or omitted.

## Coverage, resources, and frozen evidence

Actual budget: 35 case-command processes plus one CLI help process = 36/36,
all sequential; no timeout, signal, or output-cap stop. No Cargo/build/test,
network, benchmark, recursive search, random seed, or additional runtime route.
The initial two-case manifest records its eight initial calls plus two forced
runtime followups. Peak RSS and CPU time are unknown. The source domain is
exactly eight families and one auxiliary annotation mutation; general aliases,
polymorphism, callbacks through stores, recursive functions, fresh-use scope
transport and principal-type equivalence remain unverified.

For 35 recorded case commands: summed wall time 0.9000s; maximum input 254 bytes; maximum stdout/stderr 2169/565 bytes.

Scratch roots R1/R2/R3 and manifest SHA-256 (logs remain there, not for commit):

```text
R1=/tmp/yulang-hygiene-oracle-comparison-uagajgqp
9d1c1caaeee76d2692b2273e34b42d79f1d9cddcd2e83a764b9505998818caf7  R1/manifest.json
R2=/tmp/yulang-hygiene-oracle-comparison-uck4uths
36c0cfc9ee42e0df79ba668c2cc93d01dc8012a4cc46f7e10af4f4874f971d5f  R2/manifest.json
R3=/tmp/yulang-hygiene-oracle-comparison-ekeqa6e1
957fe65bf5ac43a355a563d7036619eefd48b744c77b0afa73083e247f0ff06e  R3/manifest.json
```

Complete source hashes, including generated auxiliary runtime/native files not executed:

```text
8c22e3bacf74a0bfb4a94c2ac8e07da79bcbef8882d65220e7849984e91b04e6  R1/01-pure-value.native.yu
6462c2cc2efb318b583a6903a4a18dff50d2a996e74133ad700940960f3b9511  R1/01-pure-value.oracle-runtime.yu
aa85f5bc6998337f6c8b4d8f06b76ed568f5187fb52c7acfad1191f69b0434e4  R1/01-pure-value.oracle.yu
7b7baa2d04e5fa07b7a9199af07b5fb03a8a43a9aeac0f7c78a9bd537d948654  R1/02-direct-pure.native.yu
5d5778171e189447a51b795553e32f9138007d4829dda57f272d522b41bf284e  R1/02-direct-pure.oracle-runtime.yu
734effc300c78f399e259545343f173769d1e11f988caab5bf101ba93ec940e1  R1/02-direct-pure.oracle.yu
f8da42591836828cd2689415d6a02f2680f7debf2186b08ca71a7451976153b1  R2/03-omitted-callback.native.yu
c2cccc1f19aac91a26e60753c9611ec5e18f9a6c3f1a11d5bfc5671ef7129f7d  R2/03-omitted-callback.oracle-runtime.yu
873c531ebfab7ea9b4109d930a5f536a84342b80b7cd13753a573172a42cde52  R2/03-omitted-callback.oracle.yu
34bff34748e425a183ccf4303efac8c44c293b1d4367abab2ae7cb5d82dccea4  R2/04-annotated-callback-pure.native.yu
3e397c59360c4abeae43065547dd837433285b6c1105c40945c8c0aed29b91db  R2/04-annotated-callback-pure.oracle-runtime.yu
5c748a3bc518368b7dface16cbc3c084727168219b82dc2dafd9d52f0e2f79e7  R2/04-annotated-callback-pure.oracle.yu
52ea796247eee98a11a2a689b58180855d77d241ed6fc8d72ba97db999145363  R2/05-annotated-computation-pure.native.yu
c177267abbb6c8075d9f6d5ded6a4a318f50fb32d8dd72ba78169bdb065ea13b  R2/05-annotated-computation-pure.oracle-runtime.yu
62b67830c76a67e65147d2fe7606b10462e6568adff3daeef11a08b7a255218e  R2/05-annotated-computation-pure.oracle.yu
f5dc84651877e5b5ba43628d2bc14a160f4779894d641227b11da0aec9b6a69a  R2/06-write-residual.native.yu
02a985fd8437e18a3c8dfaf8ddfb627fa0bb272e2a5882dbe449d5e69c03510a  R2/06-write-residual.oracle-runtime.yu
15518b8ab7054b52318f5f4249e460b76c81e50eab1df1e95a33e3f74e22dc1f  R2/06-write-residual.oracle.yu
f2a70eec31c7a35c211035ed8675439ad0c7076fc0e1537c85617bcc2401c56c  R2/07-outside-arm.native.yu
44e68f2d281ce85d0a9ee7206491865de86b33fb44b6b67d4f37ff01be3637ec  R2/07-outside-arm.oracle-runtime.yu
6ebf40aa1771c5204d3b6a87ad79bec5140cece6b92ca9b084c6bc38ec962f8b  R2/07-outside-arm.oracle.yu
050001af163b22e3ba9085c37861f7fbca9a3177b5b4698f3f8d894576e8cb9b  R2/08-same-family-other-operation.native.yu
73afaae9a1ad4650699621ac6b7ee4ca007bc7950d0de6e69011e1d0a169e288  R2/08-same-family-other-operation.oracle-runtime.yu
3f4c847013809e236dbf4f32be78c47feba97e334cc95073b7b8f432c76d201a  R2/08-same-family-other-operation.oracle.yu
5187be99db9351fefcea9d8bb6a74265699de1e8d18e34ededfc651e2893ce67  R3/03-omitted-callback-pure-check.native.yu
86f3cb1e0d3cdb22224a693d04b048209403436524c7678e5e57cd631aa2519f  R3/03-omitted-callback-pure-check.oracle-runtime.yu
600f35f7f3947f1a95ffad3b7fa7f15cf03edb140beef9337572c72b8df37347  R3/03-omitted-callback-pure-check.oracle.yu
```

Complete log hashes; each row names stdout SHA-256 then stderr SHA-256:

```text
R1/01-pure-value.oracle-check e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R1/01-pure-value.oracle-poly c5bd7e34aa1bcb1c38af17ee91324c89552ed651da193c1441587b4cef33460d e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R1/01-pure-value.oracle-run e216479de05dde75c351d663f35ef60a684a2b1af2a4c8db9a95f4ad11152f5a e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R1/01-pure-value.native f1a85f82e85412474fa98142eb2af025d1fdc1cd337c16361934ffd518366550 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R1/02-direct-pure.oracle-check e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R1/02-direct-pure.oracle-poly 0e6068ed1065fdcdced015b9927c4e09d4cf7e0b71b03817821a836f1a27ccf3 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R1/02-direct-pure.oracle-run e216479de05dde75c351d663f35ef60a684a2b1af2a4c8db9a95f4ad11152f5a e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R1/02-direct-pure.native e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 887889ddae889866a7b1ec0d3efbf21ba013c38baa8d89d685aef10902381538
R1/01-pure-value.oracle-run-forced 32575683d5041429c7dcf659795ea793aeb73d13cd8a721a593ddafc324a070f e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R1/02-direct-pure.oracle-run-forced 32575683d5041429c7dcf659795ea793aeb73d13cd8a721a593ddafc324a070f e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R2/03-omitted-callback.oracle-check e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R2/03-omitted-callback.oracle-poly 889e8e391fedc4db67e02d0bab1ed69631116d0d20a47865514c5fb4871eebe4 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R2/03-omitted-callback.oracle-run 32575683d5041429c7dcf659795ea793aeb73d13cd8a721a593ddafc324a070f e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R2/03-omitted-callback.native dd8a4d2d2a853cde6d8a3995f58c8d2ae987198acc670cedabe2f3e829fa0b36 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R2/04-annotated-callback-pure.oracle-check e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R2/04-annotated-callback-pure.oracle-poly 94fa7976fab1b5ef63846db0638bee732ca56b150252ffaabb680a7171ab53db e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R2/04-annotated-callback-pure.oracle-run 32575683d5041429c7dcf659795ea793aeb73d13cd8a721a593ddafc324a070f e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R2/04-annotated-callback-pure.native e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 e6e3661c95151fe50f5ca4d3cf5d75fdf6aae25f2755420c308066c0bbbbbc7a
R2/05-annotated-computation-pure.oracle-check e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R2/05-annotated-computation-pure.oracle-poly 844a14a20215c1efa403d15f982ac517e7a8f8403621cfb92d97ecb5f0851733 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R2/05-annotated-computation-pure.oracle-run 32575683d5041429c7dcf659795ea793aeb73d13cd8a721a593ddafc324a070f e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R2/05-annotated-computation-pure.native e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 56457c7d4a78d784f257ded241e8926aab00e47b036a7aa4e5587625d541729b
R2/06-write-residual.oracle-check e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R2/06-write-residual.oracle-poly dd98f947f7820e9253fa4bb7b2cd2232e32ef1df527d81b67a593c576ed4c530 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R2/06-write-residual.oracle-run e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 baa2afdcb76b336815dc7b6263cfb4ccec797a0db73e15d9775fb9bdf811cbb3
R2/06-write-residual.native e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 d5fca181ffe3bba0ee89865713883434cb211418019733bd32f8091bfeec7539
R2/07-outside-arm.oracle-check e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R2/07-outside-arm.oracle-poly b19178d408bb1e52ccc7d37a9976a0b06144407f85c2f65eeecde54dd8783ee1 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R2/07-outside-arm.oracle-run e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 8c4e8235abf68e558187f49a90eacd139619389c82c9dae4bb42a3b800ab711d
R2/07-outside-arm.native 2aeea0d16010f90b9b8b931bc6a59807d43619baad7c4b18454fc7229773fca6 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R2/08-same-family-other-operation.oracle-check e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R2/08-same-family-other-operation.oracle-poly 96b3ed17423a8086d866ac82feb936e9897f600aa0febe5dcd0d70fc545298cb e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R2/08-same-family-other-operation.oracle-run e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 d0f6f9a6f5aabf095e7d89b5405e782467017248c4d226ab243d700a079a7881
R2/08-same-family-other-operation.native 2aeea0d16010f90b9b8b931bc6a59807d43619baad7c4b18454fc7229773fca6 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
R3/03-omitted-callback-pure-check.oracle-check e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
```

Recommended next action: establish the exact omitted-call source-to-runtime
boundary evidence before treating case 03 as reference-compatible hygiene. Retain 02/04/05
and 06–08 as concrete native integration discriminants with the limitations
above. The selected user semantics continue to govern.

## Primary source adjudication and interpreter control

The frozen run is not unchecked execution. Its `source/mod.rs:5434` and `:698`
route builds inferred poly output, checks runtime readiness, and specializes
with runtime/source provenance. `ensure_runtime_ready` at `:1973` rejects
lowering errors. The evidence VM selects handlers using operation identity and
request guard/boundary exposure (`evidence-vm/src/runtime.rs:22970`), rather than
the printed residual row. Boundary adapters originate in specialization
(`specialize/src/hygiene.rs:15–65`, `specialize2/runtime_shape.rs:875`). This
locates responsibility without proving which adapter branch this case takes.

The primary ran one additional control, outside the producer's 36-process
packet, on the identical case-03 terminal source:

```text
O --no-prelude --no-cache run --interpreter --print-roots R2/03-omitted-callback.oracle-runtime.yu
```

It exited 0 with `run roots [1]` and empty stderr. Source SHA-256:
`c2cccc1f19aac91a26e60753c9611ec5e18f9a6c3f1a11d5bfc5671ef7129f7d`;
stdout SHA-256:
`32575683d5041429c7dcf659795ea793aeb73d13cd8a721a593ddafc324a070f`.
The complete command/hash record is
`/tmp/yulang-hygiene-audit-my68a_85/omitted-interpreter.json`.
The independent spec review inspected this additional evidence.

The discrepancy therefore also occurs through the interpreter. Its shared
source-to-runtime cause remains unresolved. A scheme that admits `int` and
conservatively retains a possible effect is not contradicted merely by observing
`1`; no value-type unsoundness or historical hygiene defect is proved here.
Current user-selected noncapture remains the required successor behavior.
Total comparison/control CLI processes: 37, including the documented setup calls.

## Commit packet

Exact leased paths: `tools/research_playground_hygiene_oracle.py` and
`notes/progress/2026-10-15-playground-hygiene-oracle-comparison.md`.
Native baseline: `e9790f96f154ef0ddf67cb45aa26a569148569d7`; dispatch checkpoint:
`67b82c2ba68ac6e8fbf533575ea331223604b32d`; Oracle dependency:
`a58eefc31e22141574b6f20c6a5748151c6d79f1`. No dependency hashes changed during
these executions. Script/input/command/log integrity checks were run without
more producer CLI executions; all recorded hashes match their frozen files.
Fresh independent spec review found no blocking/major issue; its minor locator
repair and the separately reviewed interpreter evidence were integrated by the
primary. Producer writes were limited to the two leased paths. The primary
synchronized task/laboratory and verification records; no authority, theory
gate or question-board status was promoted.
Proposed message: `research: compare hygiene sources with the frozen Oracle`.
