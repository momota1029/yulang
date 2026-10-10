# HIR owner-copy return path: computation-port exposure blocker

Status: frozen, unreviewed research-only source characterization and conditional
graph derivation. No ordinary-source counterexample, global exclusion, defect,
restoration-gate closure, or production authority.
Baseline supplied by primary: `8282e7a756eeb4a1262847d5fb050e355440765f`.
Producer/lease: `hir_owner_scc_return_path`; this note only.

## Objective and governing premises

Resolve the missing source premise in the frozen positive-tail composition
proof: actual source actions must close the recorded owner pair `(C,S)` while
leaving the corresponding original-tail pair `(T',T)` outside one SCC. The
method is static inspection of annotation slots 42/47, scoped formal result
ports, Apply, Group, one-shot block computation links, positive Support
expansion, and their admission/diagnostic consumers. The constructive theorem
lane remains the primary's prover responsibility; this complementary lane
does not repeat its level or fiber derivations.

Authority is `notes/design/2026-10-10-contextual-attachment-admission-design.md`
§§3.1–5. Occurrence-local attachment identity, exact member ordinals, scoped
tails, level-selected orientation, actual parent/copy provenance, and transfer
of contextual obligations remain fixed. General concrete-negative formal
admission is still guarded; the two-cycle acceleration supplies no missing
source edge. The user's natural-inference and Simple-sub withdrawal decisions
are retained. No new meaning, proof-only relation, or source restriction is
selected. Research-lab, design-authority, git-concurrency, agent-orchestration,
and the yulang-proofs skill were read.

## Result and the precise missing producer

No concrete source prefix was established. The inspected **root-computation
annotation owner** does not expose its negative checking port `S`, or its
incidence-only positive copy `C`, as a source computation endpoint. Its scoped
variable entry identifies `T`; positive exported Function supports also expose
their tails rather than that root checking port. This leaves a precise missing
producer: a source-owned positive position or actual computation lower whose
canonical row is **the recorded copy C**, followed by admission to a later
checking interface that returns to **the recorded original S**.

Replacing C with its copied tail T' does not resolve the premise. Under the
explicit admitted-task hypotheses below, that nearest tail-based route closes
both recorded pairs. It cannot leave original T generic while lowering only S.
This is a discriminating constructor-local derivation, not an all-source
impossibility theorem.

The bounded exclusion covers S created solely by root evaluation checking,
C obtained solely through its incoming-Allowance copy, and no extra alias,
merge, other port occurrence of S, or independently generated positive
reference to C. It does not cover a negative checking port embedded in nested
Function structure, additional incidence paths, recursive interfaces that
expose that exact row, provider schedules, or intervening canonical merges.
The absence of those alternatives is a scope hypothesis, not a proved global
invariant. Stop condition reached: the owning constructor's missing positive
exposure is identified; no additional fixture or toy-model search was run.

## Source identities, ordering, and the inspected seams

Names here identify allocation sites, not invented numeric live row IDs. No
parsed HIR or concrete successful action schedule was produced.

| Identity/action | Exact owner and consequence |
| --- | --- |
| `K`, local scope | `candidate_source.rs:156–159` assigns annotated binding parameters `AnnotationScope::Local(K)`. `candidate_local_annotation` uses the same local identity (`candidate_effect.rs:994`). Other expression/definition scopes remain distinct. |
| `T = annotation_effects[(scope,name)]` | `candidate_effect.rs:844–864` allocates once at first occurrence and reuses that row. The map records neither S nor C. A singleton symbolic formal result returns this exact row pair (`:918–935`). |
| `E_o`, actual initializer computation | `Work::Install` reads `positions[initializer].effect`, emits initializer-to-block slot 20, then schedules LocalAnnotation at `boundary+1` (`candidate_source.rs:283–300`). |
| `S_o`, original root checking port | At slot 42, `candidate_annotation_computation_effect` constructs a new negative covariant port when the root effect row is not singleton-symbolic. With a written tail T its physical upper is `Allowance(v_o[T])`; it admits `E_o <: S_o` (`candidate_effect.rs:1172–1207,1304–1433`). |
| `A_o`, ascription occurrence | Ascription aliases the peeled child's component position; scope is selected from its retained HIR scope (`candidate_source.rs:195–207,403–424`). Slot 47 checks that child's computation. A newly constructed checking port is not equal to an earlier S merely because scope/name/spelling agree. |
| `I_a`, Apply invocation | Allocated at the canonical application computation's level. Slot 0 checks the callee against a Function demand; structural result comparison can admit `T <: I_a`. Slots 1/2 link callee evaluation/invocation to application computation (`shadow_apply.rs:1340–1462`). |
| `G_g`, Group facade | Group slot 1 compares the child's actual computation row to its separate facade (`shadow_apply.rs:1421–1439`); source generation retains that facade except when an enclosing ascription peels it. |
| `B_k`, block computation | Initializer slot 20 is a one-shot link to this row; block finish uses the final-expression Group relation (`candidate_source.rs:283–290,444–450`). Later local lookup evaluation is pure, rather than another initialization effect. |
| `C_t,T'_t`, positive copies | Positive incoming-tail extrusion allocates actual owner/tail copies and records `(C,S),(T',T)` (`candidate_extrusion.rs:88–179,293–305`). C is an algebra row in that operation's row map; no source action changes `positions[*].effect` or the scoped name map to C. |

For singleton-symbolic root evaluation annotations, the upper of slot 42/47 is
T directly: no fresh S or Allowance is created (`candidate_effect.rs:1184–1189`).
That branch cannot be cited as the constructor of the required original owner
pair. In the other branch the root computation port is created only by that
computation check, after the Value checking link and before exposure/install
(`:1014–1038,1102–1129`). Root evaluation is checked once and supplies no
positive Support to the computation or local scheme (`:1182–1183`).

Apply, Group, and slot 20 use component/invocation row identities selected by
their actual source positions. They have no argument selecting the incidental
owner copy C. The source planner does not turn scoped-name reuse into port
reuse. Positive Support expansion explicitly enqueues **its view tail** against
the current upper (`candidate_effect.rs:753–776`); a stored Support supplies
neither a reverse tail-to-owner edge nor a C-to-computation comparison by
itself. Consequently an actual chain from a formal T to I, Group, block, and
an annotation checking port can exist at these seams, but it is not the
requested chain from C, and its final checking port must still be proved the
recorded original S.

## Conditional derivation: a copied-tail return closes both pairs

Assume a successful session prefix, distinct canonical S,C,T,T', valid retained
views, no rollback or external interleaving, and the actual parent records
`(C,S)` and `(T',T)` from one positive extrusion at target t. Let
`level(S)=level(T)=d>t`, `level(C)=level(T')=t`. This equal-level source instance
is an explicit hypothesis; reused scoped tails can violate it. Assume the
physical original and copied negative keys have nonempty fibers and remain:

```text
S - C
S - Allowance(v[T])
T - T'
C - Allowance(v'[T'])
```

These yield actual adjacency `S->C`, `S->T`, `T->T'`, and `C->T'`, with the
Allowance nodes present between owner and tail. Creation provenance and
capture incidence add no graph adjacency (`candidate_intrusion.rs:382–493`).

Now assume the contemplated positive Support/call/computation continuation
actually admits `T' <: S`, and ordinary opposite replay actually admits
`T' <: Allowance(v[T])`. These are admitted-task premises, not inferred from
the existence of a stored Support or a schematic source chain.

1. Admission of `T' <: S` stores T' as a positive direct lower on S, because
   canonical S is younger than canonical T'. The physical edge is `S->T'`,
   **not** `T'->S` (`candidate_extrusion.rs:726–749`).
2. S's original negative Allowance replays against that lower. The admitted
   comparison `T' <: Allowance(v[T])` installs the exact negative Allowance
   on T', without structural Value extrusion. Hence `T'->Allowance(v[T])->T`.
3. `T->T'` already exists. Thus `(T',T)` belongs to one SCC.
4. `C->T'->T` alone has still not reached S. If the supposed computation
   return further supplies an actual graph path `T->...->S` (for example
   admitted equal-level symbolic-result/invocation/computation uppers), then
   `C->T'->T->...->S->C` closes the owner pair too.
5. On that **same graph**, the owner membership test is true and the tail
   membership test is true. Selective owner-only qualification has failed.
   The intrusion consumer tests recorded pairs independently, but both now
   qualify; merging T' into T lowers canonical T to t (`candidate_intrusion.rs:
   482–493,578–603`). No generic original tail above a boundary b>=t survives
   that merge for the proposed restoration route.

If step 4's return is absent, the owner test remains unestablished even though
the tail pair qualifies. In the initial four-edge constructor subgraph, with
no additional outgoing edges from the copied endpoints, neither recorded pair
is in one SCC. These are exact conditional graph membership statements;
neither is a concrete HIR witness. A selective return must leave this tail-based
route, or prevent the stated admitted Allowance replay while establishing a
different actual return. The missing positive exposure of C is therefore a
useful constructor-specific blocker, rather than another level calculation.

## Exact positive lower and later omission requirements

The required old positive C lower is not established by a permitted family,
a source-name spelling, or a row relation. In this owner path the physical
producer on S would be `candidate_apply_effect(actual_lower,S)`, with
`actual_lower` non-row or a canonically older row. The operation constructor
does create a real Support operand for its nominal family
(`candidate_effect.rs:1318–1324`); Apply and opposite replay can propagate it
to an actual checking receiver. The static audit did not produce a prefix
showing that this exact operation Support reached this exact S before the
specified tail extrusion.

Conditionally, if that key already exists when the extrusion visits S, its
positive bound is copied onto C before the IncomingAllowance action in the
first-visit schedule (`candidate_extrusion.rs:115–179,293–322`). For an
operation Support with no tail, the copied operand has the same retained
family/view endpoint; it supplies no path back to S. BottomEffect can likewise
be a real physical lower but its operand check returns immediately
(`candidate_effect.rs:752`). A nonempty opposite count alone therefore does
not establish a mutation capable of hiding an obligation. This audit supplies
no exact actual positive-C key with occurrence/cause in a successful source
prefix; positive transport remains conditional rather than a source witness.

No within-use missed fiber `omega` was found. The restore consumer saves an
opposite count, reads each current canonical bound, builds the literal
incoming-use Cartesian list, then drains each callback
(`candidate_extrusion.rs:599–641`, `candidate_context.rs:1938–1994`). All
captured bound restores precede the final lookup Value link
(`candidate_scheme.rs:998–1032,1127–1135`). Additional restores of the same
key and later positive restores must be included in any candidate omission.

All located rescue owners were inspected: ordinary Effect bound admission
replays opposites; a qualifying merge transfers both sides/fibers and replays
the merged owner's lowers; Value replay records the diagnostic child before
context suppression (`candidate_extrusion.rs:646–691,726–751`,
`candidate_intrusion.rs:549–603`). Effect reporting starts from initial and
current canonical pairs and traverses children for every retained relation;
Derived/FunctionPort and both Replay parents provide diagnostic edges, while
FreshUse transport alone does not (`candidate_effect.rs:524–580`,
`candidate_context.rs:1445–1477,1515–1521`). Effect-initiated work also reports
Value diagnostic deltas from mixed SCC work (`lib.rs:12083–12099`). No named
omission survives these consumers in this audit; universal rescue completeness
is also unproved. No solver defect follows.

## Checks, coverage, resources, and handoff

Commands: bounded `cat`, `sed -n`, `rg`, `rg --files`, `sha256sum`, and one
leased-note creation using apply_patch. Static coverage is the named
constructor/consumer seams above, not enumeration of source programs or SCCs.
Some initial combined captures truncated; subsequent narrow reads supplied
the source used in the derivation. No executable oracle exists: the argument
shares the actual inspected compiler rules and is not independent validation
of language semantics. Seeds/ranges, executable samples, mutations: none.

No tests, builds, probes, formatting, child delegation, model changes, compiler
edits, or shared-record edits ran. Zero heavyweight processes. Small shell read
batches only; CPU, peak RSS, and total wall time unmeasured. The supplied budget
is source/static only with a constructor-blocker stop condition, not a numeric
time allowance. Process deviation: the initial read command inadvertently
included read-only `git rev-parse HEAD`; it returned the supplied full baseline.
This violated the packet's no-Git instruction. No Git mutation or later Git
command ran; the deviation was disclosed to the primary.

Unverified: concrete parsing/HIR, actual live row numbers and origins, complete
recursive/provider schedules, other Function-owned S ports, all mixed SCCs,
rollback/retry, a within-restore mutation, and any failed diagnostic rescue.
This producer does not independently review its own output. Requested/observed
model and effort metadata are not asserted; no prover child execution is
claimed by this source-audit lane.

Recommended next action: have the primary test or delegate a narrowly scoped
source bridge for a **Function-owned** incoming S whose copied C is exposed
as an actual positive Function/computation position. Require that exact row's
producer and both SCC tests; a route exposing only T' repeats the tail-closing
premise above. Keep R open.

## Frozen dependencies and commit packet

The nine implementation/design hashes below describe the initial inspected
snapshot and match the frozen composition proof. Two frozen note hashes are
additional direct dependencies. A final recheck found concurrent movement only
in `candidate_context.rs`, from its listed hash to
`c7719e0e8dc8fa1040b89d096e14d0794e261385bed4bdf6b50bd81befc58866`.
The current dependency/children functions and incoming-replay implementation
were narrowly reread; the described edge rules and incoming-use Cartesian
enumeration remain present (current replay wrapper/implementation at
`:1937–2011`). Complete change scope and baseline-blob correspondence are left
to the primary. The core constructor/SCC derivation uses unchanged files. This
worker did not compare files to Git blobs or certify the moving dependency as
an independently reviewed snapshot. The movement was disclosed to the primary.

```text
8adc289142dd78a625184dd661fb162e49f24532a19c7c4f9e114e604c0966a0  crates/yu-solver/src/candidate_source.rs
2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e  crates/yu-solver/src/candidate_effect.rs
3fd1c7234c38013343e1c2e72bfed06c4eecdf7173e27d7581e11d6df84f0b3a  crates/yu-solver/src/candidate_extrusion.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
582bfb741315534dacf7290bb5618452bb55d9949a8aac691d8d01b93720de11  crates/yu-solver/src/candidate_scheme.rs
2897c168c02640443a2f1280286a648853afe08324294c53f1c95d373ac3a337  crates/yu-solver/src/candidate_context.rs
6bea8808153b8b71a57e4a8583284e49284ec9aa35118a61f44a3a387a8a32f6  crates/yu-solver/src/shadow_apply.rs
9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1  crates/yu-solver/src/lib.rs
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc  notes/design/2026-10-10-contextual-attachment-admission-design.md
6e8a41bc27e0570c916cf49fa4e4a916b6bb6059ad8b0c32627a2d33a0cfbf93  notes/progress/2026-10-10-positive-tail-source-composition-proof.md
efa0750d7cf82bb0fd18e5f1ec0e6003b054adf30f14176a2e6fe1600f169cbc  notes/progress/2026-10-10-ordinary-hir-successor-composition-search.md
```

Commit packet: exact leased/changed path
`notes/progress/2026-10-10-hir-owner-scc-return-path.md`; baseline
`8282e7a756eeb4a1262847d5fb050e355440765f`; changed dependency hashes:
`candidate_context.rs` changed from `2897c168c02640443a2f1280286a648853afe08324294c53f1c95d373ac3a337`
to `c7719e0e8dc8fa1040b89d096e14d0794e261385bed4bdf6b50bd81befc58866` during
inspection; other eight implementation/design hashes unchanged on final
recheck, note hashes pinned above. No dependency was changed by this worker;
baseline-blob/delta verification left to primary. Review status:
unreviewed, frozen research-only bounded characterization/conditional graph
derivation. Checks already run: static owning-source inspection and dependency
hashing only; no tests/builds/probes. Proposed one-line checkpoint message:
`research: isolate computation-port exposure blocker for selective intrusion`.
Shared-record deltas intentionally left for primary/curator: record the
root-computation-only exposure bound and copied-tail route's conditional
qualification of both pairs; retain R and actual positive-C/source-prefix,
within-use mutation, and complete replay/diagnostic rescue premises as open.
No task, index, authority, theory, manifest, lockfile, or question bundle changed.
