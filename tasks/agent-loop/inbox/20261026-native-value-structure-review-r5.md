# Native Value structure r5 — independent compiler referee

Date: 2026-10-26. Reviewer: `/root/value_review_r5`.
Assignment revision: 1. Outcome: **ACCEPT for the bounded construction**.
No blocking, major or minor correctness finding. No repair requested.

## Isolation, authority and frozen target

Fresh review-only worker; no contribution to the construction, no descendants,
no Git operations and no source, note, handoff, import, index, status or
configuration mutation. The only repository write is this assigned receipt.
The task packet fixes the review scope and finite 1,000-second budget, with at
most two risk-driven focused checks and no redundant clean build. Applicable
root/pre-sprint, design-authority, testing, orchestration and sprint policies,
the Lean proof skill and its source/execution references were consulted.

The original parent remains `MERGE-EXPANSION-COVER-1`, ultimately the unchanged
`SourceProblem.InferenceSoundness`; the full original source scope and shared
scoped witness remain required. The top-level inference principles and original
whole-proof target do not authorize semantic simplification or parent closure.

| Reviewed frozen input | Verified SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/NativeValueStructure.lean` | `81060e17ad37f2e4a47edb7ed2829bea6820438bf3d4db0e4de8d113fd9497fc` |
| `notes/theory/2026-10-26-native-value-structure-r5.md` | `ab9d3d278f6635285bb5888671d3f7ade9dfa50c56b39c30b49f74f203e35bc7` |
| `tasks/agent-loop/inbox/20261026-native-value-structure-r5.md` | `b8923615aeac7b435ef9ed9f721ac75ce49fa861fecd807c3d0a04d9e91e33c1` |
| Published dependency `NativeValuePorts.lean` at `82b8fb6` | `f49bf12537633c65b4dbdcb4e739df5de5eee76cfb5ad845c8dba50cef4101fa` |

The live and isolated-project source bytes match throughout the eight project
modules in the actual import cone. The original-baseline Rust `lib.rs`,
`candidate_extrusion.rs` and `candidate_context.rs` match the pinned input
manifest. No moving dependency was substituted.

## Source and theorem review

| Responsibility | Exact reviewed evidence and conclusion |
| --- | --- |
| Full payload | `NativeValueStructure.lean:16–34,363–378,430–460,645–655`: `Request.key` keeps both complete Value endpoints, stored Context, optional source set, transformer and all five deferred demand fields. Context forwarding is the original request equality, not reconstruction from endpoints. The composition concludes admissions against that same original full key. |
| Outer routing | `NativeValueStructure.lean:292–361` against `crates/yu-solver/src/lib.rs:14458–14494`: actual precedence is current memo, candidate canonical rewrite, retained extrusion rewrite, then operand dispatch. All four iff roots retain their actual Bool/readback conditions; no assumed global coverage predicate supplies the conclusion. |
| Shape and shortcuts | `NativeValueStructure.lean:36–84,259–290,463–474,526–533` against `lib.rs:14494–14526,16494–16520`: exact polarity-specific shape mapping; Tuple arity is part of shape; positive Bottom and negative Top bypass incompatibility. Advertised unequal Tuple arities therefore produce the earlier shape diagnostic, while inner malformed length/tag/read failures remain IdentityExhausted. |
| Structural failures | `NativeValueStructure.lean:259–290,486–524` against `lib.rs:14528–14704`: Variant/Record term lookup or tag failure is ReceiptMismatch; Tuple read/tag/length failure is IdentityExhausted. Required absence, optional absence and optional-to-required Record unavailability preserve the existing first-name rule. A failing scan does not publish a partial child vector. Allocation failures are outside the explicitly labeled allocation-success projection, not silently proved impossible. |
| Function polarity | `NativeValueStructure.lean:231–255,476–484` and frozen `NativeValuePorts.functionChildren` against `lib.rs:14706–14709,14800–14828,16452–16490`: raw Function tags preserve positive/negative extraction. Missing or wrong Function views become invariant violations, matching native expect/unreachable rather than successful fallback. Argument and argument effect reverse direction; result effect and result retain direction, in native four-child order. |
| Extrusion and current bound | `NativeValueStructure.lean:121–221` against `lib.rs:14710–14798,16193–16203` and `candidate_extrusion.rs:1115–1144`: positive/negative requested endpoint, receiver and level are computed; changed candidate copies rewrite before application; legacy application retains the original pair. Candidate application canonicalizes after extrusion, then selects the correct reflexive, row/row level or rigid/row branch. `fallback_selected_pair` establishes equality to that post-operation observed directed pair, rather than to a stale pre-copy bound. Actual copying, aging, insertion and replay are not assumed proved. |
| Variant domain and duplicates | `NativeValueStructure.lean:535–573` and frozen `NativeValuePorts.lean:667–715` against `lib.rs:14533–14569`: the nonvacuous domain iff requires a matching tag/arity even for zero-payload positive alternatives. Every matching duplicate negative entry contributes every indexed payload. Original positive, negative and payload indexes survive. |
| Diagnostics | `NativeValueStructure.lean:575–643` against `lib.rs:14501–14508,14563–14572,14625–14634,14683–14685,14830–14843`: direct witnesses retain original terminal pair, kind, distance zero and absent first field/index. Record/Variant diagnostic edges do not fabricate Tuple indexes. Function Value edges retain Argument/Result metadata and Effect children create no Value diagnostic edge. Lists describe native edge calls before interning, not final graph multiplicity. Publication remains pending. |
| Structured execution | `NativeValueStructure.lean:380–460`, exact frozen `drive_success_readback`, and `lib.rs:14955–15054`: this is specifically the candidate typed-drain port adapter, with actual computed structured children, admitted-before-enqueue pending state, final original-order jobs/queue and no Replay acknowledgements. Other routes and legacy mode remain distinct represented owners. Its `none` is not a source-language rejection or removal of those cases. |

The principal theorem is
`YulangClosure.NativeValueStructure.context_value_children_readback`. Its
single operational premise is successful computation of the explicit
`executeAfterContext` over the supplied raw inputs. Its result is identity
transformer, candidate mode, the actual structured branch, exact children and
queue, no pending item, and same-output-arena complete admission receipts.
This is a real computed constructor/readback component. It supplies neither
semantic completion of those jobs nor authenticity of the supplied native
observations. Finite fuel indexes this proof-side execution prefix and is not
claimed as a source/native restriction or termination proof.

## Verification and preserved collection failure

No fresh Lean build or compiler test was run: the inspected final checker
receipts already exercise the unchanged source and exact dependency cone, and
the concrete remaining review risk was census collection integrity. One
focused read-only reconciliation check ran successfully (exit 0), writing only
`/workspace/scratch/c10e953a5453/value-review-r5/evidence-integrity.json`.
Its SHA-256 is
`e18fa0bd26e10391d0392c41853cbaa0fea1458f18b60759a8965df641808113`.

The check independently verified every one of 25 chunk lengths/hashes,
reconstructed `check11.log` byte-for-byte, required exact EOF trailer and
balanced unique named blocks, checked printed types and complete axiom reports,
and matched all 33 authored theorem names parsed from the reviewed source.
It also reconciled current/isolated project source hashes and pinned Rust
owners. Results:

| Evidence | Verified result |
| --- | --- |
| `check09.log` | SHA-256 `9b27381659b90b62cf14ae38e7eb841d13889f8356314af022c1c7402a7a2904`; 33 authored roots, complete begin/end reports; actual Lake and Lean 4.35.0; exact module build succeeds (9 Lake jobs); audit exit 0. |
| `check11.log` | 806,291 bytes; SHA-256 `6af2668f45fe5757245fc4c736c24d30baeebd48e2e1db13f6292f3edca77a37`; all 1,007 originating declarations and 514 theorem constants, including generated/private declarations; exit 0. |
| All declaration axioms | 824 none; 170 only `propext`; 13 `propext` plus `Quot.sound`. |
| Theorem axioms | 395 none; 108 only `propext`; 11 `propext` plus `Quot.sound`. |
| Authored-root axioms | 1 none; 21 only `propext`; 11 `propext` plus `Quot.sound`. |
| Holes/bypasses | No `Classical.choice`, project/custom axiom, `sorryAx`, native-evaluation assumption or kernel bypass in the audited surface/dependency results; reviewed source search has no proof hole/bypass match. No omitted-type marker or replacement character in the complete census. |

The originating-module audit actually selects the imported module index,
rejects originating axioms, verifies each authored root is a theorem constant,
and checks transitive collected axioms. The retained `check10` log remains a
failed output collection despite its Lean exit zero; this review relies on the
complete hashed `check11` reconstruction and does not erase that failure.
No optional default-target/whole-project build, binary verification or source
semantic theorem is inferred from these checks.

## Parent application and exact OPEN residuals

The accepted contribution is executable decoded outer Value selection and its
composition with the previously accepted full Context/structured-port
construction. It can supply an installed Value graph body's exact child data;
it does not establish that the body is current, returned, committed or valid.

The first native bridge remains authentication of the raw memo-current,
retained, canonical, processing, term/endpoint, source-set, post-check Context,
scope-interner and arena observations in one actual execution. In particular
`Routing.current` is a supplied readback, while `lib.rs:13507–13518`
`pair_is_current` requires actual memo membership and, in candidate mode, the
current processing relation's completion at the current generation. No theorem
in this module turns that readback into the missing completion certificate.
Canonical and retained rewrite results still need their actual diagnostic,
Transport/Derived and inherited-processing paths, not a fabricated rewritten
Context key.

Actual structural/legacy extrusion, bound insertion/replay/merge and generation
changes, versioned committed history, allocation/inventory/scoped-enabled/
overflow/failure refinement, diagnostic completion/acceptance, malformed
Function store formation and the shared Context/drain acknowledgement bridge
remain separate owner obligations. Original full Function/Call, method,
annotation, record adaptation and same-scoped-source semantics remain required.
The primary/native source and proof owners retain those OPEN gates;
`MERGE-EXPANSION-COVER-1`, full inference soundness/principality/termination and
production promotion are not closed by this ACCEPT.

## Cessation

Review complete within the assigned budget; zero Lean invocations, one focused
evidence-integrity check, no remaining process, no descendants or unresolved
descendant leases. This receipt is the final repository write. All writes are
stopped and the reviewed artifacts remain frozen. Integration and Git belong
to the primary.
