# R83 frozen classifier obstruction

Assignment: `R83-CLASSIFIER-PROOF`, revision 1, 2026-10-19. Sole author:
`/root/r83_classifier_proof`; no descendants or coauthors. Status: **candidate
mathematical counterexample to the draft classification specification; STOP**.
No reviewed theorem, source-qualified compiler counterexample, semantic adoption,
implementation or production authority follows.

## Parent application and precise obstruction

Original Simple-sub/evaluator and A/B gates remain **OPEN 0→0**, with their
original accepted source domain and quantifiers, including independent F1/FK1
and foreign-continuation cases. R50 remains NOT_ADOPTED. This result blocks the
requested R83 classifier theorem and the adoption offer: the frozen algorithm
and its stated universal outcome disagree on one product-domain input.

The frozen definition §2 explicitly makes `ImplEligible` a declaration/binder
**form** check; endpoint evidence is supplied separately by ordinary checking.
Take eligible signature `int -> int -> int` and implementation declaration:

```yu
my second self (selected:int) (extra:bool) = 0
```

The implementation has an unannotated receiver, at least one explicit binder,
and ordinary value annotations. It has no parameter pattern, polymorphism,
higher-order slot, adapter or unsupported effect annotation. Therefore it passes
the literal independent form predicate. The `bool` annotation supplies an
out-of-envelope endpoint. Its explicit count is two against the signature's
one. Definition §3's ordered algorithm returns **Incompatible** at the count
branch before inspecting `OutsideOrUnknown`. Definition §3's following prose
says ordinary endpoint evidence outside the supported set makes the pair
**Unsupported**; the adoption table likewise gives outside/unavailable endpoint
evidence as an Unsupported condition. The assignment requests that universal
outcome as well. These cannot all hold for this input.

This is a mixed-failure case omitted by the finite case table. It does not
claim that the ordered algorithm itself returns two values: an ordered
algorithm is single-valued. It establishes disagreement between that algorithm
and the universal outcome asserted for it. The signature and implementation
eligibility predicates need not inspect matching arity to exhibit this failure.
Reading `ImplEligible` as also rejecting the bool endpoint would contradict its
explicit form-only statement and move a pair-evidence condition into that
predicate. Choosing either interpretation is a design decision reserved to
Luna, not a proof repair authorized to this author.

No actual parser, inference or runtime execution of this declaration is
claimed. This is an input to the frozen proposed classifier, whose evidence
component explicitly permits `OutsideOrUnknown`. It needs no new source
constructor assertion or endpoint solver.

Luna's STOP arrived before further construction. No classifier theorem,
finite-preservation theorem or R81 specialization is submitted on these
inconsistent bytes. The useful parent application is elimination of an invalid
proof/adoption premise, with the exact missing case now identified. A new
version must decide the priority of out-of-envelope evidence and supported
count/role mismatches; the old bytes remain frozen.

## Source/native boundary and prior work

R81 by `/root/r81_prefix_proof` remains reusable only under its original P1–P4
and source-role P5 hypotheses. Its exact first unanswered outcome remains
`UnhandledRequest(first observe occurrence, resolved io::observe, payload=1,
event=q, continuation=saved suffix)`, trace `[observe(1)]`. The suffix retains
the pending ValueEntry for `self` and outer Callee for `observe(2)` among the
ordinary frames crossed. No `observe(2)` or final `2` follows without a response.
Its pure `SecondInt::second 1 2` result is conditional on actual source selection,
member/body/environment retention, ordinary Apply graph and complete admission;
Compatible supplies none of those P1–P4 premises or body typing.

Pinned charter §21 fixes entry from the executable binder's own outer annotation.
Bounded inspection of `program.rs:414–433,488–509` confirms ordinary Name
consumption and Lambda role use that predicate. This establishes an ordinary
consumer fact only, not role-member producer output. The actual P1–P4 seam is
`shadow.rs::pending_role_impl_sources` → `module/local_source.rs` selected
member identity/root/environment and Apply → `candidate_source.rs` /
`shadow_apply.rs` admission → `RuntimeProgram::from_hir` → machine Apply.
Role-member construction on that path remains unestablished.

The inherited six-frontier map is status evidence from frozen R81, not six new
proofs: ordered matching (`machine.rs:1550–1637`) retains general selection OPEN;
§21 entry (`program.rs`, machine ValueEntry/Callee) retains P1–P4 OPEN;
wrong/sibling permission (`receiving.rs::Receiving::local_grant`) retains native
sibling/residual preservation OPEN; shallow unmatched outward request
(`machine.rs:1635–1775`) retains general contribution correspondence OPEN; one
continuation fixture/capture path retains complete template transport and
independent F1/FK1 OPEN; static-to-runtime Operation/FormalEntry generation
retains definitions/native consumers of `candidate_operation` and
`candidate_formal_entry_annotation` OPEN. These owners are inherited locators,
not additional source inspections. No provider/residual/witness/control lineage
is equated. No Simple-sub generation, accumulation, propagation, levels,
extrusion, qualifying intrusion or generalization changes.

R82 closeout by Luna is reused for the stop-on-definition-ambiguity rule and
independent-eligibility motivation; it does not resolve mixed-failure priority.
The broader R81 draft domain (bool/str, closed rows, Computation receiver/result)
is not imported into the R83 pilot. Historical completed no-handler traces are
not revived. More assumed-transition experiments would not decide this textual
priority conflict or establish P1–P4.

## Frozen inputs, checks and STOP

All six supplied direct hashes matched, and all 103 R80 manifest file pins
matched read-only SHA-256 calculation:

| Input | SHA-256 |
| --- | --- |
| R83 contract revision 1 | `68fdfda6599d3b894482d4ef447e2940802c64ef97573a602b63abf003ff648b` |
| R83 compatibility definition, Luna | `bdf814ad1cab0bd07976b9e14079c534fe811547515a015aa8ff65d637f62af3` |
| R83 adoption draft, Luna | `7ec59de6d1961b1bcc045f0c18d0015c388eb55bc5ae9ac053a73c0c8c722607` |
| R81 conditional proof, /root/r81_prefix_proof | `d3b3d52e19332506c6fab8eea7878a5ff1c81f90cf96dff548b30ab5f88c767f` |
| R82 closeout, Luna | `a296ae59e8db86f3f3a2ea19071a0afbb6140e28f4a64a9b0d32c4b1843c347c` |
| R80 manifest, Luna | `a54331b710300baeb0b88a2032dccc0cf73a7cca838242643255e44108179803` |

Baseline `af3ccf2d63ba7f87e0359e183568db548ea53307` is supplied, not Git-observed.
Requested model/effort: Sol/high; observed model/effort UNKNOWN/UNKNOWN.
Grant: 150 seconds charged in full, no renewal/carryover. Active elapsed is
UNKNOWN; explicit clock receipt `2026-10-19 02:11:08 UTC`. Initial `python` was
unavailable; successful hash calculation used `python3`. No tests/builds/probes,
compiler CLI, Git, external contact, delegation, source edits or scratch output.

Mutual TODO `R83-MIXED-PRIORITY-1`: Luna decides mixed-failure priority in a
separately versioned frozen definition/contract, aligns adoption outcomes, then
issues any renewed proof lease. Required evidence: exact same input above has
one agreed result across algorithm, prose, theorem and adoption. Falsifier:
an earlier mismatch still masks an endpoint condition claimed universally
Unsupported, or endpoint eligibility silently changes domains. Future P1–P4
implementation evidence remains a separate adoption-backed TODO with its source
owners above. No implementation permission is requested by this result.

Exactly two new paths: this artifact and
`tasks/agent-loop/inbox/20261019-r83-proof.md`. No other new/scratch paths.
**STOP receipt:** Luna explicitly requested STOP; no descendants exist. Freeze
this artifact and the one handoff; all writes cease after their final hash
receipt. No worker continues while awaiting intake or review. No independent
certification was attempted; Luna owns fresh review and subsequent assignment.
