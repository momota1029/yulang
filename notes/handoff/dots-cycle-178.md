# Cycle 178: nominal pair same-model residual (in progress)

Started 2026-11-14 01:25:44 UTC. Latest fetched integration:
`d636750ce44de9271ebf328a5ab27ad4955cb845`. Fresh standing-orders and inbox I30
read; previous cycle177 completed with report; no previous writer observed.
55-minute user cap overrides longer text. No STOP observed.

## First source checkpoint

Six modules cover arbitrary finite linear type binders at two different
same-name nominal slots. Parameter intervals need not be point-valued.
The actual BranchModels is equivalent to source Models, endpoint subtyping and
the actual fresh capture merge equations. A finite form says each fresh lower
is equivalent to the union of the two lowers, and each fresh upper to the
intersection of the two uppers. Zero arity and source identity distinctions
are retained.

Current centered Candidate plus Models supplies endpoint subtyping. The
candidate's supplied-model Holds is exactly the merge/extrema residual;
conditional leaf and EvidenceNode-shaped producers consume that residual.
No historical journal membership or packet installation assumption is used.

The finite regression strengthens the old warning into a concrete centered
Models + Candidate example: the wrong value of a fresh lower gives no Evidence;
correcting that value gives Evidence. The two assignments agree on old source
identities. This has a nonpoint root and does NOT assert G reachability or
Stable. Therefore it is NOT a counterexample to G.EvidenceNode.

## Verification and limits

Focused Lean 4.35.0 trust-zero builds passed. The small audit scans all 146
new declarations (including private/generated declarations) and admits only
the standard propext/Classical.choice/Quot.sound set. Raw logs accompany this
checkpoint. Minor elaboration issues in newly written proofs were corrected;
none remain. No local full build or runtime oracle was executed.

The exact unrestricted G.EvidenceNode field is still OPEN. This fragment has
one nominal head, type-only linear binders, no requirements and no named
outputs. Nested patterns, repeated binders across positions, rows, compound
outputs and the general stable-selection model-extension/guard bridge remain
outside this new result. Runtime X13/X15 observations are not promoted to an
internal-state completeness theorem. Usage remaining: unknown.

At 01:40 UTC a fresh fetch found integration `60373c8c4194ec97a95f13c6f2ad335d7eb12b95`.
Its 28 added files and two append-only indexes were incorporated without dropping
any earlier work/dots-main file. This includes Astra's counterexample to the
nonterminal installation preservation contract, not to termination or G.
Focused validation of those upstream additions is running separately.

## Second checkpoint: corrected CI and stable comparison

The initial CI on 56a8a338 passed core but failed the Lean job because its build
policy treats an unused-simp warning as failure. The redundant simp argument
was removed without changing the theorem statement. Focused compilation now
uses `-DwarningAsError=true` as well as `--trust=0`. This was a verification
failure, not a newly introduced false theorem. Full CI will be rechecked on
the corrected source commit.

Thirteen source modules are now locally validated; the expanded small audit
passes all 285 declarations. Descriptor/parameter witnesses are recovered from
actual Finished inspection. Additional unconditional producers cover point
outer nominal arguments with arbitrary finite linear type binders, and
nullary nominal heads at either point or nonpoint endpoints.

A third assignment sets the explicit actual binder center to int and proves
full centered Plan.Holds. It must not be confused with the earlier corrected
raw-branch assignment. Source value support, raw Joint, raw Installable and
full centered Installable are constructed for the finite fixture. Consequently
`stable_not_selected` proves its bad-fixed-model state cannot simultaneously
be Stable and selected. The apparent gap is therefore not a stable-selection
counterexample.

The source-support construction is generalized to arbitrary finite nominal-pair
shapes in an initial singleton registry. The initial adapter derives raw Joint
and raw Installable from Candidate+selected, then full Installable from the
explicit common-centered-model existence premise. General production of that
common model remains OPEN. This nonpoint initial shape does not directly meet
G's point-root Initial predicate; support preservation to arbitrary reachable
states also remains open.

Independent review found no model substitution or G completion overclaim and
recompiled the point/nonpoint contrast separately. The two roots/states in
that contrast are different, despite equal nominal endpoint values.
