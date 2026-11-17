# Cycle246: guarded actual Presence definition blocks

## Timing and recovery failure

Started2026-11-17T19:30:08Z. Last ordinary build command recorded19:35:12Z;
the next clock check after a new parent task was20:27:04Z. Continuous work and
time management during that gap were not verified. The20:25 deadline was
missed, and the mandatory intermediate heartbeats were not published. This is
a schedule/heartbeat failure, not a successful45-minute research cycle. The
cause of the unobserved interval is not established. At20:27 the workspace and
process table showed no active Lean writer. Further new work was stopped;
only verification/publication recovery proceeded. No next cycle started in
parallel. Usage allowance is unknown.

## Repository state and constraints

Read latest integration939fe87ba at start, full standing orders and inboxI47.
Prior245 was completed, fully published and clean; no outstanding writer.
Beginning heartbeat: ada028824144fca1913c1d4270813cb33e6ca992. At recovery, remote
work still pointed to that heartbeat. Integration had advanced to245's already
integrated a1c54ee3887603466d82b10515d887c78dbb017d; no new semantic instructions
were introduced. I47 remains the target. No frozen Audit.lean/README.md edits,
no existing source edits, no source acceptance restriction or new semantics.

## Verified additions

1. GeneralFiniteAssignment246: executable first-match finite assignment writes.
   For every finite injective target map, every value vector and fallback,
   finite_at returns the designated value at each target; finite_outside
   preserves every name outside the image. Zero nodes and repeated values are
   allowed. write_member uses an explicitly stated coherence premise.

2. GeneralPresenceGuardedLayer246: finite guarded layer syntax compiled to
   actual Presence TyTerm, with a separate lowering to CommonNominalSyntax.Layer.
   Supports base/bottom/top, lattice constructors, pair, width/exact empty,
   required/record/default, variant and arrow. References occur under payload
   constructors; row expressions are actual RowTerm expressions. eval_bridge
   gives literal semantic equality for every assignment. lower_rows depends
   only on row values. Exact typed/row source equations expose the finite
   reference support, rather than assuming a desired support bound.

3. GeneralPresenceGuardedBlock246: for every finite guarded body, injective
   target-name map, parameter-name map disjoint from targets, and arbitrary
   original Comp assignment, construct an assignment satisfying all compiled
   actual two-inequality Presence definitions. Every non-target Comp coordinate
   is literally preserved, and every row coordinate, including target rows,
   stays unchanged. Parameter names may repeat; row expressions may read target
   names. The proof constructs regular Common values through the existing
   all_parameter_sound theorem and the proved layer evaluation bridge. It does
   not assume External, source ranks, or the desired block's satisfiability.
   Key results: equation_satisfied, block_satisfied, arbitrary_public_model.

4. GeneralPresenceConsumerSupport246: literal value equality from equality on
   typedReads and global row equality, then Atom.Holds and All equivalence.
   Row-only reads do not count as type dependencies. all_outside_iff gives an
   exact semantic preservation lemma for consumers outside a finite private
   typed-read set. No semantic Model law is required for these equalities.

## Verification and publication

At recovery all four final source files were rebuilt with Lean4.35.0,
--trust=0 -DwarningAsError=true. Every module exit0. New exhaustive module audit:

    CYCLE246-PASS: 250 constants in4 modules

Allowed transitive axiom dependencies are only propext, Classical.choice and
Quot.sound. Verified source hashes and full output are under
notes/verification/cycle246. No whole journal build or frozen global gate was
run. No additional dependency closure was needed beyond245's focused cache.
Final publication head/tree comparison is recorded in the completion receipt.

## Precisely unfinished

The general all-models recovery theorem, the guarded-block/consumer extension
composition, and the proposed two-node default/arrow regression were planned
but not implemented. Existing actual OriginView/journal integration still needs
its large dependency closure and witness-equivalence bridge. This fragment
does not encode arbitrary unguarded aliases or all source equations. The finite
layer grammar is a representation fragment, not a language rejection test.

No claim is made about fresh-block production by actual source operations,
full current/history/cache updates, plan generation termination, solver Acc,
12 boundary laws, or EvidenceNode completion. No new language counterexample
was found. Next independent work: models_equations iff and all_models_recovered
for this compiler; consumer exact preservation composition; finite-allocation
and mutually recursive whole-record-default/arrow regression.
