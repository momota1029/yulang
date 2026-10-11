# Oracle direct return: projection input and compact consumer audit

Date: 2026-10-12
Status: frozen producer source audit; independent review pending; original H OPEN
Claim class: bounded source correspondence and conditional collection derivation
Y3 baseline: `016cca26609ccd17364c31ba2b5a9e91f80dd87f`
Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle read root: `/tmp/yulang2-oracle-read`
Exclusive lease: this note only; leaf, no delegation or Git mutation

## Objective, authority and hypotheses

Audit the actual scheme input for `my direct(cb: (() -> [tick] ())) = cb`.
Let c be the formal Value coordinate, A the annotation-positive Function,
e its result-Effect coordinate, and α the concrete annotation's fresh stack ID.
These denote the actual constructors, not displayed identifiers. The primary
supplied the reviewed facts that A <: c is emitted, A contains PUSH α at its
result Effect, Name(cb) returns c before wrapping, and the enclosing parameter
output predicate is empty. This audit checks the next source seam.

Governing sources are annotation-effect-hygiene-integration §§1–2, top-level
inference principles §§1–5, original
[H](../theory/2026-10-11-oracle-global-effect-hygiene-proof.md) §1 and its
projection context §§2–5. H retains its original universal successfully lowered
source domain, actual occurrence/scope/binder/use/output routes, independent
same-family contribution survival and connected symbolic tails. This note does
not prove or refute H, complete Call, soundness or principality. No selected
language meaning, admission rule or compiler implementation changes.

Operational hypotheses for the local derivation: pinned source bytes, normal
completed calls at the cited owners, fresh allocation without exhaustion, and
no terminal proof failure before the claimed operation. Successful lowering
alone does not establish queue completion, publication or these hypotheses.
The actual final replay ledger, compact root and selector are not assumed.

## Original c lower and returned Y lower are different inputs

Oracle citations below are under `crates/infer/src/`.

1. `annotation/constraints.rs:124–137` emits A <: NegVar(c) with the lowerer's
   genuine source origin. `constraints/machine/entry.rs:1357–1410` retains that
   origin on a new canonical constraint or adds it to an existing one.
2. On completed propagation, `machine/propagate.rs:150–160` calls
   `add_lower_bound(c,A,...,Constraint(p))`. `machine/bounds.rs:630–711` inserts
   or reuses its exact bound. The alias-cycle shortcut requires PosVar and
   cannot subsume A's Function. `extrude_pos:4523–4532,4555–4564` returns A's
   same PosId while traversing its ports. This derives an admitted native
   annotation lower r_c conditional on completion; emission alone is weaker.
3. `constraints/mod.rs:2664–2672` and
   `structural_kernel/access/legacy_read_view.rs:214–222` enumerate ordinary
   and evidence lower records on the *queried coordinate*. They do not search
   neighboring coordinates for an equivalent Function.
4. For r_c, first admission with no qualified parents and no existing ledger
   returns at `machine/bounds.rs:2493–2495`; the projection owner then returns
   Unclaimed if both supports and exact formula are absent
   (`constraints/proof/mod.rs:10014–10031`). If a later ledger bootstrap reads
   its retained source derivation, `bounds.rs:2600–2634,2692–2706` classifies
   the source carrier as independent provided no linked upper claim has p as
   its producer. A <: c goes through the Function-to-Var branch rather than
   producing an upper bound. The standalone Independent clause installation
   is at 2539–2568; its evaluation is IncludedExact at
   `proof/mod.rs:11735–11741,11906–11915`. These are distinct source branches;
   they are not an executed final r_c ledger census.

Neither branch establishes that direct's positive return collection queries c.
The named source has header arguments. `lowering/body/mod.rs:2290–2318`
selects `lower_binding_body_with_args_to_named_self`; `expr/mod.rs:309–334`
passes Some(internal_self_value). `expr/lambda.rs:745–767` therefore allocates
the named skeleton. At 797–808 it emits c <: Y, where Y is the skeleton's
body_value, and **replaces** the body Value coordinate with Y. The subsequent
Function wrapper uses that replaced body at 958–968. Name(cb)=c is consequently
an intermediate source fact, not identity of the exported Function result.

The Var/Var comparison c <: Y creates a PosVar(c) alias lower on Y and an upper
NegVar(Y) on c (`machine/propagate.rs:103–128`). Actual lower/upper replay can
also produce A <: Y, as derived in the previous
[native transport note](../theory/2026-10-11-oracle-direct-static-liveness-followup.md)
§3. Denote this separate replayed Function lower r_Y. It is not r_c and its
carrier need not be the standalone annotation source carrier.

## Exact first missing consumer predicate

`analysis/session/generalize.rs:580–603` collects the definition root in scheme
mode. For every positive coordinate actually visited,
`compact/collect/mod.rs:848–878` consumes only the list returned by
`scheme_projectable_lowers_in_scope`. The query at
`structural_kernel/access.rs:862–895` skips exactly Excluded; it retains
Unclaimed and Included. A ProofFailure aborts this query instead of selecting
another lower. Thus the required first predicate is:

> At direct's actual collection snapshot, Y has a live replayed lower with
> endpoint A (or an established equivalent α-bearing positive Function), and
> project_lower(r_Y) returns Unclaimed or Included rather than Excluded/error.

A mere alias lower PosVar(c) does not satisfy this predicate.
`compact_pos_bound_id` (`compact/collect/mod.rs:1099–1128`) turns PosVar(c) into
a **secondary CompactVar**, without recursively collecting c's bounds.
`generalize/mod.rs:662–695` may query c during positive alias expansion, but it
accepts only PosVar endpoints and alias-neutral weights; its A Function lower
fails the PosVar check at 683–685. The expansion at 385–399 adds secondary
variables, not A's compact Function. A positive query of c occurring somewhere
in that pass therefore does not establish collection of A into the returned
Function view. Negative collection of c for direct's argument uses upper
records, which also does not supply this positive return witness.

The exact replay branch is `machine/bounds.rs:3839–3848`: qualified parents are
registered only when replay admission is not Incomplete. Their transaction at
2916–3021 distinguishes a new target from an existing lower record and ledger
bootstrap. `2332–2370,2476–2568` connects lower derivations/supports; the
replay clause is a conjunction of its actual lower and upper premises
(`1132–1248`; also 1301–1325 for replay evidence). The final r_Y ledger is not
supplied by the frozen input evidence. `proof/mod.rs:10014–10031` distinguishes
absent ledgers, mismatched supports/formula errors and actual evaluation;
`11739–11761` evaluates **both** replay premises. An independent r_c, an
uncovered initial upper claim, or emitted A <: Y cannot alone determine the
final r_Y decision after later canonical admissions and coverage changes.

This is the first unresolved predicate, not an observed exclusion. The earlier
[projection census](2026-10-11-oracle-direct-static-projection-census.md) already
records the incomplete admission/collection census. This audit does not claim
to close that census or count another restatement as progress. Its additional
source discrimination is why the apparent c-only shortcut fails at the actual
collection consumer.

## Conditional compact continuation; no simplification-survival claim

If the same A-bearing r_Y is selected, the source continuation is concrete:

| Stage | Exact source action and limitation |
| --- | --- |
| Lower collection | `compact/collect/mod.rs:898–917` passes the left bound weight union the outer weight to `compact_pos_bound_id(A,...)` and positively merges the result. |
| Function | A is not PosVar, so 1128 dispatches to `type_nodes.rs:13–23`: a CompactFun is constructed; arguments receive empty carried weight, while result Value/Effect receive the carried weight. |
| Result Effect | For Stack(Var(e), PUSH α), `compact_pos_effect_id:196–219` first tries a row-item view. `compact_pos_row_item:261–289` reaches Var(e) and returns None; it therefore falls back to positive stack collection at 87–95, then `compact_var_side(e,Positive,...)`. A concrete row prefix is not substituted at this branch. |
| Weighted variable | `compact/collect/mod.rs:746–788,791–803` constructs a covariant occurrence with the carried weight and merges e's own bounds. Recursion may move its expanded form into a recursive bound and return an empty-weight variable; literal root-path persistence is not automatic. |
| Merge | `compact/merge/entries.rs:288–306` preserves Function result polarity while merging corresponding ports; final α weight still depends on all actually merged weights and occurrences. |
| Before generalization | `generalize/mod.rs:136–157` performs alias expansion and simplification before `805–834` computes quantifiers, prunes dead weights and cleans stacks. `compact/analysis/mod.rs:163–202` applies interval collapse, polar/co-occurrence fixed points and sandwiches. None of these has been evaluated on direct's final root here. |

With empty outer/bound weights and ordinary nonrecursive e collection, the
annotation's positive stack branch carries PUSH α into the constructed
covariant e occurrence. The actual r_Y weights, recursion and simplification
input are additional premises, not established by A's syntax. An equivalent
positive Function/result-Effect view carrying α after simplification remains
unverified. Installed stack-quantifier selection is outside this audit's stop.

## Evidence, resources and recommended next action

Method: static source correspondence, no transition checker or execution oracle.
The pinned Oracle source is independent of a newly invented model, but this audit
shares source bytes and constructor premises with the proof lane. It does not
revalidate prior binary/build correspondence or certify its own artifact.
Seeds, ranges and mutations: none. No Oracle invocation, instrumentation,
compiler edit, test, build, formatter, network operation or child launch.

Checks: bounded rg/nl/sed/cat reads, read-only revision/status queries, SHA-256
and pinned-byte comparison for five Y3 and eighteen Oracle dependencies.
All 23 matched their pinned bytes. A few combined outputs were truncated;
decisive branches were reread narrowly. Guessed `constraints/bounds.rs` and
`compact/merge.rs` paths were absent and supplied no evidence. No heavy process
or sample ran; at most two lightweight shell reads were concurrent. CPU/RSS and
total wall time were not instrumented. No numerical wall/CPU/RAM quota was
supplied; the static-only and exhausted Oracle invocation limits were obeyed.

Unverified: complete actual admission/coverage/ledger census for r_Y, final
projection decision, accumulated compact weights and recursive bounds,
simplification survival, final selector, installed scheme, provider/use/output
lineage and universal H. No minimized counterexample was established.

Recommended next action: primary keeps the existing r_Y collection predicate
OPEN under the replay/projection owner and seeks that specific retained owner
evidence. The prior passes left the same state premise untouched; another
source-presence checker or display probe would not discriminate it. With the
Oracle budget exhausted, obtaining new runtime owner evidence requires a
separate primary assignment and budget; this note authorizes neither.

## Commit packet

- Exact leased path: `notes/progress/2026-10-12-oracle-direct-return-projection-audit.md`.
- Baseline: Y3 `016cca26609ccd17364c31ba2b5a9e91f80dd87f`; Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Dependency hashes changed: none. Original H SHA-256 `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1`; prior native transport `5b0d56da9df4d11c9fc4959451df6b2b30ba92327a278ec866c65a9d334a1af3`; prior census `c8ee639b3ec53bdb9cbd202345b83b30d96745548c18b9959b3703c0ed2584f1`. All cited Oracle bytes match their pinned commit.
- Review status: producer-frozen, independent review pending; source characterization only; H OPEN.
- Checks already run: focused static reads, 23 pinned dependency byte comparisons (22 also hashed), leased-note newline/fence/whitespace and diff checks. Zero execution/build/test.
- Proposed checkpoint message: `research: distinguish Oracle direct annotation and returned projection inputs`.
- Shared-record deltas intentionally left to primary/curator: distinguish Name(cb)'s c from named wrapper result Y; record that secondary aliases/positive alias expansion do not collect c's Function lower; keep r_Y's final projection and α survival OPEN. No shared task/index/theory/authority file was edited.

Writes stop at handoff before frozen review.
