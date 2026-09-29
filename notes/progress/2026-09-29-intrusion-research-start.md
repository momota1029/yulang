# SCC intrusion research start

Date: 2026-09-29
Branch: `research/simple-sub-intrusion`
Base: `yulang3` at `32f0a063`

## Scope

The user directed a fresh investigation of type inference and supplied two
exploratory notes: the SCC intrusion sketch and the intrude/effect-hygiene
memo. This branch starts a proof-first research track. It does not change code,
authorize implementation, replace F5/F5c, or approve a new scheme
representation. The in-progress F5c state remains on `yulang3` and its parent
commit.

## First gate

Compare ordinary polarized Simple-Sub extrusion with parent-based intrusion
for the pure F5 subset. Define the exact polarized boundary closure, variable
eligibility, target level, immutable generalized graph, per-member projection,
and per-incoming-use substitution overlay before claiming equivalence. Compare
both principal constraint consequences and each member's closed scheme up to
alpha-equivalence. Keep complexity and compact-output claims separate from
semantic equivalence.

## Independent review findings

An `architect` review recommends a read-only proof or executable
characterization first and identifies exact F5 constraints: member-local Q/R
namespaces, complete component publication, fresh Q/R for every incoming use,
open live roots for internal uses, and deterministic closed per-member
schemes. A graph representation does not by itself prove that the closed F5
projection avoids path expansion.

A `compiler_referee` review found two blocking gaps in the sketches for design
acceptance:

1. A definition SCC does not necessarily delimit the extrusion graph. F5
   extrusion follows exact positive/negative bounds across levels and may
   reach an enclosing non-generic variable or a younger variable outside the
   definition SCC. Parent allocation must cover the eligible polarized
   boundary closure, not just SCC members; polarity-blind sharing is
   unproved.
2. One shared parent map does not encode per-member binder ownership or
   independent incoming uses. Mutating a shared frozen graph for one use can
   constrain another use. The candidate needs an immutable generalized graph
   plus member-local binder maps and a separate fresh per-use overlay, while
   internal uses continue to reference live roots.

The referee also identified major open questions: the freeze snapshot must
preserve exact lower/upper rows and outside endpoints without allowing
instantiation to mutate publication; specialization cache keys are not
justified; and future hygiene transport needs binder ownership, freshness,
injectivity, and path-sensitive handler semantics. Effect behavior remains a
separate later gate.

Minimum discriminating witnesses include a nested Function sharing a variable
between argument and result with nontrivial lower/upper bounds and an outer
non-generic endpoint; one-sided Bottom/Top elimination; unguarded cycles versus
guarded R; opposite-polarity guarded re-entry with both R bounds; boundary
equality versus child-level quantification; and interleaved `f`/`g` incoming
uses with incompatible instantiations followed by an internal-use trace.

## Initial repository state

At kickoff, the research incorrectly treated
`notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md` as
the semantic target. The user later corrected that direction: the F5 Function
generalization and closed-scheme architecture is to be withdrawn as the target
for this redesign. The reviewed protocol above remains only to document the
mistaken gate and its review findings.

The current F5c guarded-cycle capture plans on `yulang3` have consumed their
authorized process runs; this research branch will not repeat them.

No code or tests changed in the kickoff. Implementation and any F5
scheme/lifecycle change remain behind independent review and explicit user
approval.

## Reviewed reference protocol

The first model is now recorded in
`notes/design/2026-09-29-pure-f5-intrusion-reference-model.md`. It separates
the pre-insertion transition comparison (needed to claim replacement of F5's
insertion-time level aging) from post-insertion per-member generalization and
projection. It also fixes `DefinitionUse.use_level`, same-member independent
uses, Q ordinal order, R lower/upper restoration, use cause/provenance,
per-use graph sharing, and atomic component publication/failure as comparison
obligations.

Mode: M3 design research, because the question touches type soundness,
principal schemes, recursion, and SCC publication. Pre-write architecture
review and post-write `compiler_referee` / `spec_auditor` reviews found and
closed one blocking scope ambiguity and several major comparison omissions.
The remaining minor finding asked for two incompatible uses of the same
member; that witness is now included. No production code changed, no tests or
measurements ran, and the note remains Reviewed but non-authoritative with no
implementation authority.

Next: build the Oracle behavior ledger and define the new abstract intrusion
semantics against those observations. The F5 Q/R shape, closed schemes,
numbering, and F5c resource contract are not acceptance requirements for this
redesign. Finite examples characterize a candidate but do not alone prove
soundness or principality.

## User scope correction and Oracle source map

The user clarified that F5 itself is to be abolished from the redesign target,
not preserved by proving intrusion equivalent to F5. The active scope is now
to replace F5 Function generalization/closed-scheme architecture on
`research/simple-sub-intrusion`. This does not authorize deletion from the
shared `yulang3` branch or modification of frozen `main`; the new design must
be reviewed and approved before implementation/cutover.

The concrete behavior source is frozen Yulang2 `main` at `a58eefc3`, consistent
with the repository's Oracle-compatible product priority. Read-only source
inspection found that Yulang2 `extrude_pos` / `extrude_neg` lower existing
variable levels during bound insertion. The 2026-09-29 sketch's statement
that ordinary Yulang2 extrusion creates fresh representatives is not borne out
by this implementation. The new intrusion semantics must be stated directly
and compared to Oracle observations rather than copied from that claim.

Useful Oracle locators: `crates/infer/src/constraints/machine/bounds.rs`
(`extrude_pos` / `extrude_neg` and bound insertion); `crates/infer/src/analysis/session/instantiate.rs`
(`quantify_component`, per-member scheme preparation); `crates/infer/src/instantiate.rs`
(per-use Q/recursive-bound freshening); `crates/infer/src/analysis/tests/case_02.rs`
and `crates/infer/src/generalize/tests.rs` (observable witnesses). The
Authoritative F4 SCC design remains applicable only to its Integer/resolved
Name scope; its scheduler and publication barrier are reusable evidence, not
Function-scheme authority.

The replacement charter is
`notes/design/2026-09-29-scc-intrusion-redesign-charter.md`. Initial
architecture review recommends an Oracle ledger, new abstract semantics,
finite intrusion characterization, representation/resource design, then M3
review and explicit approval. No code or tests changed and no measurements ran.
