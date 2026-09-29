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

## Repository state and constraints

The source authority remains
`notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md`,
especially §§8–9, 23, 25, and 33. The drafts remain non-authoritative. The
current F5c guarded-cycle capture plans on `yulang3` have consumed their
authorized process runs; this research branch will not repeat them.

No code or tests changed in this kickoff. The first next action is a compact
formal state model and reference relation for pure F5 extrusion versus
intrusion. Implementation and any F5 scheme/lifecycle change remain behind
independent review and explicit user approval.
