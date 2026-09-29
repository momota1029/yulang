# Graph-boundary instantiation operation candidate

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Classification: unselected Gate C operation candidate; no implementation authority

## Candidate operation

The abstract-semantics draft now describes use instantiation over a shared SCC
graph and member-selected views, without making closed per-member trees the
authority. Ordered root preparation and the all-member visibility barrier
precede external use handling. `H_d` retains source TypeVar identities;
`Free_d` resolves through an injective component-stable `beta_C` to shared
anchors, while `Lsrc_d = Gen_d ∪ Cycle_d` maps through member-owned `Phi_d`
ports and then per-use injective `sigma_(d,u)` fresh identities. The composed
map `rho_(d,u)` is explicit. Map
application includes roots, selected edges, recursive-bound payloads, and
type-variable occurrences in evidence; evidence identities must be transported
with their validity dependencies or revalidated. Graph-node memoization is
scoped to each `(d,u,sigma_(d,u))` operation.

Fresh target identities must avoid the full receiving solver identity set
`I_recv`, including caller variables and all incoming-use constraints, as well
as other uses' fresh ranges. This preserves a variable that is local in one
member view but `Free` in another without capture. Internal SCC references
remain open live-root edges during collection. Empty solution fibers remain
empty. The operation's conditional assignment semantics are separate from its
operational transition; type values, subtyping, public observations, and
adequacy are still undefined.

## Independent review

An `architect` recommended separating (1) a graph-boundary transition from
(2) a conditional solution relation. The transition can describe identity
freshening, selected-edge transport, use insertion, ordered root/view inputs,
and failures without choosing a carrier. Any claim about possible root types,
subsumption, soundness, or principality still requires a carrier, endpoint
evaluation, subtype relation, and an adequacy theorem. The architect treated
this as an unselected candidate, not a design decision.

A `compiler_referee` delta-reviewed the operation. The first review identified
missing global freshness against caller identities, incomplete evidence-payload
transport, cross-member imported-anchor lookup, and memoization scope. The
draft now requires: `beta_C` to be shared across views; fresh ranges
to avoid `I_recv` and each other; all identity-bearing payloads to be mapped or
their proof dependencies revalidated; and memoization to be per use operation.
The final delta review found these specific counterexamples closed. It found
no new contradiction within the operation, while confirming that source
partition coverage and cross-member relational composition remain unproved.

A focused follow-up found and closed two formal domain gaps: the single-view
`Root_d` definition had an unbound use index, and an explanatory `Member`
abbreviation applied the source-ID graph directly to fresh-ID assignments. The
draft now defines the root observation using any valid fresh renaming and cites
the conditional transport lemma for independence from the chosen fresh IDs;
the multi-use formula names the renamed view explicitly. The source-to-port
map is named `Phi_d`, with `Lsrc_d = Local_d`, and injectivity of `beta_C` is a
stated precondition unless a separate quotient proof is supplied. The referee
inspected the changed symbol/domain sections only; semantic proof validity and
Oracle compatibility remain unreviewed.

## Remaining Gate C obligations

The operation is still not an equivalence theorem. In particular, the
candidate lacks a defined observable result function, a proved relation between
saved member views and the Oracle at each ordered epoch, a total source
`Free`/local partition across member views, a proof of cross-member batch
composition, and solver adequacy for the claimed graph class. The carrier and
recursive subtype rule remain unselected. The recent Rust Oracle probes only
characterize recursive interval installation/retention; they do not establish
recursive subtype comparison or scheme principality.

No compiler code or permanent tests changed for this design-record slice. No
tests or resource measurements were run for this record update. The next Gate C
artifact should formalize the observation function and prove injective graph
transport under explicit validity premises, then extend the root-indexed
Oracle simulation to the use transition. Gate C stays open.
