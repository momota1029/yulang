# cycle262 independent read review: request and pool bridges

Reviewer: alias-kernel subagent. This is an independent read review of the
coordinator's request/snapshot/pool modules, NOT independent review of the
reviewer's own GeneralFiniteAliasClosure262 or GeneralFiniteAliasSearch262.
No independent rebuild of the coordinator's modules was performed here.
Read at 2026-11-18 18:41–18:46 UTC; findings refer to the versions read then.

## ExecutableRequests262 / ExecutableSnapshot262

- requests_eq is equality of whole lists, not just membership: the same original
  sites list is filtered with equivalent Boolean predicates, then flatMapped.
  Site order and output order/multiplicity are therefore retained exactly.
- At initial review requests used the exponential cut reference. The coordinator
  subsequently announced replacement by the exact frontier component membership;
  the proof interface component_exact supports this without changing semantics.
- select/observe are executable parameterized definitions. roots is supplied as
  an arbitrary function of the finite rebase state. A noncomputable caller-supplied
  roots function would not make that concrete instantiation executable.
- The source snapshot, Plan and owner are fixed. roots may vary with finite state.
- completion derives candidate coverage and returns .ok, a bounded finite run,
  and absence of further novelty-gated Step. It does not establish Ready, Frame,
  packet correctness, model existence, or any language-wide resolution theorem.
- history_actual places the history existential outside the assignment universal.
  One history works simultaneously for every assignment. Its public selection
  clause only states each root occurs in roots of some state, rather than exposing
  the precise intermediate state at each history index. The induction uses the
  actual intermediate states, so this is a weaker projection, not a soundness gap.
- finish_history can preserve an empty model set. Successful settling is distinct
  from satisfiability, missing-output rejection, and packet/Evidence validity.

## ChildRequestPool262 / SourceRequestPool262

- equation_target distinguishes normalized variable references to declared output
  names (public purpose2) from clause output allocation (purpose5). raw_target
  follows actual emitted children and rawSites, rather than assuming arbitrary
  child requests belong to a guessed pool.
- raw_name follows the visible declaration and canonical requirements permutation
  to the registry's explicit finite output-name menu.
- product is a Cartesian overapproximation. Every member has a menu name and target;
  not every candidate pair is claimed to be source-reachable.
- trace_covered explicitly assumes finite future public ports. Its install case
  passes the actual Generated, Installable, and not-Committed witnesses from the
  old mixed Step directly to that premise. Old sites retain the induction invariant.
  The enqueue case is impossible because generated occurrences are already recorded.
- mixed_finite_requests actually discharges that finite-port premise by unpacking
  boundary.Initial into source formation, point roots, ground roots, and Coverage,
  then applying installed_port_enumerated. It does not assume Absorbed or require
  new child targets to have already appeared in the current alias class.
- all_requests holds for every reachable snapshot and every queried root because
  a selected alias-class output always comes from a recorded raw site.
- These are old-source-family request coverage results feeding the new rebase
  system. They do not assert old Step termination, or a simulation between old
  Step and the new novelty-gated Step. No such overclaim appears in these files.

## DynamicSource262

- inspect can vary the actual source snapshot at every rebase state, but the Plan,
  owner, pool, fact meanings and base assignment predicate remain fixed.
- covered and completion explicitly retain the hypothesis that every inspected
  state is Covered by the fixed pool. Importing SourceRequestPool262 alone does
  not derive an arbitrary inspect function's source reachability.
- step_actual selects a root from roots before and uses inspect before in its
  actual ClassEffects statement. Quantification is again simultaneous over all
  assignments after choosing the root.
- A reachable-inspection adapter could discharge the remaining coverage premise
  using mixed_finite_requests; it is not present in the three files reviewed here.
- Changing Plan/capture, transporting packet frames, validating Ready, and proving
  whole-language correctness remain separate obligations.

## Reference scalability and safe representation refinement

The original vertices list contains root, query, and two entries per edge; cuts
therefore enumerates exactly 2^(2+2*edges.length) entries including duplicates.
A safe refinement is graph-vertex eraseDups only: preserve vertex membership,
reprove root/endpoint coverage, and enumerate cuts over that list. This reduces
its exponent to the distinct vertex count but remains exponential. Do not dedup
sites or outputs when replacing the alias predicate: their order and multiplicity
are part of requests_eq. The separate frontier algorithm avoids cut enumeration
and can compute one component per root before filtering all sites.
