# R48 independent specification review receipt

Receipt owner: `/root` (Luna primary), transcribing the read-only final review
response from `/root/r46_spec_review`. Review assignment was fresh for R48 and
read-only; reviewer did not write this file. Target contract revision 1 and the
following implementation/proof hashes were verified by the reviewer.

## Disposition

**BLOCKING — the scoped fixture cannot reach the requested inspection.**

The test enables scoped admission and requires `session.execute().unwrap()` at
`candidate_scheme.rs:2675–2677`. Its active recursive `loop` references emit
`Action::Link` at `candidate_source.rs:1244–1249`; Link admits an endpoint link
but creates no FreshUse route. Scoped Apply admission unconditionally calls
`authenticate_scoped_apply` at `shadow_apply.rs:1772–1775`, which requires the
matching occurrence-indexed `LocalFreshRoute` at `candidate_call.rs:727–733`.
That entry is installed at `candidate_scheme.rs:688–692` by
`commit_local_use`, reached from Local reconstruction, not Link.

The earlier direct `loop x` Apply can fail before the helper use; q has the same
missing route. Assertions after `execute()` therefore cannot establish q
reachability or temporal inspection. This is a static obstruction in the
frozen path, not an observed runtime failure or a source-semantic counterexample.
R48's stop condition requires reporting the earliest obstruction and forbids
execution when reachability is unsupported. Keep the focused Cargo command
GATED/NOT RUN. Any alternate fixture, route or admission behavior needs a new
primary-approved contract revision.

No other specification issue was found in the bounded candidate: it retains
both signed C/D coordinates and route identities, the R47 no-hit invariant,
negative substitutions, and the test-only boundary. These remain unexecuted
assertions. The proof is conditional and the parent theorem remains
**OPEN, 0 → 0**.

## Frozen review target

- R48 contract: `e17bd3f602cb00cb600d6647432a18cc6df5d5ce8d5eb59a78eba52eb8dfbc5a`
- Conditional proof: `50f70a8a47faaac1cff670044faf4faafbf2a495d0a437bcab6bee1983095e13`
- Implementation receipt: `dd9aa87b15835105ed6445c3106045d1b9a84447dfa2a8ab1bd7fc7f3a0eb884`
- `candidate_scheme.rs`: `d4ff8a9e98eb667a5eb85aff9c0feec1f0227e86257bb56892493ac1d04a9278`
- `candidate_intrusion.rs`: `8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4`

Reviewer performed read-only exact-scope inspection and hash verification. No
Cargo/build/test/runtime or source edits. Requested role `spec_auditor`;
effective model/effort, CPU/RSS and exact elapsed grant usage UNKNOWN. No
descendants.
