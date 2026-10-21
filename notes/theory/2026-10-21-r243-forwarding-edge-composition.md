# R243 — Forwarding-edge composition

Status: partial constructor-level result; unreviewed. Parent, R71 and R72
remain OPEN. One equal-age Local edge into a direct-terminal provider is
traced; arbitrary-chain induction and mixed-age relay cases are not closed.

## Fixed obligation and result

The unchanged parent is
`notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1, 6–7
(SHA-256 `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`).
Keep its shared satisfying assignment, original formals, arbitrary finite
chains, repeated calls, simultaneous entries and finite prefixes. R242 is the
direct-terminal base, partial and unreviewed.

For one source shape with a local `relay (u:[io]int) = bridge u`, where
`bridge (x:[io]int) = x`, followed by an actual `relay t` Apply, the source
constructors supply two different Local FreshUse maps. Let `nu` map the
original `bridge` graph into its callee occurrence inside `relay`; let `mu`
map the original `relay` graph into its actual callee occurrence in `relay t`.
The `bridge` instance in that relay use is the composition `mu_next = mu o nu`
on endpoints. The source occurrence and context-use identity for each map stay
distinct.

For the equal-age case where both local schemes' generic rows are above their
capture boundary, the captured physical rows give this conditional chain:

```text
e_A <= mu(t_u) <= mu(n_u)
    <= mu_next(t_x) <= mu_next(n_x) <= mu_next(r_x)
    <= mu(c_u) <= mu(q_u) <= mu(r_u)
    <= e_C <= e_out.
```

Here `n_u` is relay's exact formal-Name effect and is also the actual
argument-effect component in its body Apply `bridge u`; `c_u` is that Apply's
invocation-effect demand, `q_u` its application effect, and `r_u` relay's
Lambda return effect. `e_A`, `e_C`, and `e_out` are the actual argument,
demand return-effect, and output of the enclosing `relay t` Apply. Relay's
reverse Name equality `mu(n_u)<=mu(t_u)` is also admitted.

This establishes one constructor-level forwarding edge into the
direct-terminal base, conditional on successful drains, both Local routes,
bound capture/restoration and the two exact Apply admissions. It does not prove
the parent for arbitrary chains or runtime behavior. It does not treat `nu`
and `mu` as one map or identify equal endpoint values as source correspondence.

## Source construction and joins

The source planner visits Apply children before its recipe and schedules the
Lambda action after its body. In the inner `bridge u` Apply, the Local callee
route constructs `nu` from bridge's published scheme; the Name `u` keeps its
registered Computation occurrence. `ApplySourceInput` retains the exact callee,
argument, argument-effect, result, application-effect and checking occurrence.
`admit_candidate_fact` checks those endpoints against the retained Apply
relation before it builds a negative Function demand from the actual argument,
that exact argument-effect, a fresh invocation-effect row and the actual
result. The typed Function child is therefore `n_u <= nu(t_x)` and its RE
child is `nu(r_x) <= c_u` at this same Apply. The Application effect admissions
include `c_u <= q_u`; the Lambda slot 4 drain supplies `q_u <= r_u`.

The bridge formal Name and Lambda source actions admit
`t_x<=n_x<=r_x` and `n_x<=t_x` before the bridge Function root is exposed,
as in R242. `nu` restores these reached graph bounds through one map and
physical readback. In the relay source scheme, `t_u<=n_u` is emitted by its
registered Name action. Starting Capture at relay's positive Function reaches
its AE row `t_u`, then `n_u`; the exact Apply child reaches `nu(t_x)`, whose
restored bounds reach `nu(n_x)` and `nu(r_x)`. The Apply RE comparison reaches
`c_u`, slot 2 reaches `q_u`, and slot 4 reaches `r_u`. Capture retains these
physical bounds with their source relation/evidence. The slot-4 completion
receipt is attached to its seed relation even though slot 4 has no Apply
checking event.

The enclosing `relay t` Apply compares its actual argument-effect `e_A` with
`mu(t_u)` and `mu(r_u)` with its exact demand RE `e_C`; its own Application
effect admits `e_C<=e_out`. `LocalFreshRoute` retains each use's source
occurrence, distinct `context_use`, graph and row/evidence remaps. When relay's
captured graph is used, `mu` maps the already restored `nu` endpoints as part
of that graph. Thus `mu_next` is their pointwise composition on generic rows;
this example has no shared row inside either local scheme. Shared anchors
remain separate coordinates and are not covered by this equal-age derivation.

## Limits and falsifiers

The R187 bridge/relay candidate has an older bridge whose body is itself an
Apply. Its intermediate source effects have different levels and owners from
this direct-terminal bridge. This derivation does not establish that all of
those rows enter one graph; keep R187's emitted-fiber/source qualification and
candidate model open. A missing mapped intermediate edge in that case is a
falsifier for extending this certificate by logical connectivity alone.

The general parent step still needs an actual source/use witness for every
`mu_i` and each composed next-provider `mu_{i+1}`, including shared anchors,
recursive/internal routes, arbitrary finite suffixes, repeated calls and
simultaneous entries. R239's `ReplayUseAntecedentsNotRetained` and unresolved
source/use correspondence remain explicit. No arbitrary-chain induction,
R71/R72 closure, production, implementation, test, build or sample claim is
made. No code changed; no tests, builds or samples ran.

Contract and byte pins:
`tasks/agent-loop/sprints/simple-sub-forwarding-edge-composition-20261021-r243.md`.
