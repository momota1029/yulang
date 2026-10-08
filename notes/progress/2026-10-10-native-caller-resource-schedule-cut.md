# Native checker caller and resource-schedule cut

Status: bounded research characterization; non-authoritative; independently
reviewed by a compiler referee and a spec auditor at this artifact's baseline
Baseline: `6c69e16e4` on `research/simple-sub-intrusion`
Scope: selected published unannotated `id` → Name `Instance` → monomorphic
Alias → PE decode → `Direct` checking boundary
Production implementation, semantic change, gate promotion, and F5 cutover:
none

## Result

The selected native Direct direction does not yet have a concrete source
checking occurrence or compilation-scoped attempt schedule to which a Rust
caller can be connected. This is now a narrower gap than “caller and resource
limits are unknown”:

1. SRC §3.4's `view(h,q,V)` is notation annotating an actual source checking
   rule, not an additional executable operation. The selected `id` plus alias
   path supplies an incoming polymorphic Name `Instance` and one monomorphic
   rebind, but does not itself supply a `view` occurrence.
2. The inspected ordinary HIR/solver path has no established native
   checking-occurrence producer, ordinary-root store, or Direct consumer.
   Existing scalar Q/R instantiation is not a whole-frame PE decode. The
   feature-gated shadow application path does not establish a native Direct
   caller.
3. Therefore the candidate construction/retry schedule, retained environment
   lifetime, session failure behavior, and concurrency admission are not
   determined. Numeric work/byte limits cannot be derived from the current
   checker fragment or F5 accounting.

These findings do not show that source checking rejects the selected program,
that every source grammar lacks such an occurrence, or that the approved
Direct direction is semantically incompatible with native inference.

## Selected discriminator and ordered boundary

The smallest useful semantic discriminator is the conditional client

```text
new(p,i,r); alias(i,j); view(j,q,Any)
```

with a supplied hereditary `Top` Value proof at the actual decoded ordinary
root pair. Under the selected PE construction, `new` allocates one whole-frame
root, `alias` reuses that frame, and Direct recognizes the submitted proof at
the exact roots. This is a declarative conditional path, not an existing
compiler call. The source text `my id x=x; my alias=id` does not by itself
provide `q` or the target/proof producer.

The missing producer must provide one authentic source checking rule
application, its target root, original scope/telescope, proof source, and
invocation schedule. An internal check inserted into unannotated `id` would
be a new scheduling proposal; it cannot be represented as an already present
source occurrence. If an actual owning rule is established, its ordered
consumer handoff is: authentic registration/formation; final-root publication
and `ProjectionExport`; incoming Name `Instance`; one PE whole-frame decode;
monomorphic Alias to the same root; construction of the checking request and
proof; Direct validation; and retention of success at the source occurrence.
The registration/Hreg predecessor remains under its existing no-repeat stop.

Concrete contract discriminators: a proof tied to `(u_i,v_Any,q)` must reject
substitution of a different fresh root `u_k`; monomorphic Alias must not
allocate a second root. These are semantic falsifiers for a future
implementation, not executed tests.

## Resource-bound falsification

The research Python checker does not supply a source-caller budget. Three
independent dimensions demonstrate why static table or proof-node counts are
insufficient:

- Dependency tuples at `tools/research_projection_public_direct.py:301–304,
  337–341, 372–373` have no length bound. Repeating an already valid
  ancestor dependency `m` times leaves top-level table/proof counts unchanged
  while increasing scans and retained references by Θ(m). This was a static
  mutation argument, not an executed probe.
- `PublicImport.ground_value` at line 135 accepts arbitrary Python objects;
  ground integer validation at lines 359–365 checks the Python type but not
  payload bit length. Table counts therefore do not bound retained bytes.
- `check_direct_fragment` validates the environment on each call (line 441)
  with no compilation/session budget. Repeating an identical valid check `k`
  times leaves static input unchanged while multiplying validation work by
  Θ(k).

The fragment also uses linear tuple lookup, rebuilds interface indexes,
repeats ancestry/index construction for inlets/imports, and recursively
rechecks proof type operands. Its local 512-node and depth-24 limits do not
bound whole-environment work, dependency entries, total attempts, or bytes.
These are properties of the Python research fragment, not evidence about the
proposed flat Rust checker.

The approved plan's work decomposition accounts for root constructions,
queries, and attempts and forbids refunding failed attempts. It is not yet an
executable operation formula. Exact work must also count incidence entries,
substitutions, telescope/equation entries, local-law steps, comparisons, and
examined bytes. Peak storage must include simultaneously retained roots and
proofs, work/visitation buffers, scratch high-water capacity, and overlapping
old/new reservations. A flat arena alone does not settle these quantities.

## Next evidence and stop condition

Obtain one authentic source checking-rule application and establish who
constructs its target/proof, when it invokes Direct, what retries after a
failure, which decoded roots/proofs remain live, and whether exhaustion ends
the compilation or permits fallback. Then define metering units against the
actual finite representation and attempt schedule before selecting numeric
limits. Do not infer these from F5 Q/R rows or from the Python fragment.

If no such occurrence exists in the selected language envelope, stop this
Direct-caller lane at the source-rule boundary and resolve the missing
source-constructor/placement decision before proposing an internal synthetic
check. Preserve the full type-inference/F5-replacement objective and all
existing open proof, source correspondence, principality, approval, and
cutover gates.

## Evidence and checks

Inspected the approved Direct and root-policy answers, SRC §3.4, the native
projection and Direct plans, PE §§4.1–4.3 and 6.1–6.2, the caller owner map,
the integrated `id` bridge, current HIR/solver owner sections, and the bounded
Python Direct fragment. Two specialist read-only passes contributed: an
architectural source-occurrence cut and a performance falsification of
caller-level numeric bounds. A compiler referee reviewed the source/order and
cost claims; a spec auditor reviewed the SRC/PE and approval boundaries. Both
found no actionable findings. The spec review did not independently verify
the HIR inventory, Python resource analysis, or dependency freshness.

The primary rechecked the direct dependency hashes against current HEAD; they
match the specialist snapshots. `git diff --check` passed. No production code,
tests, builds, benchmarks, or executable mutation probes changed or ran. No
pending question bundle was used.
