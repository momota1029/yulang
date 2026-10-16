# NPAIR forward witness and ingress readiness

Status: Draft; unapplied implementation-readiness contract, no compiler-code
authority.
Sprint: `npair-forward-source-witness-realization-20261017`, revision 1.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN.

## Purpose and frozen result

This Draft defines the narrowest executable gate justified by the forward
source-witness attempt. It does not authorize source admission, an N-Ingress
consumer, compiler code, tests, or a semantic change.

The preceding candidate proof starts with the original dependent contribution
witness `w`, then follows the actual Operation reference/member, native
Support(view) seed, physical emission/admission, FunctionPort and ordered Replay
records toward the recovered concrete Permission port. It establishes a
conditional native structural incidence path. It does not derive adopted
`At(D,w,delta)`.

Two source constructor premises remain open:

```text
eta_op: the same original w contributes at this exact Operation reference's
        positive result-effect port in its original dependent predecessor context;
realization_op: the source declaration/reference instance and eta_op
                correspond to the emitted OperationOrigin, view, member,
                port and exact physical admission.
```

If the original `w` already contains `eta_op`, preserve it. The native
correspondence still needs its owning source constructor. Native member,
family, slot, occurrence or Contribution identity cannot stand in for the
complete provider/observation/assignment/world/typed-position/lineage witness.
No new event ID is established as necessary.

The concrete receive annotation is separately refused by
`candidate_source::preflight_formal` before its FormalAnnotation action is
emitted. Therefore the current source route does not produce an admitted
negative-concrete descriptor run. Internal producer availability does not
change this.

## Three independent gates

### 1. Native structural certificate

An eventual read-only validator may report **structural incidence only** for a
single live successful construction snapshot when it checks all of the
following:

1. The exact Permission D, formal domain and typed Function path identify the
   same raw negative effect-port occurrence; validate Function tags, field,
   variance and links 43/44. Check a canonical representative separately from
   the raw occurrence.
2. The source Operation reference and its declaration/owner/occurrence/typed
   position produce a source-owned OperationOrigin/view/member. Validate the
   live physical Support(view) lower against its exact BoundAdmission,
   BoundEmission owner/lane/index and current slot operand.
3. Each FunctionPort step matches actual endpoints, Function field, variance
   operation and bound keys. Each Replay step validates both ordered inputs
   and endpoints. A finite witness tree must retain the premises used; graph
   reachability is insufficient.
4. The chain reaches a live lower at the recovered Permission port and validates
   its own admission and optional OwnerEmission.processing relation.

This result has no implication for a complete original `w`, `delta`, source
acceptance, adopted At, eligibility, subtraction or production. It is safe to
use only for debugging/research until a consumer contract separately names a
structural-certificate type and explicitly prevents it from being interpreted
as semantic ingress.

### 2. Semantic witness realization and adopted At

This gate remains **OPEN**. It requires the original Operation/Call source
supplier to establish `eta_op` and `realization_op`, and each source rule used
by the FunctionPort/Replay derivation to lift the same `w` and `delta` through
the actual dependent contexts and scope changes. Only then may an independently
reviewed owner establish `At(D,w,delta)` for the exact incidence.

The native structural validator cannot fill this premise by selecting the
first Origin, matching an effect family, trusting slot 42, or choosing a
Contribution ID. Multiple alternatives must remain explicit. If the source
supplier cannot establish the relation from original constructor evidence,
return the precise missing premise to Luna for a source-authority decision;
do not create a consumer that claims At.

### 3. Source admission

This gate remains **OPEN** and independent of gate 2. `candidate_source`
preflight rejects the negative concrete-only formal row before the action and
ordinary formal links exist on the receive route. Its source owner and Luna
must review a separate admission contract that preserves ordinary constraint
generation and the original source-domain quantifiers. A future change cannot
delete the refusal or claim an accepted source run under this Draft.

## Lifecycle, traversal, resources and failure

Any future structural validator contract must specify these before executable
implementation:

- **Existing and future lowers:** Permission publishes after both synchronous
  formal drains. Inspect every already-present qualifying lower at publication
  and subscribe to later lowers while the incidence remains live. A future-only
  hook is incomplete.
- **Alternatives and cycles:** preserve every relevant Origin, admission and
  derivation alternative. Use explicit cycle detection for relation traversal;
  do not select the first Origin or confuse multiple proofs of one `w` with
  distinct provider witnesses.
- **Lifetime and invalidation:** tie the certificate to one successful route
  and arena snapshot. Reject route rollback, truncated/reused slots, stale
  canonical representatives and copied/generalized presentations unless their
  owners supply an explicit correspondence. Permission record truncation is
  checkpoint-owned; emission, bound, canonicalization, FunctionPort and Replay
  owners must specify their own invalidation behavior.
- **Bounded work and storage:** define finite deterministic traversal and
  storage limits, checked byte/work accounting, and atomic private accumulation
  before any published certificate. Exact numeric caps belong to the
  implementation contract after owner audit; this Draft authorizes no runtime
  path.
- **Failure disposition:** incomplete, stale, cyclic-unresolved or over-budget
  evidence yields no published semantic ingress. A private validator attempt
  may stop safely while preserving route rollback invariants. No residual or
  subtraction may be published on absence of evidence. Runtime exhaustion
  behavior needs a separate approved execution gate.

The failed-current-route source refusal occurs before any of these native
consumer checks could discharge the receive obligation. The original NPAIR
source premise must be handled first by its owner.

## Exact owner-directed gates and falsifiers

- `NPAIR-OP-SOURCE-WITNESS-20261017`: original Operation/Call supplier provides
  `eta_op` and `realization_op`. Falsifiers include family-only matching,
  omission of operation-local substitution/scope, or treating slot 42 as the
  complete contribution judgment.
- `NPAIR-FORWARD-RULE-LIFT-20261017`: Function/context owners justify each
  source lift through actual FunctionPort/Replay nodes and dependent scopes.
  One-premise Replay, an arbitrary Origin, or an unsupported reindexing
  falsifies the certificate.
- `NPAIR-STRUCTURAL-VALIDATOR-20261017`: Luna may separately authorize a
  bounded structural-only validator after independent review. It must not
  return At, source admission, or a subtraction result. Stale evidence,
  dropping existing/later lowers or ignoring alternatives falsifies it.
- `NPAIR-SOURCE-ADMISSION`: source formal owner and Luna decide whether the
  exact negative concrete formal reaches ordinary FormalAnnotation
  construction. Deleting a refusal or narrowing original source forms does not
  satisfy this obligation.

Keep `J1` and `J2` distinct and preserve the original receive route
`f () -> R1 / Install(g) / whole FreshUse -> g ()`. N-Transport, whole
`rho_u`, actual receive consumer, subtraction, `C_sym`, F1/FK1, soundness,
principality and production remain OPEN.

## Frozen inputs

- Sprint contract revision 1 SHA-256
  `f3e55f3f8e0dc95658e69b85e0deb443265e9e5e1916fb5b90f4e688167309ef`.
- Forward proof artifact SHA-256
  `1d2c827cdf7661cc77a9edbb869bffd3cdcca7b51afba418789eaae9abf3cb3a`.
- Forward proof handoff SHA-256
  `184bcd86658ef5ed7f77513986b15be13e3f9e3b5223968153cc730fd5e309ad`.
- Applied producer, adopted source semantics, Operation/Call clauses, and
  native source pins are all enumerated in the frozen proof manifest.

No tests, builds, probes, Cargo, compiler or source execution ran. This Draft
is a reviewed-gate proposal only after its independent sprint reviews; it
cannot be treated as an executable consumer contract or language decision.
