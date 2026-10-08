# Annotated formal constructor: owner-to-consumer draft

Date: 2026-10-09
Status: Draft; not approved
Scope: one annotated higher-order formal and one direct body Call
Authority: existing decisions only; no new language or implementation rule
Implementation authority: none
Assignment baseline: `83399fb85ef3be76332437113b82c914d9e8d54a`
Review: independent compiler-referee and spec-auditor review found no
actionable findings; no tests or builds run

## 1. Purpose and limits

This draft makes the missing annotated-formal constructor obligation
reviewable. It names the facts the source owner must produce and the distinct
consumers that use them. It does not choose a solver representation, source
acceptance rule, permission activation condition, protection seed, or local
effect-removal rule.

The semantic target is the already approved shorthand
`apply(f: _ -> [io] _, x) = f x`. A nearby grouped-header syntax shape is
`my apply (f: _ -> [io] _) x = f x`; its exact recovery-free parse and current
production lowering have not been executed. This draft asserts neither source
acceptance nor a parser change.

The only output is a conditional owner-to-consumer contract. A missing
certificate blocks this proposed derivation; it does not reject the source
program. The wider source-adequacy, principality, membership/admission,
production-conformance, and F5-cutover gates remain unchanged.

## 2. Existing decisions that constrain the constructor

The source annotation, inferred public contract, and internal evidence-rich
view remain distinct. For the unannotated `f` example, annotation absence
causes a provisional fully protected Handler view and ordinary-value evidence
later determines the inferred formal/use relation. For the annotated example,
only the corresponding `io` contribution may be removed; permission does not
assert removal and excludes unrelated contributions. Actual callable role and
entry are preserved.

Each actual annotation boundary compares its current endpoint directly with
its complete normalized target. On success it exports the target together
with local realization evidence and retains prior evidence. Endpoint equality
or a previous successful comparison does not replace this direct boundary
check. The original annotation, source occurrence, scope, typed paths, and
joint `xi=(nu,K,D)` must remain correlated. Pending comparison success `Q`
cannot create those source facts or admission.

Directional protection applies from an already protected inferred variable to
the designated output-effect occurrence of its original Function upper use.
It does not back-protect an existing provider lower occurrence. Event/profile
protection additionally needs its actual contribution, typed incidence,
receipt, and live receiver evidence. Annotation presence alone supplies no
protection or no-protection conclusion.

## 3. Candidate constructor vocabulary

The following are logical names for this draft, not approved solver atoms,
runtime carriers, HIR fields, or new language constructs. `a` identifies the
written annotation occurrence; `b` the resolved formal; `beta` its shared
contract slot; `sigma` the original scope; `xi` the one original joint
assignment; `E_a` the actual endpoint at this boundary; and `T_a` the complete
normalized target.

```text
AnnotationAt(a,b,beta,sigma,role,E_a,T_a,permission_i,xi)
BoundaryUse(a,beta,sigma,u_a,E_a,T_a,xi)
Contribution(k,o,p,owner,provider,sigma,xi)
Incident(a,permission_i,k,o,p,beta,sigma,xi)
Direct(a,u_a,E_a,T_a,epsilon)
Lawful(a,permission_i,k,o,p,sigma,xi,rho)
Frame(rho)
```

`o` is an original typed effect occurrence and `p` its typed path. Contribution
identity `k` is distinct from a protection-seed identity. `owner` and
`provider` retain orientation; the same family spelling, equal endpoint, or
same formal does not merge these coordinates. `epsilon` is the direct local
boundary evidence. `rho` is a proposed local change witness whose frame
preserves unrelated contributions and evidence. The complete constructor
meaning of these names remains to be supplied by their owning judgments.

## 4. Producer and consumer order

### 4.1 Source resolution and formal registration

The syntax/source owner identifies the actual grouped formal annotation,
resolved binder, declaration component, scope and source order. Formal role
generation retains the existing outer Value role for an ordinary named
parameter; it does not invent a source entry from the nested Function
annotation. Annotation absence/presence is attached to the original formal,
not inferred from a later Name use.

Current production HIR does not carry this package: `HirParameter` has only
identity, name and range, and its ordinary header lowerer rejects grouped
annotated/multi-parameter targets. The current solver's `parameter_recipes`
retain the parameter identity only. The ordinary Parameter-to-Lambda route
allocates a Value row and a four-port Function fact but does not construct
`E_a`, `T_a`, annotation permission, or source contribution evidence.

### 4.2 Annotation normalization and direct boundary

The owning annotation elaboration must establish `E_a` from the actual
boundary in the original source derivation and normalize the written
placeholder/Function annotation to a complete `T_a`. It retains the exact
`[io]` permission occurrence and designated Function effect position. It also
retains prior local evidence and original dependent scope/occurrence data.

The candidate boundary relation is:

```text
AnnotationAt(a,b,beta,sigma,role,E_a,T_a,permission_i,xi)
------------------------------------------------------------------ candidate original boundary
BoundaryUse(a,beta,sigma,u_a,E_a,T_a,xi)
```

`Direct(a,u_a,E_a,T_a,epsilon)` may discharge this boundary only at this
actual `E_a` and complete `T_a`. The target export appends `epsilon` to prior
evidence. Later boundaries compare their own current endpoint with the
previously exported target. Whether and how the producer proves that the
symbolic `u_a` is introduced before comparison success is known remains an
explicit source-construction obligation; it is not inferred from `Direct`.

This relation does not classify every annotation boundary as a
`SourceUpperUse`. The A5 classification and A6 authentic seed-at-exposure
proof remain separate obligations for directional protection. The selected
absence-seed constructor does not apply to this annotated formal; this does
not prove that no other seed origin is possible.

### 4.3 Contribution and annotation incidence

The source/typed contribution constructor identifies each effect contribution
at its original typed position, owner/provider orientation, scope and shared
`xi`. The annotation/use constructor then has to prove which contribution is
governed by the exact permission occurrence:

```text
AnnotationAt(a,b,beta,sigma,role,E_a,T_a,permission_i,xi)
Contribution(k,o,p,owner,provider,sigma,xi)
Incident(a,permission_i,k,o,p,beta,sigma,xi)
------------------------------------------------------------------ candidate local permission
MayRemove(a,permission_i,k,o,p,beta,sigma,xi)
```

The output records permission only. It does not remove an effect, remove a
seed, establish a handler, or change an actual callable role. The incidence
must be a typed source correspondence from its owning constructors. A family
name/depth marker, matching printed `io`, endpoint equality, successful `Q`,
or cardinality assumption cannot supply it. Other same-family contributions
remain separate and require their own preservation evidence.

### 4.4 Lawful local realization and preservation

Permission is consumed only by an independently justified local realization:

```text
MayRemove(a,permission_i,k,o,p,beta,sigma,xi)
Direct(a,u_a,E_a,T_a,epsilon)
Lawful(a,permission_i,k,o,p,sigma,xi,rho)
Frame(rho)
------------------------------------------------------------------ candidate realization
export T_a with local (epsilon,rho); retain prior evidence and origins
```

`Lawful` must specify what local change is permitted at this contribution and
its actual placement/scope. `Frame` retains unrelated effects, provider-owned
marks, constraints, origins, and all prior evidence. These are missing
producer judgments, not established by the inference-view permission or the
direct type check. This draft selects neither release at an annotation slot
nor release conditioned on a live eligible handling opportunity; the current
evidence does not establish complete observable models for those candidates.

For an actual handled request, a separate producer must supply its event to
contribution incidence, actual provider, receipt, observation, and then-live
receiver/eligibility evidence. This draft does not make that event package
the universal precondition of every annotation-local permission, and it does
not synthesize a request or handler from a static slot.

### 4.5 Name/Call and transport

The body Name export identifies its actual resolved binder/provider and
transports the same shared contract and original evidence. The Call constructor
emits the complete original Call demand, preserving actual provider/entry,
argument computation, result consumer and future/other alternatives required
by the selected Call contracts. It retains an independent upper-use
classification and the original occurrence/scope map. It does not identify
the annotation check with the Call demand even if their eventual endpoints
solve equal.

Generalization/use transport applies one certified whole map to annotation,
contribution, incidence, seed and local realization evidence together. It
preserves original identities, scope maps, shared witnesses and `xi`.
Transport preserves an established relation; it cannot create the missing
annotation or exposure premise.

## 5. Conditional composition claim

Assume authentic producers supply all judgments in §4 with matching original
identities/scopes and one `xi`; assume the direct boundary proof succeeds;
assume the lawful action and frame are independently justified; and assume
every use/transport step has its selected whole-map certificate. Then the
source derivation may record the scoped permission for exactly the incident
contribution, discharge the direct boundary at its current endpoint, export
the normalized target with local evidence, and preserve prior/unrelated
evidence through realization and transport.

This is only constructor composition and preservation under those hypotheses.
It proves neither the producer rules nor annotation source completeness,
universal C5 protection applicability, principal solutions, full Function
membership, Option 2 admission, or production correspondence. Substituting a
checker that accepts the same missing judgments would not establish them.

## 6. Separating cases and failure conditions

The required review should test at least these boundaries:

- **Same family, different position:** move `io` between original
  `arg_eff` and `ret_eff`; the annotation occurrence must retain its exact
  designated position. The frozen Oracle family/depth sidecar maps these
  positions to the same marker, while its richer constraint lowering retains
  separate ports. Neither fact supplies the new source incidence.
- **Same family, independent provider:** two same-family contributions with
  different provider/scope identities must not let the annotation permission
  remove or overwrite the unrelated one.
- **Incoming provider:** a provider lower Function occurrence is not
  back-protected by the formal's upper-use seed; provider-origin evidence
  remains independent.
- **No annotation:** the selected full-protection seed is tied to actual
  annotation absence at formal registration, not absence at each Name use.
- **Direct check and prior evidence:** a later successful comparison cannot
  replace the actual current endpoint or erase prior local evidence.
- **No live receiver:** neither candidate is granted an observable handling
  trace merely by assigning a different static release certificate.

Failure of an input derivation invalidates this conditional composition only.
It does not create a new source rejection. Exact parser recovery, annotation
normalization, source acceptance, all Call branches, and runtime observation
remain unverified.

## 7. Open decisions and next gates

The following are not resolved by this draft:

1. Authentic normalized target and current endpoint generation for the
   annotation, including the original boundary/use correspondence.
2. A5 original upper-use classification and A6 seed origin/stage rule at
   annotated uses, together with exhaustive exposure coverage.
3. Annotation-to-contribution incidence and lawful local realization/frame
   producer, including any required activation condition.
4. Shared-interface conflict/principality, recursion, generalization and
   use-time transport.
5. Complete source acceptance and production membership/admission under
   independent Option 2 alternatives, implementation correspondence, and
   eventual F5 cutover.

Representation choices such as HIR ownership, solver storage, reference
lifetimes, allocation/failure behavior and public/private API placement are
not fixed here. A separately reviewed implementation architecture and
recorded user approval are required before making those choices durable.
The next safe artifact is a reviewed owner-to-consumer constructor contract
that either supplies each conclusion from an authentic head or leaves the
exact producer gap explicit. User input may wait until that review gives
concrete, observably distinct alternatives; no approval is implied by this
Draft.

## 8. Review and verification plan

Mode: M2 contract/cross-layer draft review. Assign one compiler-referee review
for ownership, occurrence identity, soundness boundaries and failure cases,
and one spec-auditor review for exact adherence to approved contracts and
scope. Converge when every derived conclusion has an authentic supplier or
remains explicitly conditional, no selected behavior is strengthened, and
no new implementation/semantic authority is claimed. Batch any accepted
blocking/major findings into one repair; otherwise retain the draft and open
gates.

Producer checks are static source/design reads and Markdown integrity only.
No tests, builds, parser execution, probes or benchmarks are authorized by
this research draft. No code, fixtures, questions, shared authority/index
records or production HIR/solver paths are changed here.
