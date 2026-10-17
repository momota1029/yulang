# Source producer contract for the receive Entry/Exec/Return plan

Date: 2026-10-17  
Status: Draft, unapplied producer-readiness contract; no plan semantics adopted and no compiler-code lease.  
Sprint: `receive-caller-context-formation-20261017`, contract revision 2.  
Parent: inference/executor with proofs remains OPEN.

## 1. Purpose and fixed boundary

The reviewed [importer contract](2026-10-17-receive-source-plan-import-contract.md)
names a concrete missing input: an original source derivation `T` that owns
the selected two-Call component's Entry, Exec, Return, and dependent future
input fields. This note maps those fields to selected source constructors and
to current playground producers/consumers. It identifies the first missing
producer without treating syntax, candidate constraints, a native model, or
runtime observations as source `T`.

The bounded component remains:

```text
receive(f : Unit -> alpha+) = let g = f(Unit) in g(Unit)
alpha+ = ([ctrl]Unit) -> [ctrl]Int
```

The first Call's source context still requires the unproved ResultBind/context
plug law from the accompanying conditional proof. The direct source route
therefore has no complete `T` producer yet. The native route separately lacks
its anchored full MODEL. This producer map is a design audit only: it does not
write compiler code, test behavior, select an architecture, adopt the
candidate bridge, or authorize production cutover.

## 2. Producer-to-consumer map

| Certificate field | Selected source owner when an original `T` exists | Current playground producer | Current consumer / exact frontier |
|---|---|---|---|
| Source root, exact Lambda/Apply/Bind/Return occurrence and local destinations | Original source registration, Lambda/Parameter, Apply/Call, ResultBind and Return rules at their original scopes. Occurrence IDs identify syntax only; the source derivation must carry the actual source instance and shared `xi=(nu,K,D)`. | HIR local source plus `RuntimeProgram::from_hir` occurrence/label indexes. `prepare` returns `CandidateInference`, but `execute` binds it to `_candidate`; no original `T` is exported. | `Instruction`, `SourceSite`, `LocalBinding`, `Frame::Local`. Syntax and binder identity are available; source-typing evidence is absent. |
| Entry profile for annotated formal `f` | Original formal/Parameter entry plus selected Value(Function) annotation introduction and the source-context obligations for the same instance/scope/xi. The profile's future input/result fields remain dependent and source-owned. | HIR exposes parameter, annotation syntax and a runtime role. Existing Comp-only `RootCompSchema::from_parameter` accepts a narrower schema; it does not form this complete Function entry. | `Instruction::Lambda`, closure and `Frame::Callee`; Value entry currently forces the argument before `ValueEntry` binds the formal. No imported source certificate authorizes this order as the selected Function entry. |
| First execution plan for `c1 = f(Unit)` | Original Name, Unit/Return/Delay, Call/Apply and selected complete invocation constructors. The actual provider/interface and whole carrier stay correlated; challenge formation consumes an independent punctured context. | `CandidateInference` may retain candidate constraints; `prepare` does not export a source derivation. HIR and runtime program retain callee/argument labels and an Apply instruction only. | `Apply` → `Frame::Callee` → closure/operation path. No source-owned provider, complete-call delimiter, or designated consumer node is imported. |
| Second execution plan for `c2 = g(Unit)` | Original ResultBind/Name/Call rules under hypothetical `g:Value(A1)` for context formation, then under the actual same returned binding only after `c1` Return. The same `xi`, scope path and original source instance are retained; this obligation is part of the missing caller-context proof. | HIR contains the local `g` binding and Apply labels. `CandidateInference` is still discarded at `execute`; runtime local lookup stores/retrieves values and views, not the source ResultBind derivation. | `Frame::Local`, later Name/Apply and `Frame::Callee`. No proof establishes that `g` has source `Value(A1)` or that the `c2` provider uses the matching interface. |
| `c1` completed Return and binding at `b_g` | Original two-input source Result/Return introduction at one actual return/world, retaining both tagged packets `W_z` and `F_R,z`, original `mu_z/rho_c` maps, and ResultBind to `b_g`. No packet exists while the call is pending. | Runtime records the returned value/view. `Frame::Local` installs the completed initializer at its actual binding. No source Return map or two-input certificate is produced. | `ReceiverReturn` then `Frame::Local`; an operation may continue through `OperationResultConsumer`. Existing frame sequencing does not import or validate `W_z/F_R,z`, tags, maps or source destination. |
| `c2` Return to enclosing Lambda result | Original body-result Return rule at the Lambda's actual result destination, with the same typed result maps and original scopes/xi. It is distinct from `c1`'s `b_g` ResultBind. | Runtime produces an ordinary returned value/view from the body/root. There is no source `ReturnPlan`. | Enclosing Lambda body/root return path, including `Frame::RootCompReturn` when applicable. It cannot be conflated with `b_g`. |
| Future input/provider action | Original dependent Function input/future constructor and FutureUse, instantiated only at the actual later provider entry. Preserve the actual provider, original antecedents, instance, scope and shared xi. | Saved continuation templates retain frames and `ExecutionView`; the pinned templates carry no callable Entry/Exec/Return recipe. | Later actual provider entry/consumer. A prior receiver or Return cannot be copied onto a hypothetical/future input. |

The source rules provide the *shape of the derivation obligation*, not a
current executable producer. In particular, HIR source occurrence joins do
not establish the semantic `T` fields shown above. `CandidateInference` is a
different result type from an independently valid source derivation; its
current handoff into `execute` is explicitly discarded.

## 3. Identity, staging and validation obligations

If a later producer is established and adopted, every dependent plan node
must retain (not reconstruct) the original source instance identity, scope
path, and shared `xi=(nu,K,D)`; exact source root/occurrence; original
annotation, parameter, binder and result destination; and the actual
provider/interface and typed path maps. Equality of endpoints, printed
Function shape, solver support, runtime tags or a successful matcher cannot
rebuild any of these identities.

The importer must validate exact joins for each node before making a
`RuntimeProgram` visible. Missing, foreign, conflicting, wrong-scope,
wrong-instance, wrong-xi or wrong-destination references fail privately and
publish no partial program/result. Preserve the phase order: source `c1`
challenge before provider acceptance; actual Return before installation of
`g`; `c2` consumes the actual `b_g` binding; and an eventual Lambda Return
uses the original body-result destination. A pending Request carries no
completed Return packet. These obligations are inherited from the reviewed
importer contract, not a new runtime selection in this note.

## 4. Exact missing evidence and next owner

The first source-side missing item is a complete original `T` at the first
Call's source context. The currently selected Unit-arrow constructor requires
an independently satisfying punctured context; the reviewed candidate
`CTX-RESULTBIND-PUNCTURE` still lacks a source ResultBind/context plug theorem
for the open `g(Unit)` suffix. Until the source Context/Bind owner supplies
that theorem or establishes that the context is an external premise, no
source plan producer for this component can be claimed.

Once `T` is available, the source exporter owner must map each constructor
step into the fields above and retain original source instance, scopes,
`xi`, provider interfaces and return maps. The native route still needs a
single anchored full MODEL at original `alpha,A1,E1,xi`; neither `T` nor this
producer contract supplies it.

Before a compiler source lease, the primary still needs: reviewed/adopted
source bridge meanings; an independently valid source producer/exporter; an
architecture decision for representation and lifetime; source-to-plan
erasure/simulation for this component; and a separate bounded implementation
packet with rollback and verification scope. This Draft selects none of
those. Tests, builds, probes, source admission, semantic adoption, and
production remain outside this sprint.
