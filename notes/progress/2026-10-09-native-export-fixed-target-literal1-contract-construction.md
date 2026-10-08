# Fixed pick / bare id: authentic literal-1 contract construction

Date: 2026-10-09
Baseline: `1c0fa21364113efc2a305a42f03eec7ff6c3694f`
Claim class: bounded source-constructor derivation; frozen unreviewed research
Authority change / source counterexample / gate closure: none
Production implementation, tests and builds: none

## Objective and result

Construct the actual ground contract for an immutable integer `1` that can
serve as the argument value in the conditional Return(1) discriminator for
the fixed target `my z=0; my pick ignored=z`. The selected native constructors
construct that ground contract when supplied the actual literal's whole local
relation: use the authentic `Int` literal rule at the `1` occurrence, retain
its provider and whole ground certificate, and apply PE-PICK's
finite-public-import construction to that monomorphic value. The numeral
spelling alone supplies neither the relation nor its provider.

This closes only the literal-contract sub-obligation. It does not construct
the Call-owned `ReifyOrigin`, a complete original carrier at both inlet
telescopes, or a scope-preserving pairing between those two roots. The
conditional Return(1) discriminator therefore remains conditional and is not
a source counterexample to `ALL_VIEW` or a refutation of `Valid_V`.

## Governing constructors

- `notes/theory/2026-10-08-source-directed-joint-decision.md` §3.1 gives the
  finite authentic-ground-literal source fragment and its original `Int`
  endpoint.
- `notes/theory/2026-10-08-projection-public-export-construction.md` §8
  constructs the full public ground contract of an actual immutable literal
  binding, preserving its provider, ground hereditary certificate and fixed
  dependencies. PE-PICK accepts such actual finite public imports and keeps
  their complete free dependency closures monomorphic.
- `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` §§3.1,
  5.1–5.3 require the actual literal's whole local relation and retain fixed
  external/public dependencies; they do not turn a printed value into a
  provider or a Call origin.
- `notes/theory/2026-10-07-call-input-construction-proof.md` §§3.1, 3.4 make
  `Carrier-Delay` consume the original Call's registered `ReifyOrigin` and
  typed incidences. The carrier constructor does not create that origin.
- `notes/theory/2026-10-08-call-semantic-input-realization.md` §4.1 supplies
  ordinary world-independent ground validity and does not remove the need for
  the actual carrier/Call incidence.

## Literal contract derivation

Take one source binding `my one=1` in a compatible immutable world. Apply the
selected authentic ground-literal clause to that exact occurrence. The
occurrence has the ordinary `Int` endpoint; its actual evaluation/publication
creates one immutable provider `p_1`. The independently selected ground
semantics supplies the same-value hereditary certificate at `(1,p_1)` and
retains the original world/slot dependencies. Denote the resulting finite
public contract by

```text
J_1 = (value 1, provider p_1, type Int,
       ground hereditary certificate, original fixed dependencies).
```

This is the PE-PICK §8 literal constructor instantiated at the source value
`1`, with its value/provider fields replaced by the actual occurrence's
`(1,p_1)`. The proof does not freshen the binding or replay its initializer.
Any later use refers to this same installed provider and complete public
contract. This is the producer for the `J_1` literal-publication premise in
the earlier conditional discriminator.

## Exact remaining carrier and pairing obligations

The literal binding can be the source of an argument expression, but that
does not yet form a Call carrier. For an actual Call argument, the selected
constructor chain still needs:

```text
Code(Name(one), ...),
the Call's actual ReifyOrigin(o_arg, ...),
Carrier-Delay(..., o_arg),
the original port map, whole-carrier contract, scope and admission evidence.
```

The Return(1) discriminator needs those original records at the unchanged
`id` and `pick` inlet telescopes, with the required same-carrier/event and
scope pairing. Two separately named calls do not become one paired event by
having the same argument spelling or by sharing `p_1`; each still needs its
own original Call origin and complete dependent incidences. No selected
constructor found in this bounded read creates the missing pairing from
`J_1` alone.

Accordingly the next action is now narrower: construct or locate the authentic
Call/reify records and cross-root pairing for the one installed `p_1`, or
derive an exact independent admission clause that excludes this carrier. Keep
the root-relative map and exhaustive `Valid_V` questions separate.

## Coverage and limits

This is a constructor instantiation from the selected ground literal and
PE-PICK rules, not a compiler run, parser/HIR-to-original-call bridge, or
independent review. No test, build, executable probe or Git mutation was run
while deriving it. The proof remains within the selected native source and
public-import envelope. It claims no universal producer for arbitrary
operations, no same-event Call pairing, no target-domain equality, and no
production F5 behavior.
