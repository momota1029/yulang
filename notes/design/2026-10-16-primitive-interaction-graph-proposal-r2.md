# Primitive interaction graph proposal — revision 2

**A2-R1 complete revised Draft — proposal only**

This replaces the A2 proposal for review. The supplied original snapshot `d7485706cc998aa4bf4bcdaaa925cef2e2348c92984a77bb99e4a5922b6c68af` remains unchanged. No adoption, implementation or parent-gate closure is claimed.

Settings: requested responsibility is read-only architecture repair. The advertised architect configuration is `gpt-6.1-sol`/medium; observed runtime role, model and effort remain **unknown**.

## Ownership and fixed contract

The §3.7 primitive-design owner owns compiler-created Z alternatives. Source owners retain source-R semantics; foreign owners retain their exact relations. The original telescope, binders, `xi=(ν,K,D)`, admitted challenges, actual providers, live configurations, shared witnesses, future dependencies, H and U remain fixed.

Reuse E1-R2’s D2 result: the Z body and dependent declaration were unselected. Neither source-operation expansion nor §5.3 supplies that declaration.

The proposed Z policy remains: independently licensed, typed interaction-rule graphs may provide observations without source anchors, subject to the original complete G. They do not acquire permission through U membership or query success.

## Declaration and evidence grammar

The extension is placed inside the original telescope, without moving its binders:

```
Γoriginal;
original declaration, substitution θ, scope/origin and phase references;
xi; actual provider and complete Call interface;
original admitted whole challenge, carrier, live C and history;
fixed foreign environment F; complete envelope G;
finite typed graph L;
whole observation y, including actual provider/future indices;
finite evidence w : MemberL(original dependent operands; y).
```

`Γoriginal` is retained verbatim. **Unverified:** this is not a reconstructed exhaustive declaration of the unavailable full `Tα`.

```
P ::= Return(v)
    | Request(q,[r,Cnow,η].P)
    | Bind(P,[v,Cnow,η].P)
    | P ∪ P
    | P ∧ P
    | exists x:T(original dependencies).P
    | Prefix(original pending observation)
    | FixedForeign(f, original whole operands)
    | Ref(ℓ, original dependent arguments)
```

Positive registered equations and finite derivations interpret the graph. `FixedForeign` retains its exact complete and prefix relations. Returned values retain their actual fixed future interfaces.

```
Zα(y,w) := w is a licensed typed graph derivation producing y.
X(y) := G(y) ∧
        (R(y) ∨ Zα(y,w) ∨ ∃x,z. X(x) ∧ W(x,y,z)).
```

This selects a candidate abstraction policy, not existing production meaning. Admission preservation, exhaustive original-alternative coverage and acceptable conservatism remain unproved. W remains present and requires its own unchanged-contract action.

## Repair 1: finite code with explicit continuation parameters

The former `(node, handler phase)` identity was insufficient. Replace it with **parameterized equations**, not additional memo-key components:

```
Runℓ :
  (e : Envℓ) →
  (C : Current(e)) →
  (κ : Kont(Resultℓ(e), BoundaryResult, original scopes)) →
  Head(BoundaryResult)

Imageℓ,H :
  Envℓ → Current → Kont → OriginalJointContext → ImageObservation
```

`Envℓ` is the dependent environment of the node’s free original operands. Continuations use finitely many frame constructors:

```
κ ::= End
    | BindFrame_b(saved dependent environment, κ)
    | OriginalFrame_f(saved dependent environment, κ)
```

There is one `BindFrame_b` constructor per static Bind site. `OriginalFrame_f` retains existing consumer, owner and phase frames. A raw continuation contains a code reference, dependent environment and the **entire** pending continuation:

```
raw = Raw(ℓk, ek, κsaved, original packet/response dependencies)

Resume(raw,r,Cnow,η,κarm)
  = Runℓk(ek extended by the same r,η,
          Cnow,
          append(κsaved,κarm))
```

`append` is a fixed, typed continuation operation:

```
append(End,κ) = κ
append(Frame(e,κ1),κ2) = Frame(e,append(κ1,κ2)).
```

It preserves frame order and delimiters; it does not simplify away original frames. Environments retain typed references, not store snapshots. Resumption receives the live `Cnow`.

The relevant execution rules are:

```
Run(Bind(P,b),e,C,κ)
    → Run(P,e,C,BindFrame_b(e,κ))

Run(Return(v),e,C,BindFrame_b(eb,κ))
    → Run(body_b,eb extended by v and original evidence,C,κ)

Run(Ref ℓ(args),e,C,κ)
    → Runℓ(args(e),C,κ)

Run(Request(q,k),e,C,κ)
    → Yield(q,C,Raw(k,e,κ)).
```

The handler dispatches on the resulting head. Selection and arms execute outside the selected activation. Raw resume calls `Run`, not `ImageH`.

**Finite-construction invariant.** For every reachable configuration, the explicit continuation denotes exactly the ordered pending suffix of the original graph execution, with each frame’s original dependent environment.

Proof for the declared rules is by induction on finite execution steps: Bind pushes precisely its pending suffix; Return executes precisely the top suffix; Ref changes code/environment while retaining the continuation; Request packages that unchanged continuation. Typed frame formation and application retain binder dependencies. No step substitutes an independently chosen world, witness or provider.

Compilation emits finitely many equations and frame tags from the finite graph and handler. Recursive references pass dynamic environments and continuations as arguments. Their contents never enter a specialization/memo key. Consequently unbounded recursive suffix depth does not create unbounded generated code.

This is a **finite representation**, not a finite-state machine or a runtime-resource bound.

Examples:

- **Abort:** handling `Bind(Request(q,k),b)` captures `k` followed by `b`. An arm that returns without resuming executes neither.
- **Resume:** the same arm’s resume executes `k`, then `b`, outside H, in the supplied live state. Any request in `b` remains outside H.
- **Recursive pending suffix:** for `L = Return(v) ∪ Bind(Ref L,b)`, selecting the recursive alternative n times builds n dynamic `BindFrame_b` frames. One `RunL` equation represents every n. Subsequent abort/resume preserves that exact stack.
- **Recursion without return:** `L = Bind(Ref L,b)` continually accumulates frames. None executes without an inner Return. The compiler emits no invented terminal event.

**Remaining gap:** independent verification must cover the complete original frame inventory, legal environment transport and every fixed foreign transition. The induction above establishes the stated candidate-rule invariant only.

## Repair 2: conjunction retains one common preimage

Do not intersect separately transformed images.

Conjunction membership uses one original whole tuple:

```
Member(P ∧ Q, y; wP,wQ)
    iff Member(P,y;wP) ∧ Member(Q,y;wQ).
```

Its image rule is:

```
Member(P,y;wP)   Member(Q,y;wQ)
one operational handler derivation d from that same y to o
----------------------------------------------------------
Image(P ∧ Q,H,o; y,wP,wQ,d)
```

Here `d` is generated by the concrete dispatch/resume/forward rules, not supplied as an assertion that `o ∈ U`.

The finite construction introduces a shared-preimage relation node:

```
JoinP,Q(original environments; y; wP,wQ)
```

Both membership evaluators use that same `y`, original binder environment and joint history. Handler dispatch runs once. If resumption extends an observed history, both premises must support that same extension under the original dependent response binder. No new preimage witness is selected for the second premise or later resume.

`Join` retains each evaluator’s dynamic continuation separately; it does not combine their independent outputs. A failed joint premise yields no conjunction observation. It does not trigger fallback to a successful marginal.

**Preservation argument.** A generated image contains a common-y witness and both membership derivations, so it is an image of an actual conjunction member. Conversely, any conjunction member has those two derivations at the same y; applying the same handler derivation constructs its image. This is the relational existential-image law with the common witness retained. It does not assert that image commutes with intersection.

**Remaining gap:** this rule does not provide a terminating algorithm for discovering every shared preimage, comparing arbitrary future relations, or evaluating opaque foreign predicates. Such problems remain open; `Join` is not an inclusion oracle.

## Repair 3: explicit finite-prefix observations

Use distinct observations:

```
Pending(original root/phase, current C, original history,
        retained dependent continuation/future references)

Return(v,C,actual Future(v))

Request(q,C,exact raw continuation)
```

Finite interaction histories may extend a Request by an original admitted joint response `(r,Cnow,η)`. Every extension retains that response’s actual provider and future interface.

`Pending` states that observation stopped at an admitted prefix. It asserts neither eventual completion nor divergence.

Prefix introduction is explicit:

1. A compiler-owned `Prefix` clause emits its declared pending observation under its original license, admission and G premises.
2. Existing source and foreign prefix clauses are reused exactly; there is no blanket prefix rule for an arbitrary foreign relation.
3. An actual internal transition transports a prefix of its successor back through the same pending frames.
4. Return requires a terminal Return rule. Request requires an actual Request rule. Neither follows from `Pending`.
5. Bind lifts a pending inner prefix with its continuation still suspended.
6. Ref uses the registered equation’s rules, preserving environment and continuation. A cyclic proof reference alone introduces nothing.

Therefore:

```
L = Ref L
```

with **no base rule in either observation sort** has no finite derivation. It produces neither Return, Request nor Pending.

An intended prefix-bearing loop must explicitly retain its prefix clause:

```
L = Prefix(pending at L) ∪ Ref L.
```

It then has pending observations but no fabricated Return or Request. Source loops retain their original prefix rules; this proposal does not replace them with the baseless equation.

Under H, Pending remains pending, with the handler execution and exact suffix retained. It does not invoke H’s value arm. A Request may legitimately cause an aborting arm to return without its raw continuation completing; that Return is derived from the arm. Resumption extends the same original history and continuation outside H.

**Preservation argument.** Induction on finite prefix derivations maps each explicit prefix introduction and each intervening machine transition to the corresponding suspended image configuration. Bind and Ref preserve their continuation parameters. Only actual Return/Request rules introduce those observations. The reverse construction erases administrative continuation steps while retaining the same original prefix evidence.

**Remaining gap:** correspondence between these explicit Z prefix clauses and the original complete prefix contract requires review. An omitted source or foreign prefix is a coverage failure, not permission to change that contract.

## Exact U and gate boundaries

The generated image remains at the original indices and exact U. §5.3 can check finite structural comparison proofs, with full alternative accounting, original binders and actual same-provider coverage premises.

Unmatched foreign clauses, missing shared-preimage evidence or insufficient U proofs remain unresolved. Retaining those residuals does **not** discharge the original A/B target.

Before implementation, independently establish:

- full original telescope and alternative coverage;
- admission preservation and lawful Z licensing;
- complete continuation/environment and prefix correspondence;
- exact image preservation, including correlated conjunction;
- effective exact-U discharge under the unchanged A/B quantifiers.

Required reviewers: `compiler_referee` for the three semantic repairs and `spec_auditor` for scope, fixed contracts and original-domain preservation. Luna assigns review after dispatcher consultation.

User approval remains necessary for the concrete Z grammar/policy, explicit prefix policy and any resulting native architecture. No approval is requested or presumed here.

Rollback condition: reject this Draft if preserving an original alternative requires changing a fixed foreign relation, provider/future contract, admission domain, H or U. Preserve all existing authority and OPEN parents.

Later focused checks should exercise the three examples above, shared-preimage counterexamples, baseless recursive references, prefix-only loops and unchanged foreign prefixes. Measure generated equations/frame tags separately from dynamic stack depth and comparison work. None were run.

## Scope and inspected evidence

This repair reread:

- `notes/design/2026-10-05-source-contracts-and-common-allowance.md` §§2, 3.7, 5.3.
- `notes/theory/2026-10-16-operation-primitive-image-contract-construction.md` §§4–5.
- `notes/theory/2026-10-16-original-primitive-image-decisive-construction.md` D0–D2.

The original A2 authority reads remain applicable. No files, snapshot, board or inbox were changed.

**Stop condition reached:** all three clauses now have explicit candidate rules and bounded construction arguments. Their full original-contract correspondence and total exact-U discharge remain unproved. All original A/B, correspondence, implementation and production gates remain OPEN.

