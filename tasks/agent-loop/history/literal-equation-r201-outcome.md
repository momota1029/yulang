# R201 outcome — independent literal equation construction

Session: `LIT-EQUATION/R201`; branch `yulang3`; baseline
`295de848bbd0da59a1df4cdf3dd751a0164412be`.
Status: **MODEL-INCOMPLETE; no theorem activation; no parent-premise reduction**.

## Result and parent accounting

The read-only architect assignment constructed a concrete independent
Simple-sub candidate for all eight original literal payload forms and isolated
the first missing law in the original semantic construction. The candidate is
useful as a falsification probe, but it is not adopted source semantics and
does not establish that every independently satisfying assignment derives the
original literal rule.

The unchanged target remains `SourceProblem.InferenceSoundness`,
`Contracts.lean:128–130`. Before and after: **0/4 roots closed; 0/5 dependency
packages closed; zero parent-premise reductions**. No theorem was proved or
applied. Soundness, source coverage, principality, termination, and Rust
correspondence retain their prior status.

## Concrete independent candidate (not semantic adoption)

For each original literal `l`, use eight distinct symbolic base atoms:

```text
B(unit)=unit                 B(bool b)=bool
B(int n)=int                 B(floatBits n)=float
B(string x)=string           B(bytes xs)=bytes
B(path p)=path               B(character c)=character
T(l) := SimpleSub.Term.atom (code(B(l)))
```

At source site `s` and source scope `Γ`, the candidate equations are:

```text
GenerateLiteral(Γ,s,l) :=
  { site := s, literal := l, store := [], outputType := T(l),
    intrinsicEffect := bottom,
    payloadEquation := valueSlot(s)=l,
    scopeReference := Γ.scope, eventReference := Γ.event,
    rootReference := Γ.root(s) }

SolvesLiteral(d,a) :=
  SimpleSub.Store.Satisfied a.types d.store
  ∧ a.value(d.site)=d.literal
  ∧ a.scope(d.site)=a.read(d.scopeReference)
  ∧ a.event(d.site)=a.read(d.eventReference)
  ∧ a.root(d.site)=a.read(d.rootReference)

ReadLiteral(Γ,s,l,a) :=
  ⟨T(l).subst a.types, a.value(s), a.root(s), a.event(s)⟩

GroundCandidate(d,v,r,e) := ∃ l, d=T(l) ∧ v=l
```

This makes the payload equation explicit and has no output variable `α` that
could be solved as `.top`. It preserves arbitrary Nat float bits, arbitrary
byte lists and strings/paths. It uses no `Kernel.atom`, source `Satisfies`,
ground predicate, declaration predicate, or source typing judgment.
The payload equation follows because `d.site=s` and `d.literal=l`; substituting
the solved output atom and payload gives the candidate `GroundCandidate` fact.
No Lean check was run and no original ground fact follows from this candidate
definition.

## Exact remaining equations and owners

The first unresolved equation is the all-payload original primitive
declaration/ground realization:

```text
SolvesLiteral(GenerateLiteral(Γ,s,l),a)
→ OriginalLiteralDeclaration(l, ReadLiteral(Γ,s,l,a))
  ∧ OriginalValueForm(T(l)) = ground
  ∧ OriginalGround(ReadLiteral(Γ,s,l,a)).
```

The selected authority does not derive it. Its owner is the selected
Source-Generalize construction's L1 obligation: an actual primitive
declaration and complete typed relation. The pinned sources are:

- construction: `notes/theory/2026-10-08-source-generalize-definition-and-proof.md:77–80,137`, SHA-256
  `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`;
- selection authority: `notes/design/2026-10-08-source-generalize-definition.md:§§2–3`, SHA-256
  `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`.

The original Return rule is a subsequent independent obligation. The pinned
`OriginalSourceInterpretation.lean:680–690` requires all of:

```text
traceForm(returned) = pureReturn(row)
eventCoherent(returned.event)
observationGuards(returned).Valid
Meaning(world(returned.event))
row.event = returned.event ∧ Meaning(value(row))
observationFields(returned).Holds(Meaning)
```

A syntactic Return node or candidate intrinsic `bottom` does not establish
event coherence, valid guards, world meaning, or observation fields. The
contextual effect premise also remains separate: policy
`a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` keeps
intrinsic contribution distinct from contextual inflow, permission, and
residual variables. These laws cannot be filled by paper literal typing or
the selected effect policy alone.

Even after authentic descriptor formation and ground membership are supplied,
`OriginalSourceInterpretation.GroundLaw.hereditary` at `:805–807` remains
needed to establish recursive `Meaning` for the ground row; this is the
explicit premise consumed by `ground_membership` at `:809–826`. It is another
original primitive law, not a consequence of the candidate payload equation.

No competing accepted original meaning was established, so this is an exact
construction stop, not a semantic-under-specification finding or a request
for a semantic vote. The next construction needs the authentic complete
literal primitive clause at the original indices, then its Return and
contextual-effect realization on the same assignment, occurrence, scope and
event.

### Primary L1 identification check

The primary checked whether `GroundCandidate` is already identified by the
selected original law. The type-safety specification says a literal has its
corresponding single base type (`docs/yulang-operational-type-safety-ja.tex:212–216`),
so it supports the source-level base-type distinction used by the candidate.
The source typing rules also say `Lit` has its declared literal type and is
returned with `Ret` (`docs/yulang-source-type-safety-ja.tex:278`); the unified
semantics says the declared type anchors the result and construction is pure
(`docs/yulang-whole-language-semantics-ja.tex:524`). These manuscripts sketch
the source-level literal type, Return shape, and construction-effect
requirements. The source-type-safety and whole-language documents identify
themselves as standalone research manuscripts, so these statements do not
select an approved instantiation of the original interpretation. They also do
not state an equation from that base type into this formal model's
`Sorts.Descriptor`, `Inputs.valueForm`, `Inputs.ground`, or
`LiteralDeclaration` relation.

The selected Source-Generalize authority makes that boundary explicit:
construction §3.1 requires the literal's actual declaration and whole local
typed relation, while L1 requires each authentic primitive's independently
fixed typed relation and full local laws. The selected definition
`notes/design/2026-10-08-source-generalize-definition.md:§§2–3` does not itself
fix foreign primitive meanings. In the formal interpretation,
`OriginalSourceInterpretation.lean:316–330` leaves the original input
relations as fields; `:837–850` consumes `LiteralDeclaration` and original
ground facts as supplied premises. None equates them to the candidate rows.

Therefore the exact identification still missing is:

```text
for every original literal l and lawful same-site assignment a,
  descriptor(a, site) = originalBaseDescriptor(l)
  ∧ value(a, site) = originalPayload(l)
  → LiteralDeclaration(l, row(a, site))
    ∧ Inputs.valueForm(descriptor(a, site)) = ground
    ∧ Inputs.ground(row(a, site)).
```

The first conjunct about corresponding base types is present at the
source-typing level; the complete row equation and its identification with
the opaque original declaration/ground relations are not. Treating the
candidate relation as that original relation would be a new semantic
identification, not a derivation from the selected L1 authority. The primary
therefore retains **BLOCKED_AT_L1_IDENTIFICATION**. No new worker, theorem,
source restriction, or semantic choice follows from this audit.

## Authentication, review, and boundaries

The worker verified the R201 frozen input hashes, including:

```text
candidate       f60b89d98ced17cabf860c6dd65aa3929796c85a407c8f82af25607adf0017cb
R200 outcome    7b7a3fc1d1a4960ed78dee5befdf9c305d0a02b70091243d4b59995838aec337
interpretation  feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef
```

The worker assignment was read-only, one architect, at most 900 seconds, no
descendants or path lease. It performed no Lean/Lake, build, test, Rust/native
read, environment/cache/target/scratch operation, or file write. The primary
has not run Lean/build/tests for this outcome. Fresh independent review passed
the outcome at SHA-256
`fb54ca75c4b34d68bd80d9d079640caa0f82f5a60a98f389ea136b75cb6a632a`; the
candidate remains MODEL-INCOMPLETE and no theorem activation is allowed.

At the end-of-sprint boundary, `next_action_selector` recommended Luna own
the exact L1 identification, with no new worker: derive it from selected
authority if already fixed, otherwise retain `BLOCKED_AT_L1_IDENTIFICATION`.
The bounded primary check above found only corroborating standalone manuscript
statements, not an approved instantiation of the formal original relations,
and therefore retains that stop. No third constructor or wrapper packet is
admitted on the unchanged premise.

The primary-owned record preserves all pre-existing dirty/untracked paths,
UNKNOWN worker observations and quarantined leases, including the pending
typed-Union bundle. The only intended R201 source-state update is this outcome
record and the exact current-sprint/worker accounting; no Rust path was read
or changed.
