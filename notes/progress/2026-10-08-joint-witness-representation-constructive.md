# Native id joint witnesses: a relative finite-code construction

Date: 2026-10-08
Status: reviewed conditional derivation; JOINT_DEC remains OPEN-PROOF
Gate: JOINT_DEC remains OPEN-PROOF
Implementation authority: none
Baseline: `2e2adc88e93d3aadd8079e764d58e25af786019b`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file only

## Objective and exact source boundary

Attempt an actual finite-data representation of native `my id x=x` joint
witnesses. The result is a concrete **relative code transport**: native source
and public witnesses can use the same finite code for every retained input
and proof-choice coordinate. This removes an additional encoding obligation
at native export, conditional on the argument-side strategy already having
an effective code. It does not construct that input code or decide the
remaining residual. This is not another finite residual-state quotient.

Exact governing sections:

- `2026-10-08-uniform-value-entry-constructor.md` §§4.1–4.3:
  Parameter-owned schema, the eight gamma fields, original constraint
  telescopes and the finite local derivation grammar; §§5.2,6: unchanged sum
  injection and Joint-ID's explicitly supplied joint strategy.
- `2026-10-08-projection-public-export-construction.md` §§2–5:
  source formation, finite slot schema, extraction and exact raw-alias maps;
  §7: source-lawful completeness for a fixed finite client grammar **and a
  supplied original strategy**, preserving all nondefinitional choices.
- `2026-10-08-native-projection-public-export-definition.md` §§1–4:
  selected native meanings and production extras. No foreign/fixed constructor
  is reinterpreted.
- `2026-10-08-id-inlet-whole-output-image-owner-cut.md`, “Exact source
  predicate and original telescope”, “Constructed local law” and “Effective
  decision cut”: the local whole-image action is already constructed; its
  complete J/Car/context/strategy inputs are not constructed or decided.
- `2026-10-08-joint-dec-constructive-attempt.md` §§1–3.1: EPR truth equivalence
  and the additional ER extraction premise are accepted conditional results.
  Neither is assumed to hold for Yulang in this attempt.
- `successor-proof-obligations.md`, JOINT-DEC: every original active predicate,
  exact admitted envelope and simultaneous original-witness completeness.
- `2026-10-03-open-residual-factorization.md` §§2–4: original Guard/Phi,
  K,D and witness identity remain joint after structural normalization.
- `rules/compiler-engineering.md`, “Natural compiler behavior and
  proof-obligation economy”: A/B/C/D classification and owning evidence.

The arbitrary original residual R and its binder tree are inputs, not a new
language. No predicate is replaced by a local proof tag, and no quantifier is
moved. One finite client grammar is considered; histories and independently
admitted future developments have no sampled depth bound.

## 1. The actual code constructor

Let S be the original finite typed slot/telescope map for the client grammar.
Construct a table of records `(slot identity, sort, original owner, dependency
list, binder position)`. Slot references refer to this supplied owning table;
their spelling or numerical identity establishes no new ownership fact.
Every original coordinate, including shared xi=(nu,K,D), remains present.

Use the following finite term-DAG syntax, with the original independently
justified rule signatures as its constructor signature:

```text
Slot(s)                         original input/choice coordinate from S
Record(tag, labelled children)   full native dependent record
Project(label, term)             elimination of that same record
Rule(rule, operands, premises)   full local proof term, not a law name alone
At(original binder, body)       unchanged original dependency telescope
Cases(original constructor, arms) complete original constructor alternatives
Graph(original equation, refs)  supplied finite certified equation graph
```

`Slot(s)` is a variable/reference, not an implementation of its semantic value.
A closed effective instance must supply codes for those values or a specified
symbolic producer with an independent interpretation. An unexplained pointer
to an arbitrary semantic strategy is not a closed effective code.

Encode an already finite submitted local proof or record by traversing its
syntax, retaining every labelled field, original rule, intermediate and
dependency reference. Sharing uses explicit graph references. The graph form
is allowed only with the original complete equation rule and its conditions;
it is not permission to introduce arbitrary recursive executable programs.
The constructor never normalizes proofs by associativity, equality of their
conclusions, or a canonical Identity choice. Thus independently chosen
Identity and Compose terms keep their original distinct syntax/evidence.

For gamma the concrete node is:

```text
Record(CheckedInlet,
  J, kappa_J, carrier_J, mu_result, original_port_map,
  delta_static, delta_check, current_guards)
```

Those are the same original slots or their supplied finite codes. Emit actual
admission as

```text
Rule(PackGeneric,
  [Slot(kappa), gamma, Slot(IF0)], original required premises)
```

This is introduction into the already fixed sum; it does not choose another
A/Delta, change J or assert GenericValueInlet=I_q[A;Delta]. The whole-image
proof code uses `delta_check` elimination at its existing observation/event
binder and applies `mu_result` only in a completed Return arm. Pending/Request
arms keep the original handle, operation, current world and suffix fields.
Future arms refer to their original hereditary subtree. `Cases` is the finite
original constructor schema, not an enumeration of observations or executions.
Every licensed production alternative remains in the interpreted image.

At the four native source positions, emit the corresponding global ordinary
certificate record with **the same retained proof operands**. Substitution
eliminates only the forced raw alias equations `z=t`. Keep the total graph
`z -> t` for inverse reconstruction. For every original R occurrence of z,
substitute t simultaneously, including proof-dependent and shared occurrences.
Do not substitute worlds, ports or body/output proof objects merely because
the raw value/provider is the same. The inverse adds the same forced raw alias
coordinates and owning records; it copies every retained proof term.

Construction terminates on the finite input syntax and slot map. With explicit
sharing, it adds O(1) native schema nodes per real frame and O(|S|+|Delta|)
table/substitution entries, in addition to the supplied proof code. This is a
bound on **wrapper size**; there is no bound here on J/Car/strategy code size.
It neither enumerates arbitrary histories nor executes any recursive proof
program. Scope checking uses the supplied original dependency lists.

## 2. Relative representation theorem and derivation

**Claim class: conditional theorem, unreviewed.** Suppose:

1. A code interpretation for the original input slots represents their exact
   semantic J, Car, context and complete joint strategy, including every
   observed nondefinitional proof choice. It has effective prefix supply/replay
   on every independently legal challenge, retaining the actual prior prefix.
2. The native/local constructor signatures and their whole-tuple laws are the
   selected independently justified ones. Finite graph nodes carry the
   original equation certificates. Constructor recognition alone does not
   establish semantic validity of an external law.
3. All additional retained proof values supplied to the transformation have
   codes in that same interface. R is interpreted on its unchanged original
   tuple and binder tree; it need not have any restricted observer grammar.

Then the constructor above transports the represented original joint strategy
to the native public strategy, and its inverse reconstructs the represented
source strategy. For every original prefix and every complete observation,
the retained semantic tuple is unchanged, with exactly the forced raw aliases
substituted/restored. Every original R therefore has preservation and reflection
on these represented fibers. Effective input replay implies effective replay
of the transported strategy without an additional native-id classifier.

**Derivation.** Induct on the finite source/client constructor grammar, carrying
the *same* original prefix and code environment as the induction parameter.

- At an input/choice slot both transports copy its reference and interpretation.
  This includes J/Car, actual current-world fields and intermediate proofs.
- At a local certificate record the source/public expansions have the same
  retained labelled children. Encoding and reconstruction are fieldwise;
  `Project` followed by that record constructor changes no child interpretation.
- At a forced raw alias, its source equation fixes z to t. Forward simultaneous
  substitution and backward insertion give that same z for every original
  interpretation. Arbitrary R is preserved by equality substitution, without
  an oracle or decision procedure for R.
- At `At`, both directions retain the original binder and preceding
  environment. An existential output at this position depends only on those
  preceding original slots. After a universal challenge, use hypothesis 1's
  same-prefix replay and apply the code transport to the extended environment.
  No earlier choice is reselected. A ViewLogic slot remains above its challenges;
  an EventProof slot remains at its event.
- At constructor alternatives use every original arm. At pending prefixes
  restore no completed value. A later response/raw/future extension uses its
  original subtree and unfinished suffix; no receipt or completed prefix is
  replayed. Certified finite graph references keep their original local law.
- At alias/join/new client positions follow the original slot identities:
  aliases reuse their frame, new frames get only their licensed copies, and
  joins use one common environment. There is no marginal-witness amalgamation.

The same induction proves prefix-level replay closure. Native operations on
codes are finite record/reference construction; no semantic classification of
J observations is needed beyond the supplied original constructor tags and
input interpretation. F followed by G restores forced aliases and all original
retained semantic coordinates. This is semantic identity of those tuples,
not a new assertion that arbitrary proof evidence is irrelevant.

The admission/image code explicitly exhibits a finite producer, whereas the
source/public transport preserves whatever original choices were supplied.
Replacing those choices by this particular producer would prove only a
restricted subfamily. It would invalidate the theorem for an R that observes
another lawful choice. The code construction makes no such replacement.

## 3. Where the attempted closed representation stops

The construction yields a finite **open** term over the input slots. There are
two possible ways to close it, and the inspected constructors justify neither
for the whole JOINT_DEC envelope:

1. Keep semantic J/Car/context/strategy values behind opaque slot handles.
   Interpretation preserves identity, but effective challenge supply, residual
   evaluation and strategy replay then depend on those external operations.
   This is a parameterized representation, not an effective solver from the
   original finite source input.
2. Replace every handle by a finite closed term in the original independent
   constructor grammar. This gives an actual finite-data candidate family,
   but requires a **joint argument-certificate representation law**:

   > Every successful original residual in this native-id cone has a complete
   > original-scope winning input strategy represented by finite typed
   > constructor/proof code, with total symbolic handling of every independent
   > legal challenge and faithful reconstruction of the original retained
   > choices read by that residual.

   This is a candidate hypothesis, not an established source rule. It is a
   law about whole argument-check strategies, not just finite individual
   `mu_result` or `delta_check` derivations at already supplied challenges.

The exact unsupplied coordinates are visible in gamma: `J`, `kappa_J`,
`carrier_J`, `current_guards`, and the joint strategy supplying these and their
nondefinitional checks at the original dependent scopes. The native constructor
copies them; it does not reduce them to finitely many grounded values. Finite
Parameter/slot schemas describe the *positions* of these values. They do not
encode every possible value or producer filling the positions. Joint-ID and
PE-ID start with the relevant original strategy, so using either theorem to
manufacture this closure law would reuse its input as its conclusion.

Even if that representation law were proved, it would supply finite witnesses,
not a computable bound or exact rejection. Enumerating all finite code lengths
would at best supply a positive recognizer **if** original leaf validity and
whole-strategy checking were independently decidable. A finite proof grammar
has unbounded terms, and finite term shape alone does not decide hereditary
Car/context validity or arbitrary R. A terminating JOINT_DEC route still needs
an owner-derived joint residual cell decision/refutation law or a computable
complete candidate bound. No such law is inferred here.

This isolates a premise more narrowly than a new all-world quotient: the
native id wrapper adds no new input-strategy representation obstruction.
The missing representation law is at **typed argument/Call checking and the
independent J/Car/hereditary-context formation supplying gamma**, together with
joint solving of their original Guard/Phi/client predicates. Parameter/Lambda
formation owns the finite receiving schema; Generalize/export owns transport.
Neither later phase originally knows a winning arbitrary argument strategy.

## 4. Economy classification, evidence and limitations

Under compiler-engineering's classification:

- **D:** reconstructing the gamma ownership, scope, provider, incidence or
  existing finite local derivation after discarding it. Retain the complete
  original typed output of argument checking. The code table above consumes
  that output and adds no second semantic authority.
- **A:** soundness of accepted codes and preservation of original scope,
  simultaneous identity and whole-image laws. The relative derivation addresses
  native transport conditionally; its input formation laws remain independent.
- **B:** finding the ordinary jointly admissible input/check strategy needed
  for natural inference, with exact terminating residual decision where the
  production contract requires it. Existing JOINT_DEC remains required before
  cutover. Retention alone cannot find an unknown strategy.
- **C:** demanding a code for every arbitrary semantic strategy, even when no
  active original observer needs it. This stronger universal encoding is not
  established or silently substituted for the required satisfiable-cell
  completeness. This classification retires no existing gate.

This was one manual derivation, not an executable probe or counterexample
search. There is no sampled domain, seed, mutation or numeric history range.
No builds or tests were run. Initial broad read captures were truncated;
focused source slices above were subsequently read. An exhaustive inventory
of source primitives was not attempted.

There is no independent executable oracle. The derivation reuses selected
native local laws and the accepted exact alias maps. A term checker using
those signatures would check finite code structure, not establish its source
laws, complete input coverage, or residual decision. Independent validation
must examine the original J/Car/context definitions and their whole-telescope
interpretation, rather than a second implementation of these same assumptions.

Failure conditions: a retained coordinate is omitted/canonicalized; a binder
or shared frame changes; an input challenge has no effective code/replay; a
local law is merely named rather than justified; a graph has no original
complete equation certificate; a licensed production arm is filtered; or an
arbitrary R is evaluated by an assumed oracle. The first two also invalidate
exact native transport; the others expose failures of the proposed closed
effective-input interface. No failure licenses source rejection or changed
language meaning.

Resource usage: lightweight read/write shell/tool calls only, no executable
experiment, heavyweight process, network, build cache or additional output.
Aggregate CPU, peak RSS and elapsed wall time were not instrumented. The
assignment's one manual derivation allowance was used once.

Unverified scope: existence/completeness of finite input strategy codes;
effective independent hereditary/recursive input laws; original residual cell
decision or rejection; all-language/foreign/State cases; production compiler
correspondence. No JOINT_DEC closure or independent review is claimed.

Recommended next action: audit the argument-check owner's retained gamma and
strategy output against the displayed closed-code premise, starting with
`carrier_J` and current hereditary context replay. Determine whether that
output contains an effective producer or only semantic evidence before
leasing another quotient/probe. Keep arbitrary original R unchanged.

## Frozen dependencies and commit packet

Initial dependency hashes below matched the baseline; final revalidation is
recorded in the producer report. No dependency edit is authorized by this lease.

| Direct dependency | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `5788a2ef1c2181b43a9f82116fe6c4cfd32419dc7098fb84fa7c0d46a0a88ca6` |
| `rules/design-authority.md` | `925f1c5cd4ca6ce7306b1375eb9c1a699a83d3491efba21b50271e176eee5ba5` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `rules/compiler-engineering.md` | `1ff144d376052d2e01d2e97ba3290e6942f126765067fbf11dfeffc06f89b442` |
| `notes/progress/2026-10-08-joint-dec-constructive-attempt.md` | `dbf98d3a6dbbd55c79289f5bb43dd3edf2fea76287f1203c83a4876d5a820977` |
| `notes/progress/2026-10-08-id-inlet-whole-output-image-owner-cut.md` | `b9a6f724fc574a580d14ac31dcaca41fcc5347b50b6ecccf7976f15a102050e5` |
| `notes/theory/successor-proof-obligations.md` | `59442db205d0bc381de74a373f1d58a753e3366ae0ba845e8c9c877465e738fc` |
| `notes/design/2026-10-03-open-residual-factorization.md` | `02e6e04d1a4eea405442587206e34c653b45405677d653e6bfec37568fee4f43` |
| `notes/theory/2026-10-08-uniform-value-entry-constructor.md` | `273e8dae447e9997d586fc07abf48883c76b90988c8906094dd428a48339c2e5` |
| `notes/theory/2026-10-08-projection-public-export-construction.md` | `4cf84e7a38153b893f1d339780598e2b79084c747ecb883acf0e4fdaa49cf631` |
| `notes/design/2026-10-08-native-projection-public-export-definition.md` | `aed6ef63b01f555a5f2804f87a599167c1a30fa999afc0b9d9f11b8ae974a919` |

- Exact leased path: `notes/progress/2026-10-08-joint-witness-representation-constructive.md`.
- Baseline SHA: `2e2adc88e93d3aadd8079e764d58e25af786019b`.
- Dependency hashes changed: none at initial comparison; final report confirms.
- Review status: unreviewed conditional research derivation; producer freeze.
- Checks already run: baseline/branch, dependency SHA-256 and baseline path
  equality; manual derivation/source-scope inspection. No builds/tests/probes.
- Proposed checkpoint message: `research: construct relative native id witness codes`.
- Shared-record deltas left to primary/curator: record the relative code
  transport and argument-owner representation/decision cuts; preserve every
  aggregate gate status. No task/index/authority/question-board edit.
