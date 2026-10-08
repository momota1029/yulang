# Native checked-J witnesses: a conditional prefix-quotient counterexample

Date: 2026-10-08
Status: unreviewed research; conditional mutation counterexample
Baseline: `2e2adc88e93d3aadd8079e764d58e25af786019b`
Branch: `research/simple-sub-intrusion`
Lease: this file only; frozen on submission
Gate: JOINT_DEC; no status change or implementation authority

## Objective and selected method

Attack the actual proposed step in the constructive attempt §3: refine
structural/context candidates by active predicate truth vectors and use those
vectors as residual states. The specific mutation tested here erases the
prechosen inlet description from a prefix before a challenge introduces J,
and uses the union of concrete successor signatures of the merged prefixes.
An unresolved below-challenge predicate receives the same unresolved marker
at both prefixes. This is a candidate mutation of that proposal, not an
encoding already specified or claimed correct by the selected native rules.

The method is a hand derivation of a smallest prefix-extension failure. It
uses finite, computable ground descriptions and an ordinary structural
observer. It does not test pairwise amalgamation, construct an uncomputable
classifier, or dispute the reviewed EPR/ER conditional theorem.

Governing sections:

- `2026-10-08-joint-dec-constructive-attempt.md` §§1–3: EPR clause 3 is
  prefix-local backward extension; clause 4 retains every original leaf.
- `2026-10-08-id-inlet-whole-output-image-owner-cut.md`, Exact source predicate
  and original telescope, Constructed local law and conditional prefix lift,
  Effective decision cut: complete gamma/J and the supplied joint strategy
  remain inputs, not choices reconstructed from scalar payload observations.
- `2026-10-08-uniform-value-entry-constructor.md` §§4.1–4.3,5.2,6:
  A is chosen before h; gamma contains an independently justified same-value
  result inclusion; generic admission injects that exact gamma. Joint-ID
  preserves the existing strategy and every non-definitional proof choice.
- `successor-proof-obligations.md`, JOINT-DEC: original joint predicates,
  preservation, reflection and simultaneous original-witness completeness.
- `2026-10-03-open-residual-factorization.md` §§2–3,5–7: original Eq/Phi
  operands and shared witness identities survive structural normalization.
- `2026-10-07-successor-global-synthesis.md` §§2.1–2.3: original binder tree
  and independent source atoms; source generation is a separate requirement.

The previously reviewed payload/production and proof-choice countermodels
are not reused as this witness. No complete carrier alternative or proof
choice is removed. No source clause, inlet meaning, or binder order changes.

## Hypotheses and exact claim class

The following hypotheses are explicit; H3 is not established for bare id.

**H1 (independent ground and constructor laws).** Independently supplied Unit
and Bool ground contracts have disjoint same-value membership, and the
original structural inclusion grammar admits no `Unit <: Bool` derivation.
The lawful pure Unit and Bool carriers/context certificates used in uniform
inlet §6's two-frame instance exist. Their full guards, incidences, formation
records, hereditary certificates and registered local laws are genuine.

**H2 (native checked admission).** For a fixed description A at its original
sigma, every admitted h carries its complete original

```text
gamma = (J, kappa_J, carrier_J, mu_result, original_port_map,
         delta_static, delta_check, current_guards).
```

In particular `mu_result` is the independently justified same-decorated-value
inclusion `J.payload -> A` from §4.2. It is not a conversion, an alternative
generic-sum index, or a later replacement of A. All operands include the
original `C,q,sigma,xi=(nu,K,D),Delta,IF`, carrier/provider, live event/world,
scope/lifetime, ports and response/raw/future telescopes when applicable.

**H3 (retained original observer).** The actual residual being encoded has
an original structural leaf

```text
P(C,q,sigma,xi,A,Delta,IF,h,gamma)
    := Eq(gamma.J.payload, Unit).
```

This leaf occurs below the original admitted-challenge binder introducing
h/gamma, with Unit a fixed earlier descriptor. The displayed argument tuple
retains surrounding incidence even though this Eq reads only J.payload and
Unit. It is not Eq of an actual execution's returned value. The binder
fragment is `exists A at sigma; forall independently admitted h at A; P`;
all other original predicates/connectives keep their original positions.
H3 asserts an existing original leaf; it does not authorize adding one to
bare id or exchanging this telescope for a flat existential.

**H4 (candidate mutation).** The proposed prefix quotient gives the same
parent state z to the lawful A=Unit and A=Bool prefixes, retaining all their
other data. Its challenge successor set is the union of their child cells,
and leaf cells have exact P truth labels. This is the mutation that erases A
because currently evaluated validity facts agree and P is still unresolved.
An encoding that retains A, or independently proves extension equivalence,
does not satisfy this hypothesis.

**Conditional result:** H1–H4 imply violation of EPR clause 3. This is not a
counterexample to JOINT_DEC decidability, to EPR+ER, or to native id. Whether
an actually generated source residual satisfies H3 is unverified here.

## Minimized witness and derivation

Use one actual generic native id provider U_g and one original description
position sigma. Consider two alternative lawful prefixes, not two frames to
be amalgamated:

```text
a_U: A=Unit, bare-id Delta and its original well-scoped static evidence
a_B: A=Bool, bare-id Delta and its original well-scoped static evidence.
```

The provider, intrinsic q/IF0 and source operation remain the same. These
are alternative assignments at the same position; a branch cannot switch
from one to the other after its challenge.

1. At a_U use the genuine Unit carrier challenge h_U, with complete J_U of
   payload Unit, identity `mu_result`, and all original gamma fields. The
   supplied ground/context laws and bare-id Delta derivation make this a
   lawful checked challenge. Its complete tuple satisfies P.
2. Let z+ be its abstract child. Forward extension places z+ in Next(z).
   Exact leaf laws label z+ with P=true. Any other original predicates at
   this child retain their full tuple and truth labels.
3. Prefix-local backward extension would require a legal challenge h at
   a_B mapping to z+. Exact leaves would then give
   `Eq(gamma.J.payload,Unit)` at that same original h/gamma.
4. H2 also supplies `mu_result:gamma.J.payload -> Bool`. Substituting the
   original Eq produces a same-value `Unit -> Bool` inclusion. H1 excludes
   it. Therefore no such h exists at a_B.

Thus the positive child exists in one parent fiber and has no lift in the
other. The candidate preserves the encountered complete leaf labels but
fails **prefix-local reflection of legal extensions**. Even a total effective
classifier for this finite mutation would not repair the failure. Replacing
the earlier Bool choice by Unit, selecting a different generic-sum component,
or moving A below h would violate the original constructor/telescope.

Only two distinguishable parent prefixes, one positive child, two distinct
ground payload descriptions, one challenge binder and one separating leaf
are needed. A genuine Bool challenge is available by H1 but is not needed
for the contradiction. With one parent prefix there is no inter-fiber
extension failure; without a separating leaf, a different legal child can
have the same abstract label, so this particular argument does not apply.
The proof ranges over **every** legal challenge at the Bool prefix: no
history-depth bound, source-run restriction, or challenge sampling is used
to establish the missing lift.

## Bounded positive boundary and missing source bridge

The two supplied exact ground challenges themselves have a simple faithful
bounded presentation: retain A and the complete gamma identity. For the
domain containing just these two already supplied ground tuples, use two
parent states, two challenge child states and their P labels: four states
and two challenge edges. Classification and replay are finite table lookup;
lifts return the same supplied gamma. This covers that explicit two-tuple
restriction only, not the full original admission domain. It is not a new
source support boundary or a JOINT_DEC algorithm.

For the unbounded original domain, the witness proves the necessary lower
bound of **at least two distinct parent states** whenever H3 holds and leaf
laws are exact. It gives no sufficient finite-state bound.

Bare id's established Delta projection schema alone supplies no H3 observer.
The inspected records do not establish a concrete source/client derivation
emitting this Eq at that exact J telescope. Consequently there is no claimed
actual-source counterexample, unconditional finite native quotient theorem,
or whole-solver negative result. The exact next evidence is a source-derived
inventory of active observers on J and their original scopes. If all actual
observers are constant across these two challenge fibers, this witness does
not discriminate the actual encoding. Repeating it with renamed ground atoms
would leave that missing source bridge untouched.

## Evidence, checks and resource boundary

Oracle independence: the contradiction uses independent ground disjointness,
the selected native same-value inclusion rule, and original Eq substitution.
It does not use a checker that assumes the mutated transition table. H1's
genuine ground/local-law certificates are shared premises with native
Uniform-ID. Their source/production implementations were not independently
verified by this worker. H3 and H4 are additional candidate assumptions.

No executable probe, build, test, network operation, Git command, or child
agent was run. Read-only shell commands inspected the governing sections,
HEAD through its ref files, and SHA-256 dependencies. The rules named in the
assignment were read in full. Large task/index navigation reads were
truncated; no claim of exhaustive task/index inspection is made.
No seeds, randomized ranges, mutation enumeration or omitted search shards
exist: one named quotient mutation was examined by hand. Peak CPU/RAM and
total wall time were not measured; no background calculation was started.

The result fails to apply if Unit can lawfully include into Bool, the Unit
challenge does not have genuine full certificates, the Eq observer is absent
or differently scoped, the quotient separates these prefixes, or leaf cells
drop/approximate P. The last case itself violates exact-leaf requirements
but is not the prefix-extension argument proved here.

Recommended next action: trace one actually generated client/source J
observer and its telescope, then require the proposed prefix key to retain
the description or prove observer-respecting extension equivalence. This
does not justify adding a new observer merely to obtain a counterexample.

## Dependency snapshot and commit packet

Direct dependency SHA-256 values at submission:

```text
dbf98d3a6dbbd55c79289f5bb43dd3edf2fea76287f1203c83a4876d5a820977  notes/progress/2026-10-08-joint-dec-constructive-attempt.md
b9a6f724fc574a580d14ac31dcaca41fcc5347b50b6ecccf7976f15a102050e5  notes/progress/2026-10-08-id-inlet-whole-output-image-owner-cut.md
59442db205d0bc381de74a373f1d58a753e3366ae0ba845e8c9c877465e738fc  notes/theory/successor-proof-obligations.md
02e6e04d1a4eea405442587206e34c653b45405677d653e6bfec37568fee4f43  notes/design/2026-10-03-open-residual-factorization.md
273e8dae447e9997d586fc07abf48883c76b90988c8906094dd428a48339c2e5  notes/theory/2026-10-08-uniform-value-entry-constructor.md
b34c5b3644637bc1340f5636e0b6dc3fcc42c39de5d9cc73bcb48b84293e417e  notes/progress/2026-10-07-successor-global-synthesis.md
11bbee106e1f4332d0c0e97f9e2d4fc87cede0e4046b061d4e4fbe8a6768809d  notes/theory/2026-10-08-projection-export-proof-countermodels.md
```

- Exact leased/changed path:
  `notes/progress/2026-10-08-joint-witness-representation-counterexample.md`.
- Baseline SHA: `2e2adc88e93d3aadd8079e764d58e25af786019b`.
- Changed dependency hashes: none observed; final hash recheck recorded in
  the worker handoff. A later primary must revalidate any moved dependency.
- Review status: unreviewed conditional research; producer self-inspection
  is not independent review. Artifact frozen on submission.
- Checks run: governing-section reads; ref-file baseline confirmation;
  dependency SHA-256 calculation and final comparison. No executable checks.
- Proposed checkpoint message:
  `research: characterize checked-J prefix erasure under a retained payload observer`.
- Shared-record deltas left to primary/curator: optional research link and
  conditional extension-reflection blocker only. No DAG counts/status,
  semantic authority, source-emission claim, task completion or implementation
  change is proposed. All shared paths and question-board bundles untouched.
