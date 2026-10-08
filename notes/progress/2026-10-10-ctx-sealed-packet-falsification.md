# CTX_FINITE sealed packet: bounded falsification and missing source rule

Date: 2026-10-10 (leased checkpoint label)
Baseline: `6e839d5c74219226fe59f88addc87a4896396412`
Status: unreviewed research-only bounded source inspection and conditional mutation witnesses
Authority / implementation / gate closure: none
Producer: delegated falsification researcher; producer inspection is not independent review
Exclusive lease: this file only

## Objective and result

Independently attack the selected sealed result/store trace on five distinctions:
sibling openings at equal levels; shared versus independent witnesses;
caller-private equations; dependent suffix/telescope retention; and repeated
aliases/openings. The method is source-clause inspection plus minimal finite
witnesses against named representation mutations. No construction-lane artifact
or proposed transition implementation was used as an oracle.

No source-admitted counterexample to sealed result/store preservation was found
in the inspected rule set. The exact blocker is the absent source result/store
target-interface and bound-capture formation/elimination rule. The request
opening contract is selected; it does not supply that lifecycle rule. Native
source Generalize retains the scoped graph and explicitly does not establish
Pack/Decode or semantic hiding. Installing either missing rule in a checker
would assume the premise under attack.

This is a bounded characterization, not a nonexistence theorem. The mutations
below distinguish what a proposed representation must preserve. They neither
show acceptance by a production compiler nor refute the selected source rules.
CTX_FINITE remains OPEN-PROOF with GUARD_COVER and RAW_SOURCE prerequisites.

## Pinned dependencies and selected decisions

The primary supplied these exact inputs at the baseline. Reads used that Git
revision; current-file SHA-256 values also matched the supplied snapshot when
checked. No dependency hash changed during this work.

| Input | Governing sections | SHA-256 |
| --- | --- | --- |
| `notes/theory/successor-proof-obligations.md` | CTX-FINITE | `41e25bc633f69df302361f41c60c0c324e9713a7194373f23f9f7a182724e4a1` |
| `notes/progress/2026-10-07-ctx-finite-sealed-packet-boundary.md` | Entirety; Sealed packet cut and Disposition | `ad536efe993f32234cce753ee5c79a27df97fcaa476c68fe00a7ec771d687899` |
| `notes/design/2026-10-03-source-context-finite-closure.md` | §§2–3,6 | `dba409842c631d81dfeedbeafc7ca34dcd9edeaaa0a80f49bba0cb3f6916f8cf` |
| `notes/design/2026-10-02-operation-instance-binding-package.md` | §§2,7; §8 consulted for sibling-stack distinction | `1eb2cbdb49368b0839d839d6a5e72698bb06252813b00200098e70371645c7c9` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | §§3.1,3.3,5.2; §3.4 for client operands | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |

Additional authority corroboration used the selected Generalize definition
`notes/design/2026-10-08-source-generalize-definition.md` §§1–3 and charter
`notes/design/2026-09-29-scc-intrusion-redesign-charter.md` §§19–23 at that same
revision. These corroborate existing decisions; they select no new meaning.

Accepted decisions used here: one operation use chooses its local map once;
fresh rigid request openings check under declared bounds with captured fields
fixed; caller-private equations remain retained but do not become checking
assumptions; all dependent packet fields include the raw suffix when dependent;
aliases/resumptions retain the same witness. Source Generalize copies only the
eligible ordinary description declarations at their original scopes. Shared,
ViewLogic and actual event witnesses follow their own constructor incidences.
Numeric level alone supplies no sibling identity, and every derived comparison
retains its original guard obligation.

Draft finite-context premises are used only conditionally. In particular,
finite J_T, source-context closure, sound canonicalization, shared-assignment
soundness and terminating invalidation are inputs of its theorem, not proved
source facts.

## Minimal distinguishing cases

The finite domains below are mathematical test fixtures, not adopted Yulang
descriptor meanings. Minimality is relative to the named mutation and displayed
observer, not to all possible Yulang source programs.

### 1. Sibling openings with equal numeric level

Take one parent block with distinct sibling opening blocks L and R. Each opens
one name, k_L and k_R, at the same level l. In context L the identity-sensitive
observer is Visible(L,k_L)=true and Visible(L,k_R)=false. An encoding retaining
only l identifies the two names, so it cannot answer both queries correctly.
Two distinct names and one visibility query pair suffice; with only one name
there is no sibling collision.

**Classification:** distinct sibling ports and refusal to identify them are
selected clauses of finite-context §2 and premise 5 of §3. The operation
package §8 expressly retains separate sibling opening identities. The mutation
is ruled out by those clauses. A source result/store trace exposing the collision
is hypothetical until the missing lifecycle rule furnishes the actual observer
and ports. This is not a witness that correct lexical frontiers fail.

### 2. Copying a shared witness, or merging independent witnesses

Assume a witness domain {0,1}, one Shared binder s and two conjuncts s=0 and
s=1. The original join has no strategy. Copying s to independently chosen s_1
and s_2 admits (0,1). Conversely, two genuinely independent ViewLogic frames
can admit that tuple; merging them into one s rejects it. Replacing the second
new frame by alias of the first must restore the shared case. Two values and
two conflicting conjuncts are necessary for this particular satisfiability
distinction; one value cannot satisfy the split fixture.

**Classification:** new/alias incidence and Shared/ViewLogic placement are
selected-source-admitted handle rules in Generalize §§3.3–3.4,5.2. The
split/merge mutations are ruled out. The Boolean-domain equations are a
conditional fixture; no genuine primitive witness domain or packet store
operation is supplied by those clauses. This reuses the established
shared-witness distinction as a regression condition, not as a new source
counterexample or closure of sealed transport.

### 3. Reflecting a private equation into uniform arm checking

Use one operation-local binder beta, one actual request map beta:=Int and
one private ledger equation s=Int. The candidate mutation grants kappa=Int
after opening the packet. Its only arm demand is to assign the generic payload
to Int. Correct opening checks that demand uniformly under arbitrary kappa;
the private equation cannot discharge it. A second symbolic admissible type
T different from Int is enough to distinguish specialization from uniform
checking, provided the declaration is unconstrained and the genuine checking
law makes that assignment invalid at T.

**Classification:** the narrowing arm is explicitly ruled out by the selected
source decision, including an Int-only caller set (charter §19). Private-fact
retention and nonreflection are explicit in operation-package §2 and charter
§20. This is an existing rejected source shape, not an accepted source falsifier.
The optional two-type interpretation is a conditional explanation, not a new
disjointness axiom about rigid types. Retaining s=Int in K,D is lawful; using
that retained fact as the arm assumption is the failing mutation.

### 4. Dropping the dependent raw suffix or moving its telescope

Take one local binder beta incident to payload A(beta), response B(beta) and
raw suffix J(beta). The smallest incidence mutation removes the beta-to-J
edge, or makes J depend on a newly independent beta'. One binder, two distinct
dependent fields and one removed/shared edge already distinguish graph
incidence; the full packet additionally keeps response/profile/K,D fields.

For a conditional fiber witness assume beta in {0,1}, response coordinate
r=beta and suffix coordinate j=beta. The original public pair is restricted
to {(0,0),(1,1)}. Independent beta' adds (0,1) and (1,0). Dropping j entirely
does not itself prove a fiber mismatch unless an original lawful observer
actually observes or constrains j. The graph requirement and the observer
requirement are separate premises.

**Classification:** dependent J inside the same request package is selected
in operation-package §2; Generalize §§3.1,3.3,5.2 retain original pending
suffixes and event telescopes. Independent reassignment is ruled out. The
two-coordinate interpretation and a result/store observer are hypothetical
until independently furnished by an actual source rule. Generalize supplies
retention, not authorization to hide j or derive the result-boundary capture.

### 5. Alias reuse versus fresh proof names or fresh opening events

One packet has retained witness s. Alias h' of monomorphic h retains the same
instance map and frame. A mutation that independently chooses the local map
on h' reduces to case 2: a two-value observer distinguishes the maps. A change
of checking proof names from kappa to kappa' with the same substitution back
to s does not make that mutation. Both names denote the one retained instance;
alpha-renaming alone cannot establish that two instances were selected.

**Classification:** monomorphic alias reuse is selected-source-admitted;
re-instantiation on Alias is ruled out by operation-package §2 and Generalize
§5.2. Fresh capture-avoiding proof names are permitted by operation-package §4,
without new runtime instantiation. Arbitrary repeated elimination/opening of a
returned or stored package is hypothetical: the selected source rules supply
request opening and its original telescope, not a new result/store reopening
rule. A supposed falsifier requiring that rule cannot be promoted by choosing
new names in a checker.

## Oracle independence, omissions and failure conditions

The semantic oracle is the pinned source clauses and their explicit exclusion
of lifecycle closure. The mutation witnesses use direct set membership or
conjunction calculation; they do not compare two implementations of supplied
Pack/Open transitions. They share the displayed domain, binder-incidence and
observer hypotheses. Consequently they can refute a shortcut under those
hypotheses, but cannot prove that its source admission, observer meaning or
source preservation follows from Generalize.

Coverage is exactly five hand-inspected attack schemas, with two sibling names
or a two-value domain where needed. There was no random seed, executable
enumeration, search range expansion, compiler run, Oracle call, build, test or
performance measurement. No quantitative absence rate is claimed. Early broad
task/index and DAG locators were output-truncated; no claim relies on their
unread tails. The decisive selected sections above were subsequently read in
bounded extracts. No whole-source search for independently adopted store/open
constructors was performed outside the assigned source set.

The conclusion must be revisited if an actual result/store constructor and
opening rule supplies source admission plus a bound-capture map; if the owning
primitive supplies different observer domains; or if any pinned dependency
changes the identity, telescope, visibility or sharing contract. A valid
falsifier needs one independently legal source derivation before transport
and a proven mismatch after the proposed transport, with all original shared
fields and scopes fixed. None of these cases currently supplies that pair.

Resource use: serial lightweight reads and SHA-256 calculation only; no heavy
processes or persistent executable outputs. CPU, peak RSS and total wall time
were not measured. One new research note is the complete write set.

Document-integrity checks passed: a one-process `python3` read of this exact
file verified UTF-8 decoding, final newline, no trailing whitespace, exactly
five attack headings, baseline, commit packet and explicit research boundary.
`sha256sum` checked this artifact and all five primary dependencies; the latter
matched their supplied values. These are document/snapshot checks, not semantic
experiments or independent review. Baseline source reads used `git show
6e839d5c7:<path>` with bounded `sed`/`rg` section extraction; all Git operations
were read-only.

## Stop and recommended next action

Stop this falsification lane at the absent lifecycle premise. A transition
checker with supplied Pack/Open rules would leave the same premise untouched.
The recommended next action is for the primary to obtain the actual owning
result/store formation and elimination rule, with original typed root,
bound-capture witness map and suffix telescope, then commission a falsification
of that rule against these five distinctions. No new source restriction or
Generalize reinterpretation follows from this stop.

## Commit packet

- Exact leased path: `notes/progress/2026-10-10-ctx-sealed-packet-falsification.md`.
- Baseline SHA: `6e839d5c74219226fe59f88addc87a4896396412`.
- Changed dependency hashes: none; the five primary snapshot hashes above matched.
- Review status: unreviewed producer research; no independent review claimed.
- Checks already run: pinned section inspection; current dependency SHA-256
  equality; exclusive target absent before creation; the six document-integrity
  assertions above passed. No tests/builds/semantic probes.
- Proposed one-line commit message: `research: record bounded sealed-packet falsification limits`.
- Shared-record deltas left to primary/curator: optionally record the five
  mutation conditions and the missing source result/store rule as the exact
  lane blocker. Leave CTX_FINITE status, prerequisites, production relevance
  and existing boundary characterization unchanged. No task/index/authority or
  question-board bundle was edited.
