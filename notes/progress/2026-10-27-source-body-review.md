# Independent review: original source body consumer

Date: 2026-10-27. Reviewer: `/root/principality`; no production authorship.
Verdict: **ACCEPT the local packet interpretation and conditional Build-to-body
consumer theorems.** No blocking proof defect found within that scope. The
EventProof interpretation correspondence below remains a material boundary;
this is not acceptance of all-original-domain closure.

## Frozen target and method

`notes/theory/lean/YulangClosure/OriginalSourceClosure.lean`, SHA-256
`e39f165848c512830e6f92893c61e2d9f07cec66b729e8878c5f7d3491ab429a`.
The hash matched before and after review. All 499 lines were inspected.

I compared the construction with SG
`2026-10-08-source-generalize-definition-and-proof.md` §§3.2–3.3, the selected
`2026-10-08-source-generalize-definition.md`, the original heterogeneous
admission/decoder, the actual `checkedBody`/Lambda/Build definitions, the
source-owner traversal, and the finite `OriginalSourceChecking` proof
interpretation. The producer's paired note explicitly retains the local
interpretation and original-catalogue correspondence limits; those limits
are necessary to this verdict.

## EventProof ownership: accepted construction, retained coverage limit

The packet carries independently variable view interpretation, assignment
and logical witness under an explicit original `Owner` index. No completed
membership, desired formal equality, body derivation, or computation-inclusion
law is a packet field. It does not introduce a runtime event. Desc and
Interface introductions remain separate owning source rules, as required by
SG §3.3; the arbitrary original body still contains its own such rules.

`proofAdmissions` is nevertheless a **strengthening of an arbitrary supplied
raw `LocalAdmissions`**: every EventProof payload must have literally empty
descriptor and interface write lists. Retaining `base.logical` as a conjunct
does not prove preservation of all values it previously admitted.
`proof_packet_admission_exact` establishes exactness for the newly defined
packet encoder, not for every raw `Logical` payload.

This distinction matters even for harmless representations. A raw payload
can repeat an existing endpoint's unchanged descriptor in its write list;
that can leave the decoded descriptor map unchanged while violating literal
list emptiness. SG's semantic ownership distinction alone does not prove that
an arbitrary old admission relation excludes or normalizes such payloads.

The code and paired note correctly state the theorem under the constructed
`closureKernel`, rather than claiming equivalence with every earlier kernel.
Thus the local proof is accepted. Application to a separately fixed original
catalogue still requires its actual proof-field constructor or an
admission/normalization correspondence preserving the relevant local
predicates, frame readout, and whole source solution. No all-source
conservativity or completeness claim is accepted from the empty-list test.
All other logical kinds and all runtime admission cases retain their previous
pointwise meaning; the selected packet's eta/witness/view fields remain free.

## Original source owner and generated consumers

`body_proof_owner_registered` locates the EventProof at the second child of
the actual `checkedBody` sequence. `actual_lambda_body_owner` checks both
entry modes in the whole source traversal. `scoped_body_owner_registered`
retains the enclosing route and every ambient predecessor; repeated sites
require no global uniqueness premise. These are actual source registration
equations, not route reconstruction from a flat Binder.

`admitted_proof_packet` inverts the heterogeneous admission at the same
decoded environment. `proof_packet_preserves` computes the ordinary decoder:
all descriptors, interfaces, installed bindings, actual values/roots,
static fiber, eta0, runtime history/configuration, scope, authority,
incidence, dictionary, fixed prefix, callable owners and active call fields
remain. The actual environment extension also preserves event identity,
anchors, publication map and replay state. Independent logical eta, witness
and view interpretation are explicitly allowed to change.

`checked_body_consumer` extracts the real pattern proof, EventProof witness,
finite computation check and body proof from the original generated tree.
The same EventProof environment is used for the body and its consumer.
Neither pattern nor body is restricted to a special source constructor.
The computation check is exactly `body.finalRoot` to `lambda.bodyConsumer`;
the target is not replaced by an interior endpoint.

The two principal roots apply this extraction to the actual Lambda Build:

- `generated_value_body_consumer` preserves Description/View before every
  independently admitted invocation, its receipt, every admitted Return,
  then the original Shared/body scope.
- `generated_computation_body_consumer` preserves the retained entry's
  receipt/Shared/body scope without inventing a Value Return or Force.

Both permit an arbitrary original pattern/body and the original optional
outer annotation. Peeling the annotation's child does not prove its premises
unconditionally or remove them from the input Build. `BodyConsumer` is an
output proposition, absent from Kernel and admission fields; there is no
circular definition of source typing by the desired consumer conclusion.

## Finite checking and semantic boundary

`closureKernel` installs source and goal-indexed checking admissions before
constructing the finite checking kernel. Consequently the Function checking
shape captures the final checking domain, rather than a stale record field.
The idempotent local-kernel equation used by the Build consumers is correct.

The semantic action is obtained by the existing `checking_sound` induction
and `computation_action`. It preserves the same arbitrary complete raw
observation and uses **completed `Meaning`** at the exact interfaces. There
is no cast into `Background` or an arbitrary provisional candidate.

An independent actual body trace membership is still needed to apply this
action. The theorem does not infer that membership from a source judgment,
construct every original primitive/Call/State interpretation, prove recursive
L4, authenticate every prior/native history, or establish full future-domain
registration. It also retains the already documented global route-sensitive
formal-selection boundary. Original whole soundness, Effect hygiene,
principality and inference termination remain OPEN.

## Independent check and frozen receipt

The parent freshly built the frozen target and owns the cache. One independent
direct Lean audit inspected all **19 public authored theorem types and their
complete transitive axiom sets**, confirming theorem kind. It exited 0 without
warnings under pinned Lean 4.35.0:

```sh
timeout 120 env LEAN_NUM_THREADS=1 \
  /workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake \
  env lean -j1 -M1024 --root=/tmp/yulang-principality-body-review \
  /tmp/yulang-principality-body-review/Audit.lean
```

| Complete axiom set | Public authored theorem count |
| --- | ---: |
| none | 5 |
| propext | 6 |
| propext, Quot.sound | 2 |
| propext, Classical.choice, Quot.sound | 6 |

The three consumer roots use the three standard axioms. Every transitive axiom
was checked against that allowed set. No project axiom, `sorryAx`, unchecked
native evaluation or kernel bypass occurred. Parent/producer owns the complete
private/generated census; this review does not claim that broader census.

| Scratch evidence | SHA-256 |
| --- | --- |
| `/tmp/yulang-principality-body-review/Audit.lean` | `0b6795d6bba50d129285437ea53422ca1c23848f40cea8f003186a1b9a34ceac` |
| `/tmp/yulang-principality-body-review/review.log` | `618e8975e46a1fb9e3eb605bdbd83efba3950a98ff133d7a50779d1930a8044d` |

Only this review note and the two named scratch files were written. No proof
target, dependency, compiler, configuration, cache, Git or shared status was
changed. **Review writes stopped; no checker or descendant remains running.**
