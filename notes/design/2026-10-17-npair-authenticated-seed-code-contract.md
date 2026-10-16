# NPAIR authenticated seed and antecedent readiness contract

Status: unapplied readiness design; compiler code remains unmodified.
Sprint: `npair-authentic-seed-antecedent-20261017`, contract revision 2.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN.

## Frozen evidence and result

Proof artifact `notes/theory/2026-10-17-npair-authentic-seed-antecedent.md`,
SHA-256 `0121e51f0f41da70c16f301df8f3ddebcbffc37171029a37d604401d8caa0be3`;
handoff SHA-256
`a9c68beb7f9ba77feb7096927b37b123cc49fdc657b2b6c1a4700f1ff70fa8a8`.
All 13 pinned dependencies matched. The author stopped after six stages and
charged the full 900-second cap. The result is static source/native evidence,
not an execution or parent proof.

An ordinary Operation signature has an existing authentic seed: a physical
`Support(view)` lower whose retained `OperationOrigin` and member identify the
declaration, owner, source occurrence, signature position and member. Actual
FunctionPort and ordered Replay records can provide a checked structural
arrival skeleton. The system does not always retain which Origin was selected
when several Origin records share an interned relation. That is an ambiguity in
the admission-to-selected-Origin projection; it is not a demonstrated pair of
indistinguishable complete source runs, and it does not establish that a new
event ID is necessary. A checked existential derivation over all applicable
alternatives may suffice, but this contract does not decide that theorem.

## Authentication obligation for a future native consumer

A future consumer that uses formal-port Permission data to establish an
ordinary arrival must validate one complete chain, rather than infer
authenticity from a family or row equality:

1. A live physical lower emission names its exact admission, bound, canonical
   effect owner, lane and slot. The slot still contains the expected operand
   under the current version/canonicalization rules.
2. The operand resolves to a retained source-owned interface member. For the
   existing Operation case, validate `OperationOrigin`, declaration identity,
   owner, occurrence, signature position and member index/family. A fabricated
   view, stale slot, out-of-range member, family-only match or bare
   `Contribution(u32)` cannot pass.
3. The bound admission's retained relation and source context connect to an
   actual FunctionPort child with the required field and variance operation.
   Ordered Replay inputs and endpoints must be checked when they mediate the
   arrival. Traverse relation alternatives with cycle guards; do not take the
   first Origin or treat interned relations as a tree.
4. The exact negative Permission record is connected to the same Function
   projection by its owner, formal occurrence, scope and typed child path, and
   to the actual row occurrence and concrete source IDs. Row identity or
   family equality alone does not establish this incidence.
5. Preserve enough lifecycle evidence to reject rolled-back, truncated,
   canonicalization-stale or slot-reused emissions. This contract adds no
   persisted selector or registry. The owner must either prove that a checked
   existential derivation over every retained alternative establishes the
   original delta, or return to Luna for a representation decision that stores
   the actual selector at its owning operation.

The exact unresolved decision is step 5's relation between selected Origin and
processing event. The proof only establishes projection ambiguity. It neither
chooses an existential sufficiency theorem nor licenses a new source/event
identity field. No consumer or source/native soundness theorem is implemented
by this design.

## Proposed producer representation and boundaries

The separately reviewed concrete-only producer patch is authorized by the
user's reply “採択で構いません” to the exact approval request for the reviewed
design below. This is approval of that bounded patch only, not of the
authentication obligation above or source admission.

- Design: `notes/design/2026-10-17-npair-native-port-code-contract.md`,
  SHA-256 `a6b6f37218408b334922c19ff6065bd8bd607294201ec2b371f1376e800c41ce`.
- Review handoff revision 3:
  `tasks/agent-loop/inbox/20261017-npair-native-port-code-contract.md`,
  SHA-256 `6ec84d409f261345ab682c1d37b6d41126fb7d69fff2577ab580bc92a295c3d1`.
- Conditional proof reviewed CLEAN:
  `notes/theory/2026-10-17-npair-concrete-producer-refinement.md`,
  SHA-256 `ad7a89545c7318f0c19402313c495663af49a51279ab6376bded260740006389`.

Before any source write, revalidate the exact design, effective review,
adoption pins and current owners, then issue a continuation contract with the
two exact paths below. The patch stays in `candidate_effect.rs` and the
implementation handoff. It adds only a bounded nonempty negative concrete-only
formal port: one shared fresh row for both polar terms and separate self-owned
Permission records, with existing Function construction order, child paths,
links 43/44, checked accounting and route rollback. Keep source preflight's
refusal, root computation effects and existing behavior intact. Stop if
identity storage, path capacity or rollback requires another owner/file.

It does not add a seed consumer, Contribution producer, admission selector,
At, transport, subtraction, source acceptance, mixed/multiple-symbolic or
explicit-empty support. Those forms and original semantic/provider/world/
continuation/future quantifiers remain open. The producer is inert metadata;
it cannot be treated as an authenticated arrival without the chain above.

## Next evidence and falsifiers

- `NPAIR-SEED-INTERFACE-VALIDATION`: validate a live Operation member through
  emission/admission and reject fabricated members, stale slots, missing
  admissions, family-only matching and Contribution-only assumptions.
- `NPAIR-DELTA-ORIGIN-SELECTION`: prove existential alternatives sufficient
  for the original delta, or identify the exact owning operation that must
  retain a selector. Arbitrarily selecting one Origin falsifies the result.
- `NPAIR-DESCRIPTOR-INCIDENCE`: connect the exact Permission path/occurrence to
  the reached Function projection and account for existing and future lowers.
  Row or family equality alone falsifies the result.

The next implementation packet is sequential after this proof's independent
reviews and frozen-source barrier. It must begin with source-pin revalidation;
the current proof's conclusions are about its pinned source bytes and do not
automatically transfer to modified code. No tests, builds, probes, compiler
execution, source admission or production claim is authorized by this
readiness contract.
