# Cycle 181: semantic readback compatibility

Status: Draft proof-engineering note, 2026-11-14.

## Target and scope

The target remains I-30's `B4SkeletonV5.EvidenceNode
(GeneralNominalCenteredGroundBoundary.groundBoundary roles)`. This cycle does
not change that boundary, its notion of selection, or the other three fields
owned by Astra. Fresh integration is `bf6bc0d16263e9b418f0cfcea7c8f9ce621920b9`.

Cycle 180's arbitrary-origin extension fixes exact center values; its
source-origin specialization already needs only semantic equivalence. The
next local step removes that unnecessary exactness for general finite origins,
and connects the existing overlap-compatible linear nominal readback to a
complete candidate plan model. No old proof file is rewritten.

The full old raw and centered footprint is preserved. A fixed previous model
can extend across an overlapping binder only when its old value agrees with
the new observed nominal value. This is a local compatibility condition, not
a claim that the source language rejects the candidate or that no other model
exists. The eventual producer must still establish the required conditions
for reachable selected candidates rather than assume them.

## Verification plan

Use an isolated one-worker Lean cache and focused dependency closure. Audit
all new declarations with trust zero and warning-as-error. Do not run the
full repository build. Preserve historical imports and published files while
incorporating the pending upstream class-local work without modifying it.

## Checkpoint results

- `GeneralNominalSemanticCompatibility181`: arbitrary finite nominal origins,
  shared centers and old overlaps require `Equivalent`, not representative equality.
- `GeneralNominalObservationExtension181.extension_iff`: eliminates chosen
  representatives; observation existence, bounds, pairwise center coherence and
  overlap compatibility are necessary and sufficient for fixed-footprint extension.
- `GeneralDictionaryCenteredOverlapExact181.joint_iff`: actual finite linear
  nominal leaf plans have exactly the nonpoint overlap condition, with point
  input names and a fixed previous model.
- `GeneralNominalBinderIdentity181`: same-seed allocated binder collisions expose
  invocation, declaration and binder identity; registered actual uses give readback.
- `GeneralDictionaryCenteredProvenance181`: a syntactic registered-use coverage
  certificate supplies overlap compatibility, a joint model and, with separate
  raw-installation/value-support assumptions, a stable Instance.
- `GeneralNominalSemanticCollisionExample181`: two unequal chosen types, top and
  union(top,top), share one fresh center. Semantic extension succeeds; simultaneous
  exact assignment is impossible. This is a finite-family regression, not a
  source Candidate or reachable-boundary counterexample.

General G EvidenceNode remains OPEN (0 newly closed fields). Coverage has not
been derived for all full-footprint overlaps in reachable states. In particular,
raw-source freshness alone does not classify historical plan/site sources, and
old registered origins still need transport to the refreshed current candidate.
Astra's class-local obstruction concerns another boundary and is not transferred
to G. No semantic design decision is made here.

## Ordinary aliases and ledger-only production

`GeneralNominalOriginAlias181` transports nominal and structural paths through
source renaming. Non-source observations retain the exact observed value; bare
source observations are equivalent. This uses projection witnesses and does
not assume structural observation uniqueness.

`GeneralNominalOriginRootAlias181` reduces the premise from all source names
to the single root of the origin. `RootRecorded` is root equality or the two
opposite ordinary `tyLe` atoms in the current source state. Models derive the
semantic alias. `GeneralDictionaryCenteredAliasProvenance181` uses this syntax
certificate to obtain candidate overlap compatibility and a joint model.

A further simplification is proved in `GeneralNominalLedgerReadback181`:
registered actual head-use equations are already in the centered Models ledger.
The local readback needs neither a reachable path nor raw packet registration.
`GeneralDictionaryCenteredLedger181` therefore constructs both plain-covered
and alias-covered joint candidate models without a path premise. A path remains
relevant to proving coverage, not to consuming existing ledger equations.

The new `GeneralDictionaryCenteredLedgerExample181` is a real inspected
Candidate in a nonempty modeled ledger. Its nonpoint binder belongs to the old
footprint, so FreshInputs is false; registered coverage nevertheless constructs
a joint model. It is deliberately not asserted reachable, stable or novel.
`GeneralNominalOriginAliasExample181` separately checks a nonempty ordinary-alias
source model and actual nominal observations at distinct source names.

The audit branch's `notes/audit/x-oracle.md` was freshly read (blob
`0d75bdb801151589d5aeef453fd6b7dfa414baec`). X13-X16 are only approximations to
internal interval/sharing judgments, explicitly not arbitrary internal constraints.
They do not certify this cycle's centered-ledger extension. No new Yulang2 run
or source-to-Lean correspondence is claimed.

## Mode-sensitive footprint refinement

Review found a concrete overapproximation: the old schema frame lists a binder
for lower/upper uses even though their semantic clause never reads it. The next
local refinement keeps origin+binder for actual uses, and origin+capture
output/endpoints for endpoint uses. Prove schema framing and full ledger framing
with this smaller support, leaving all raw journal support unchanged. A generic
finite observation-extension construction can then instantiate this proved
frame instead of fixing the older, unnecessarily large fullSources list.
This does not classify all reachable overlaps or delete genuinely used captures.

The mode-sensitive schema and full centered-frame theorems have now passed
verification. `GeneralNominalModeExtension181.extension_iff` uses that concrete
frame, so its callers supply no frame hypothesis. The mode regression has a
valid upper-use schema before and after changing its otherwise unused binder
from top to bottom. This is strict reduction of the singleton schema footprint,
not a claim that a complete plan can change the same binder: captures or actual
head uses elsewhere may still constrain it. The final focused build passes all
18 new modules; the complete new-declaration gate passes 141 declarations.
