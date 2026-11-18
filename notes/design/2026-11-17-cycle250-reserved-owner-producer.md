# Cycle250: constructive stable owner initialization

Status: Draft successor representation, I47(a).

Choose one owner seed above the complete current materialized typed-support,
all existing definition targets/RHSs, and an explicit finite public-name list.
Use the existing actual stable lo/hi key encoding with that seed, and reserve
both keys for EVERY input name, including currently singleton occurrences.
Store the seed with the owner; never recompute it on refresh. This is a new
materialized-owner allocator, not an assertion that its seed equals a legacy
source State.seed. Existing journal/source acceptance is unchanged by a proved
private extension; all public names and active metadata are protected.

Persistent updates retain every target, use actual lower/upper formulas from
Definitions241, and snapshot their RHSs through the old ordered mapping. All
raw entries are covered and coherent. Newly added metadata is handled after
update by PostInstall/FiniteInstallTrace, with explicit preconditions on the
computed fresh witness. Actual versioned-to-stable packet production and live
class-request regeneration remain open, as does source-generated finiteness.
