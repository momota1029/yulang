# Actual Journal243 support composition

Enumerate every field of the actual compiled Journal243: current/source raw
views, observed argument lists, live sites, packets, effects. Each effect has
private raw state, projection, historical class equations and live class
equations. Class support contains effect expression/target reads and equality
atom reads. Observed support contains bounds and optional-origin reads.

The invariant theorem uses global row equality and literal equality only on
the calculated finite typed-support list; no abstract Stable law. Applying it
to compile(state,mapping old) enumerates the actual lists used by compile, not
a user-supplied arbitrary plan list. Journal compile remains noncomputable
because actual class alias-request enumeration is noncomputable.

The actual Journal.Models bridge retains LegacyEmpty explicitly. Existing
source_exact and point_source_exact obtain it for their actual reachable
states; this is not a claim of a new successor transition or all later steps.
Parent handles expansion/recovery/public iff and these reachability corollaries.

Verified: JournalSupport249 and OrderedJournalClosed249 (GeneralNominal prefix)
pass strict focused compilation. ClassSupport249, ObservedSupport249 and
OrderedClassClosed249 also pass. journal_closed proves that actual compile
with a SafeOrder old mapping removes all old targets from the calculated typed
support, and within_protected therefore covers the former subset-target case
without an extra support assumption. Fresh targets outside the old domain still
require separation from calculated support. Rows remain globally preserved.
