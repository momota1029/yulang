# Cycle 294: report selected-role and whole-file recovery separately

The existing checked-in Rowan golden has a selectable role at [0] and
three raw Error tokens at the root after it. Cycle 293 extracts the selected
role; that does not certify the whole file. This cycle reports all explicitly
marked locations of the supplied tree, with exact paths and UTF-8 spans, and
offers strict or selected gates without changing Yulang acceptance.

The executable list is audited against direct mixed-child lookup, not a
Rust diagnostic count: Rust can group adjacent Error tokens, and additional
semantic/header diagnostics need not be wire marks. Keep independently
supplied parser diagnostics and brand authenticity separate. No new
Rust parser execution, name resolution, or raw kernel transitions.

## Diagnostics are not raw marks

The recorded gross range 49..58 is one Rust ErrorGroup, while the raw tree
contains three Error tokens. Rust also emits ConflictingOperatorFixity from
accepted-site/environment lookup, not from the mark scanner. An optional
adapter diagnostic receipt has three outcomes: not checked, failed collection,
or a supplied successful independent list. The executable receipt check
uses the external snapshot brand, not source-text equality. A foreign brand
or collection failure cannot certify any policy. An unlocalized diagnostic
cannot be waived by a selected-branch policy.

Any provided path is independently attached mixed-child ownership, not a
blind copy of Rust's diagnostic identity path. The raw structural walker can
use paths for error runs and recovery anchors that are not declaration
occurrence paths. A future Rust caller must attest that the list is complete
and the supplied locations come from the same retained parse. Here this is a
named assumption of the exact theorem, not an implemented Rust bridge.
