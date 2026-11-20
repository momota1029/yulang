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
