# Dynamic strict exits through silent raw changes

A representative-indexed local program can emit a valid projected write
after any raw silent prefix. A fixed program attached to the starting
projection alone is not justified. For a finite list of genuine silent
representatives, enumerate each one's local proposals and keep only
strict writes of the starting projected state. Soundness is unconditional
given the raw paths and local certificates. Completeness needs at least
one representative witnessing each distinct strict target, not all raw
prefixes or a fixed finite raw cache.

A classical cover exists for each initial state and fixed projection:
every strict target is a sublist of the current remaining facts. Enumerate
those sublists and choose at most one actual silent representative per
inhabited target, bounded by 2^remaining-length (duplicates only weaken
this bound). The choice is not an executable raw search and could be
blocked by the old raw loops. Replay on the finite window is executable
when the window and verified local tables are supplied. State the exact
failure of scope: zero strict exits implies no weak projected change,
not no raw steps. Preserve raw child installation and final payload
separately in the real 252/271 path.
