# R264 result — R262 parser diagnostics need an environment qualification

Primary-only; no independent review.

R262 used an empty syntax environment, so its 474 diagnostics/recoveries are
not a clean Y2/Y3 grammar comparison. A broad environment built from every
pinned header is also not authentic per-module import state; it yields 500
diagnostics and 464 recoveries over 34 modules, including unrelated operator
collisions. The comparison establishes that the environment choice matters,
not that the Y2 sources are parseable or unparseable in the correct environment.

`pub mod name;` does retain Missing recoveries under both controls, showing a
real external-module shape gap. All remaining diagnostic causes are
unclassified. Derive per-module syntax dependencies before interpreting the
aggregate. R260 remains conditional. See R264 contract and theory note.
