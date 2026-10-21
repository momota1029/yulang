# R265 result — header imports do not cover direct Y2 use declarations

Primary-only; no independent review.

The exact 40-source bundle passed its embedded Git-blob checks. Under a
temporary comment projection and source-local environments built from
`scan_header`, the parser saw 112 direct `UseDeclaration` roots but only 45
header imports; counts differ in 20 modules. For example, `std::num` has
0/1, `std::io` 0/3, `std::time` 0/5 and `std::io::console` 0/4. Thus these
environments cannot authenticate module-local operator dependencies.

The 491 diagnostics/recoveries are not a source-compatibility verdict because
the dependency environment is incomplete. Y2 external `pub mod name;` still
produces Missing recoveries under each tested environment. The diagnostic
probe was removed. Inspect direct-root `UseDeclaration` CSTs next; Y2 import
resolution and module registration remain OPEN. See R265 contract and theory
note.
