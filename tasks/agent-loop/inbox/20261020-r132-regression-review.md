# R132 rev1 regression review

Result: **BLOCKING — P1**

Reviewer: `/root/r132_regression_final`; frozen candidate contract SHA-256 `5335bbb4e6d0bdcd1f0e46e947990d1e61cdde1e23e53045abbe8e0760e5efe6`.

Static reproduction: load the page, choose “Polymorphic identity”, then Run. Example selection replaces the source but retains `int_identity`, so the selected-definition API reports `MissingDefinition`; the old examples define `main`. All 12 old options are affected. The smoke invokes them using hard-coded `main`, so it cannot detect this UI transition regression.

Minimum closure: example selection sets `int_identity` for the new fixture and `main` for old examples, while retaining the editable control; add or perform focused transition regression evidence within authority.

The fixture is 388 bytes and matches its frozen source hash. All assigned changed-artifact and contract pins matched; previous source/oracle preservation was compared with primary-provided baseline content. No browser/runtime success is claimed. No tests, builds, compiler/CLI, formatting, generated files or mutations occurred. One accidental read-only `git status --short` occurred during initial discovery and was immediately reported; no mutation followed. Review STOPPED; model/effort UNKNOWN; elapsed UNKNOWN.
