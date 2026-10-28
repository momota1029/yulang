import YulangClosure.PaperTermSubstitutionAlgebra
import YulangClosure.PaperCallEntryFormation
import YulangClosure.PaperAllocationExecution
import YulangClosure.NativeIntegerArithmetic

/-!
Explicit default-build entry point for the 2026-10-26 proof advancement.
The separate glob preserves the existing root's concurrently reserved imports
while making all four new modules part of an ordinary `lake build`.

These are substitution, call-code formation, allocation/continuation and exact
primitive-arithmetic results. Their original source/native and whole-language
boundaries are stated in each module and the associated progress record.
-/
