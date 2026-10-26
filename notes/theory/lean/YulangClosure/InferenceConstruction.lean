import YulangClosure.InferenceProofs
import YulangClosure.SourceFunctionMembership
import YulangClosure.NativeDictionaryDenotation
import YulangClosure.OriginalSourceSyntax
import YulangClosure.OriginalSourceGeneration
import YulangClosure.OriginalSourceInterpretation
import YulangClosure.NativeContextExpansion
import YulangClosure.NativeDrainOwnership
import YulangClosure.NativeValuePorts
import YulangClosure.NativeContextReadback
import YulangClosure.NativeRowRepresentative
import YulangClosure.NativeContextCompletion
import YulangClosure.NativeValueStructure
import YulangClosure.NativeRepresentativeReadback
import YulangClosure.SourceSignatureConstruction
import YulangClosure.NativeContextCallbackConstruction
import YulangClosure.NativeValueDrain
import YulangClosure.NativeContextTables
import YulangClosure.SourceContributionConstruction
import YulangClosure.NativeRelationInterner
import YulangClosure.NativeValueRelationExecution
import YulangClosure.OriginalSourceChecking
import YulangClosure.OriginalSourceEnvironment
import YulangClosure.WholeMetatheory

import YulangClosure.SourcePrincipalTransport

import YulangClosure.NativeFreshScopeTransport

import YulangClosure.OriginalSourceRecordBoundary

import YulangClosure.NativeInferenceProgress

import YulangClosure.OriginalCheckingAdmission

import YulangClosure.OriginalFunctionFuture

import YulangClosure.OriginalRecursivePair

/-!
Source and native constructions for the original inference-soundness obligation.

This surface includes the reviewed source grammar, simultaneous interpretation,
finite checking, physical relation/Context/Value constructions, scoped witness
and native history components. Its companion audit selects exact originating
modules, including private and generated theorem constants.

These components do not instantiate the full original SourceProblem or discharge
all original descriptor/primitive/readout registrations, general recursive
introduction, complete native-success correspondence or the same-scoped witness.
No whole-language soundness claim follows from importing this module.

Run `lake build +YulangClosure.InferenceConstruction`, then
`lake env lean -j1 -M1536 AuditInferenceConstruction.lean`.
-/
