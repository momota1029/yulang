import Yulang.GeneralRebaseFixedDisplayGraph280
import Yulang.GeneralRebaseCompactMachine280

open Yulang
open GeneralNominalExamples (displayRoot displayChild)
open GeneralDeclarationExamples (roles)
open GeneralRebaseCompiledDisplay277 (compiled parent)
open GeneralRebaseFixedDisplay280 (c valid target)
open GeneralRebasePortCatalog280 (catalog resolve code)
open GeneralRebasePortDecode280 (writes)
open GeneralRebasePortCopy280 (lookup)
open GeneralRebaseOccurrenceCode279 (occurrenceCode)
open GeneralRebaseChildPorts280 (fixed)

def decoderProbe :
    List (Option Nat) :=
  let table := writes parent.packet c valid
  [lookup table target.1,lookup table target.2,lookup table 1]

def catalogProbe : Bool :=
  decide (resolve (catalog compiled 1 displayRoot [100]) displayChild.identity =
    some (occurrenceCode (fixed parent.packet c valid)))

def compressionProbe : Bool := by
  let edge := (displayRoot,displayChild)
  exact decide (((GeneralRebaseEdgeLedger279.normalize [edge,edge]).map GeneralRebaseOccurrenceCode279.codeEdge) =
    [GeneralRebaseOccurrenceCode279.codeEdge edge])

#eval decoderProbe
#eval catalogProbe
#eval compressionProbe
example : decoderProbe = [some 1,some 1,none] := by decide +kernel
example : catalogProbe = true := by decide +kernel
example : compressionProbe = true := by decide +kernel
