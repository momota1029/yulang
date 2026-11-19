import Yulang.GeneralRebaseEdgeLedger279
import Yulang.GeneralRebaseCompactDisplay279

open Yulang
open GeneralNominalExamples (displayRoot displayChild)
open GeneralDeclarationExamples (roles)
open GeneralRebaseOccurrenceCode279 (codeEdge)
open GeneralRebaseEdgeReceipt279 (edgeKnown freshEdges)
open GeneralRebaseEdgeLedger279 (normalize advance)
open GeneralRebaseInstallNovelty279 (Edge)

def real : Edge roles := (displayRoot,displayChild)
def collision : GeneralSourceDictionaries.Occurrence roles := ⟨displayRoot.identity,displayChild.demand⟩
def altered : Edge roles := (collision,displayChild)

#guard edgeKnown [real] real = true
#guard edgeKnown [real] altered = false
#guard ((normalize [real,altered,real]).map codeEdge) == ([altered,real].map codeEdge)
#guard ((advance [real] [real,altered,real,altered]).map codeEdge) == ([real,altered].map codeEdge)
#guard (freshEdges [real] [real,altered,altered,real]).length = 2
#eval (real.1.identity == altered.1.identity,edgeKnown [real] altered)
#eval ((normalize [real,altered,real]).length,(advance [real] [real,altered,real,altered]).length)
