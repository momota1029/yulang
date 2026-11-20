import Yulang.GeneralSourceRoleCstCatalogFailure296

/-! Closed controls for repeated requests, contradictory stored rows, and
the unavoidable need to know which lowered row is authoritative. -/
namespace Yulang.GeneralSourceRoleCstRecoveredControl296
open GeneralSourceRoleSpelling292 (Role)
open GeneralSourceMetadataBareRole291 (BareRow)
open GeneralSourceRoleCstNameCatalog296 (Catalog Lookup lookup)
open GeneralSourceRoleCstCatalogTrace296 (produce requireAll Issue)
open GeneralSourceRoleCstNamingRequests295 (Query)
open GeneralSourceRoleCstNamingTrace295 (Trace)
open GeneralSourceRoleCstRecoveredCatalog296 (recoverCatalog)
open GeneralSourceRoleCstReifyRow296 (recover)

def repeatedChar : Role := ⟨"Several",[],[⟨"x",.nullary "char"⟩,⟨"y",.nullary "char"⟩]⟩
def compatibleRow : BareRow := ⟨8,0,[(1,some (.app 3 [])),(4,some (.app 3 []))]⟩
def conflictingRow : BareRow := ⟨8,0,[(1,some (.app 3 [])),(4,some (.app 7 []))]⟩
def compactCatalog : Catalog :=
  [(.role "Several",some 8),(.output 8 "x",some 1),(.output 8 "y",some 4),(.constructor "char",some 3)]
def fullOccurrenceTrace : Trace :=
  [(.role "Several",some 8),(.output 8 "x",some 1),(.constructor "char",some 3),
    (.output 8 "y",some 4),(.constructor "char",some 3)]

theorem repeated_queries_share_unique_catalog_observation :
    recoverCatalog repeatedChar compatibleRow = some compactCatalog ∧
    produce compactCatalog repeatedChar = .ok fullOccurrenceTrace ∧
    lookup compactCatalog (.constructor "char") = .known (some 3) := ⟨rfl,rfl,rfl⟩

theorem contradictory_recovered_ids_refused :
    (recover repeatedChar conflictingRow).isSome = true ∧
    recoverCatalog repeatedChar conflictingRow = none := ⟨rfl,rfl⟩

def binderRole : Role := ⟨"Index",["'container","'key"],[⟨"value",.binder "'key"⟩]⟩
def ordinary : BareRow := ⟨2,2,[(0,some (.var 1))]⟩
def alternate : BareRow := ⟨42,2,[(17,some (.var 1))]⟩
def wronglyPlaced : BareRow := ⟨2,2,[(0,some (.var 0))]⟩

theorem binder_must_match_actual_positional_index :
    recoverCatalog binderRole wronglyPlaced = none := rfl

theorem shape_does_not_authorize_numeric_ids :
    recoverCatalog binderRole ordinary = some [(.role "Index",some 2),(.output 2 "value",some 0)] ∧
    recoverCatalog binderRole alternate = some [(.role "Index",some 42),(.output 42 "value",some 17)] :=
  ⟨rfl,rfl⟩

theorem reports_first_failure_in_query_order :
    requireAll [(.role "X",some 1)] [.role "X",.output 1 "f",.constructor "char"] =
      .error (.missing (.output 1 "f")) := rfl

end Yulang.GeneralSourceRoleCstRecoveredControl296
