import Yulang.GeneralSourceRoleCstCatalogReplay296

/-! Synthetic wrapped associated roles. Their numeric IDs come solely
from explicit finite rows, not from mixed ordinal or role spelling alone. -/
set_option maxRecDepth 16000
set_option maxHeartbeats 2200000
namespace Yulang.GeneralSourceRoleCstCatalogControl296
open GeneralSourceRoleCstNameCatalog296 (Catalog Lookup lookup)
open GeneralSourceRoleCstCatalogExport296 (run Exported Failure)
open GeneralSourceRoleCstCatalogTrace296 (Issue)
open GeneralSourceRoleCstSelectedControl295 (both first second packet)
open GeneralSourceRoleCstNamingPacketFixture295 (binderTrace ctorTrace)
open GeneralSourceRoleResolverFixture292 (parameterTable charTable)

def justRole : Catalog := [(.role "Index",some 2)]
def binder : Catalog := justRole ++ [(.output 2 "value",some 0)]
def constructor : Catalog := binder ++ [(.constructor "char",some 3)]
def absentOutput : Catalog := justRole ++ [(.output 2 "value",none)]
def conflicting : Catalog := binder ++ [(.output 2 "value",some 4)]
def duplicated : Catalog := binder ++ [(.output 2 "value",some 0)]
def irrelevant : Catalog :=
  binder ++ [(.role "Other",some 17),(.role "Other",some 18),(.constructor "value",some 9)]

theorem exact_finite_exports :
    run .selectedBranch 5 both 71 first (packet first) binder 2 = .ok ⟨binderTrace,parameterTable⟩ ∧
    run .selectedBranch 5 both 71 second (packet second) constructor 2 = .ok ⟨ctorTrace,charTable⟩ :=
  ⟨rfl,rfl⟩

theorem unobserved_and_explicit_absence_differ :
    run .selectedBranch 5 both 71 first (packet first) justRole 2 =
      .error (.evidence (.missing (.output 2 "value"))) ∧
    run .selectedBranch 5 both 71 first (packet first) absentOutput 2 = .error .oldExport := ⟨rfl,rfl⟩

theorem duplicate_and_conflicting_rows_rejected :
    run .selectedBranch 5 both 71 first (packet first) conflicting 2 =
      .error (.evidence (.ambiguous (.output 2 "value"))) ∧
    run .selectedBranch 5 both 71 first (packet first) duplicated 2 =
      .error (.evidence (.ambiguous (.output 2 "value"))) := ⟨rfl,rfl⟩

theorem footprint_is_local :
    run .selectedBranch 5 both 71 first (packet first) irrelevant 2 = .ok ⟨binderTrace,parameterTable⟩ ∧
    run .selectedBranch 5 both 71 second (packet second) binder 2 =
      .error (.evidence (.missing (.constructor "char"))) := ⟨rfl,rfl⟩

theorem cannot_retarget_catalog_export :
    run .selectedBranch 5 both 71 second (packet first) constructor 2 = .error .selection := rfl

end Yulang.GeneralSourceRoleCstCatalogControl296
