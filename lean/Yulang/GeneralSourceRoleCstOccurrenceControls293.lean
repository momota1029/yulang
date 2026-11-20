import Yulang.GeneralSourceRoleCstDistinct293
import Yulang.GeneralSourceRoleCstConsumerFixture293

/-! A transport must keep occurrence identity separate from spelling, spans,
and resolved tables. Reusing an external brand admits a different snapshot. -/
namespace Yulang.GeneralSourceRoleCstOccurrenceControls293
open GeneralSourceRoleCstTree293 (Tree Path)
open GeneralSourceRoleCstProducer293 (extract)
open GeneralSourceRoleCstFixture293 (role head block required whole namedBody sigil id result)
open GeneralSourceRoleCstSnapshot293 (Snapshot Address exportAt mark)
open GeneralSourceRoleTrack292 (Tracked runTracked)
open GeneralSourceRoleCstShapes293 (toHead)
open GeneralSourceRoleResolverFixture292 (localEnv)

def repeated : Tree := role head (block required required)
def expectedRepeat : Tracked Unit Path :=
  ⟨(),toHead "Index" ["'container","'key"],[],
    [([6,1,0],.typeDecl ⟨"value",false,.absent,true⟩),
     ([6,3,0],.typeDecl ⟨"value",false,.absent,true⟩)]⟩

theorem no_spelling_dedup_in_unresolved_producer :
    extract () [] repeated = some expectedRepeat := rfl

theorem later_duplicate_id_declined :
    runTracked (fun (_ : Unit) => localEnv) 2 [expectedRepeat] = none := rfl

def reusedBrand : Snapshot Nat := ⟨10,whole (namedBody (id "char"))⟩

theorem brand_reuse_does_not_authenticate_snapshot :
    exportAt () reusedBrand ⟨10,[2]⟩ = some (mark 10 (result (.nullary "char") true)) ∧
    exportAt () GeneralSourceRoleCstConsumerFixture293.stored ⟨10,[2]⟩ =
      some (mark 10 (result (.binder "'key") true)) :=
  ⟨rfl,rfl⟩

end Yulang.GeneralSourceRoleCstOccurrenceControls293
