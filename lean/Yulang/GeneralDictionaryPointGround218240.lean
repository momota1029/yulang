import Yulang.GeneralDictionaryPointReobserve240
import Yulang.GeneralNominalPointSourceBoundary240
import Yulang.GeneralDictionaryMixedGround218Point235
import Yulang.GeneralDictionaryMixedGround218FinalState235
import Yulang.GeneralNominalPointEqualityTrace240
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryPointGround218240
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryMixedGround218Packet234
open GeneralDictionaryMixedGround218Install234
open GeneralDictionaryMixedGround218Point235
open GeneralNominalPointKernel240

theorem install_step : Step registry root initial installed :=
 ⟨root,.root,.install effect installable novel⟩

theorem reobserve_step : Step registry root installed point :=
 GeneralDictionaryPointReobserve240.eight rfl allocated reserved ordinary context_same registry root

theorem installed_reachable : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) sourceRegistry root installed :=
 ⟨initial,initial_source,.tail .refl install_step⟩

theorem point_reachable : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) sourceRegistry root point := by
 obtain ⟨start,initial,path⟩ := installed_reachable
 exact ⟨start,initial,.tail path reobserve_step⟩

theorem second_install_step : Step registry root point GeneralDictionaryMixedGround218PointInstall235.installed :=
 ⟨root,.root,.install GeneralDictionaryMixedGround218PointInstall235.effect
 GeneralDictionaryMixedGround218PointInstall235.installable GeneralDictionaryMixedGround218PointInstall235.novel⟩

theorem second_installed_reachable : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles)
 sourceRegistry root GeneralDictionaryMixedGround218PointInstall235.installed := by
 obtain ⟨start,initial,path⟩ := point_reachable
 exact ⟨start,initial,.tail path second_install_step⟩

theorem final_reachable : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles)
 sourceRegistry root GeneralDictionaryMixedGround218FinalState235.finalState := by
 obtain ⟨start,initial,path⟩ := second_installed_reachable
 exact ⟨start,initial,GeneralNominalPointEqualityTrace240.append path
 (GeneralNominalPointEqualityTrace240.steps GeneralDictionaryMixedGround218FinalState235.equality_path registry root)⟩
end Yulang.GeneralDictionaryPointGround218240
