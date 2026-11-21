import Yulang.GeneralMixedFullControlCompiledQuotient306
import Yulang.GeneralFiniteColoredCertificate306

namespace Yulang.GeneralMixedFullControlCertificate306
open GeneralMixedFullControlCode306 (Code)
open GeneralMixedFullControlUnlabelled306 (codes targets classify)
open GeneralMixedFullControlMinimal306 (obligations)
open GeneralMixedFullControlModelClasses306 (key)
open GeneralFiniteColoredCertificate306 (certificate closureCheck)

theorem rejects_count_vs_accepts_class :
    certificate targets (fun _ => ()) obligations codes = false ∧
      certificate targets (fun _ => ()) classify codes = true := by decide +kernel

theorem phase_requires_extra_class :
    certificate targets Code.installed classify codes = false ∧
      certificate targets Code.installed key codes = true := by decide +kernel

theorem rejects_incomplete_domain :
    closureCheck targets ([⟨false,⟨false,false⟩⟩,⟨true,⟨true,true⟩⟩] : List Code) = false := by
  decide +kernel

end Yulang.GeneralMixedFullControlCertificate306
