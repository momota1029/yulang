import Yulang.GeneralDeclarativeI65I74OriginalPatternSite460

namespace Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
open Yulang.GeneralDeclarations (Declaration)
private def original : Declaration :=
  ⟨30, 6,
    [.record 1 (.join (.variant 7 (.var 8)) (.variant 7 (.var 8))) (.app 0 [])],
    [⟨70, 61, [.var 9], []⟩,
      ⟨71, 61, [.record 2 (.variant 4 (.var 10)) (.app 0 [])], []⟩], [], []⟩
private def keys : KeyRead := fun n => if n = 0 then .emptyRow else .opaque

example : readSite original (.head 0) =
    some (.record 1 (.join (.variant 7 (.var 8)) (.variant 7 (.var 8))) (.app 0 .nil)) := rfl
example : readNormalizedPath keys original (.head 0) [.field 1,.tag 7] =
    some (.var 8) := rfl
example : OriginalNormalizedPath keys original (.clause 1 71 0) [.field 2,.tag 4] (.var 10) :=
  (normalized_path_iff_from_unchanged_source).mp rfl
example : readNormalizedPath keys original (.clause 0 71 0) [.field 2,.tag 4] = none := rfl
example : readNormalizedPath keys original (.clause 1 70 0) [.field 2,.tag 4] = none := rfl

#print axioms original_at_iff_site_read
#print axioms normalized_of_original
#print axioms normalized_reencodes_exactly
#print axioms normalized_path_iff_from_unchanged_source

end Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
