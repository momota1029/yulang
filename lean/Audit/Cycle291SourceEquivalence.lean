import Yulang.GeneralSourceMetadataBundlePermutation291

#print axioms Yulang.GeneralSourceMetadataPermutation291.get_perm
#print axioms Yulang.GeneralSourceMetadataPermutation291.source_perm
#print axioms Yulang.GeneralSourceMetadataRolePermutation291.same_role_table
#print axioms Yulang.GeneralSourceMetadataRolePermutation291.same_manifest_membership
#print axioms Yulang.GeneralSourceMetadataDiagnosticProvenance291.exact_origin
#print axioms Yulang.GeneralSourceMetadataDiagnosticProvenance291.sound_failure
#print axioms Yulang.GeneralSourceMetadataDiagnosticProvenance291.complete_failure
#print axioms Yulang.GeneralSourceMetadataBundlePermutation291.attached_reordered
#print axioms Yulang.GeneralSourceMetadataBundlePermutation291.whole_ready_unchanged

open Yulang
open GeneralSourceMetadataBundle291
open GeneralSourceMetadataBundleFixture291 (actual reordered)
#guard (inspect { actual true with declared := reordered, snapshot := reordered }).ready
#guard !(inspect { actual false with declared := reordered, snapshot := reordered }).ready
