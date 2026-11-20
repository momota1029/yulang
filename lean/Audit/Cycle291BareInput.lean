import Yulang.GeneralSourceMetadataBareFixture291

#print axioms Yulang.GeneralSourceMetadataBareRole291.bounded_exact
#print axioms Yulang.GeneralSourceMetadataBareRole291.row_exact
#print axioms Yulang.GeneralSourceMetadataBareRole291.list_exact
#print axioms Yulang.GeneralSourceMetadataBuildRoles291.build_exact
#print axioms Yulang.GeneralSourceMetadataBuildRoles291.compiled_manifest
#print axioms Yulang.GeneralSourceMetadataBareBundle291.preserves_input
#print axioms Yulang.GeneralSourceMetadataBareBundle291.reassemble
#print axioms Yulang.GeneralSourceMetadataBareFixture291.raw_role_controls
#print axioms Yulang.GeneralSourceMetadataBareFixture291.well_scoped_not_coverage
#print axioms Yulang.GeneralSourceMetadataBareFixture291.actual_exec

open Yulang GeneralSourceMetadataBareBundle291 GeneralSourceMetadataBareFixture291
#guard (run (forget (GeneralSourceMetadataBundleFixture291.actual true))).map
  GeneralSourceMetadataBundle291.Certificate.ready == some true
#guard (run (forget (GeneralSourceMetadataBundleFixture291.actual false))).map
  GeneralSourceMetadataBundle291.Certificate.ready == some false
#guard !(GeneralSourceMetadataBuildRoles291.build outOfScope).isSome
