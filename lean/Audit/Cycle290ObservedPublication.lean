import Yulang.GeneralObservedMetadataReleased290

#print axioms Yulang.GeneralObservedMetadataBook290.book_exact
#print axioms Yulang.GeneralObservedMetadataBook290.keys_exact
#print axioms Yulang.GeneralObservedMetadataRequestBook290.matches_request
#print axioms Yulang.GeneralObservedMetadataRequestBook290.actual_alias_gains_request_book
#print axioms Yulang.GeneralObservedMetadataSeal290.membership
#print axioms Yulang.GeneralObservedMetadataSeal290.kept_has_reference_books
#print axioms Yulang.GeneralObservedMetadataPublication290.publishFrom_exact
#print axioms Yulang.GeneralObservedMetadataPublication290.issue_is_current
#print axioms Yulang.GeneralObservedMetadataPublication290.ready_release
#print axioms Yulang.GeneralObservedMetadataReleaseFixture290.actual_class_book
#print axioms Yulang.GeneralObservedMetadataReleaseFixture290.accepted_seals
#print axioms Yulang.GeneralObservedMetadataReleaseFixture290.pending_seals
#print axioms Yulang.GeneralObservedMetadataReleaseFixture290.missing_request_same_metadata
#print axioms Yulang.GeneralObservedMetadataReleaseFixture290.executable_release_expected
#print axioms Yulang.GeneralObservedMetadataReleaseFixture290.actual_replay
#print axioms Yulang.GeneralObservedMetadataReleased290.released_exact
#print axioms Yulang.GeneralObservedMetadataReleased290.public_models
#print axioms Yulang.GeneralObservedMetadataReleased290.bounded_release_still_does_not_imply_global_metadata

open Yulang GeneralObservedMetadataReleaseFixture290
open Yulang.GeneralObservedMetadataPublication290 (publishFrom)
open Yulang.GeneralRebaseRowChildSource287 (root)
open Yulang.GeneralRebaseReceiptFixture289 (request)
open Yulang.GeneralRebaseReceiptCompile289 (actualMark)

#guard publishFrom [normalized] root (request true) normalized == .released actualMark
#guard publishFrom [normalized] root (request true) wrongHead == .staleOrUnsupported
#guard publishFrom [normalized] root (request true) wrongHistory == .staleOrUnsupported
#guard publishFrom [normalized] root (request true) lostRequest == .staleOrUnsupported
