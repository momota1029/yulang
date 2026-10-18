"""Offline protocol regressions. All workers/receipts are synthetic fixtures."""
from __future__ import annotations

import copy
import unittest
from pathlib import Path

from agent_sprint import (ASTRA, LUNA, SOL, ProtocolError, SprintModel,
                          digest, exact_path, simulation, validate_current)


class SprintTransitions(unittest.TestCase):
    def setUp(self) -> None:
        self.m = SprintModel("parent", "approved fixture ONLY",
                             ["proof.md", "impl.rs", "aux.md", "leaf1.md", "leaf2.md", "leaf3.md"],
                             astra_total=300, astra_assignments=1,
                             astra_risk="fixture named core risk")
        self.m.begin("fixture-session-1")
        self.m.dependencies["core"] = "v1"

    def proof(self, *, astra: bool = False, deps: bool = False) -> None:
        self.m.assign("P", "proof", ["proof.md"], ["lemma", "apply to parent"],
                      role="astra_prover" if astra else "prover",
                      model=ASTRA if astra else SOL,
                      effort="medium" if astra else "high",
                      seconds=300 if astra else 1800,
                      dependencies={"core": "v1"} if deps else {})
        self.m.launch("P", "fixture-producer", "fixture-launch-P", self.m.session)

    def implementation(self) -> None:
        self.m.assign("I", "implementation", ["impl.rs"], ["source", "propagate", "execute"],
                      role="implementer", model=LUNA, production=True)
        self.m.launch("I", "fixture-implementer", "fixture-launch-I", self.m.session)

    def frozen_proof(self, *, deps: bool = False) -> None:
        self.proof(deps=deps)
        self.m.step("P", "fixture lemma", "parent premise removed")
        self.m.step("P", "fixture parent application", "original conclusion candidate")
        self.m.freeze("P", "a" * 64, ["fixture-producer", "fixture-coauthor"], "fixture-freeze")

    def accepted_proof(self, *, deps: bool = False) -> None:
        self.frozen_proof(deps=deps)
        self.m.review("P", "fixture-fresh-reviewer", "a" * 64, "CLEAN", "fixture-review")
        self.m.integrate("P", "fixture-primary-integration")

    def test_parallel_lanes(self) -> None:
        self.proof(astra=True)
        self.implementation()
        self.assertEqual([j["worker_state"] for j in self.m.jobs.values()], ["RUNNING", "RUNNING"])

    def test_internal_step_continues_same_goal_without_dispatch(self) -> None:
        self.proof(astra=True)
        fixed = self.m.contract_hash
        self.m.step("P", "lemma", "feeds original parent")
        self.assertEqual(self.m.jobs["P"]["cursor"], 1)
        self.assertEqual(self.m.jobs["P"]["worker_state"], "RUNNING")
        self.assertEqual(self.m.contract_hash, fixed)
        self.assertEqual(self.m.consultations, ["START"])
        self.assertFalse(self.m.closed_gates)

    def test_completed_assignment_has_successor_without_replanning(self) -> None:
        self.accepted_proof()
        self.m.stopped("P", "fixture-producer", "fixture-stop")
        self.m.assign("P2", "proof", ["proof.md"], ["next related parent premise"])
        self.m.launch("P2", "fixture-successor", "fixture-launch-P2", self.m.session)
        self.assertEqual(self.m.contract["goal"], "parent")
        self.assertEqual(self.m.consultations, ["START"])
        self.assertFalse(self.m.closed_gates)

    def test_blocked_proof_does_not_stop_independent_implementation(self) -> None:
        self.proof()
        self.implementation()
        self.m.block("P", "unproved foreign case", "fixture-obstruction")
        self.m.step("I", "source path", "reaches constraint generation")
        self.assertEqual(self.m.jobs["P"]["worker_state"], "BLOCKED")
        self.assertEqual(self.m.jobs["I"]["worker_state"], "RUNNING")

    def test_dependent_production_is_not_authorized_by_parallelism(self) -> None:
        with self.assertRaises(ProtocolError):
            self.m.assign("I", "implementation", ["impl.rs"], ["cutover"],
                          role="implementer", model=LUNA, production=True, requires=("parent",))
        self.assertFalse(self.m.jobs)
        self.assertFalse(self.m.leases)

    def test_astra_core_needs_no_prior_sol_failure(self) -> None:
        self.proof(astra=True)
        self.assertEqual(self.m.astra_spent, 300)
        self.assertEqual(self.m.astra_assignments, 1)
        self.assertEqual(self.m.jobs["P"]["requested_model"], ASTRA)
        self.assertEqual(self.m.jobs["P"]["observed_model"], "UNKNOWN")

    def test_global_astra_slot_includes_implementation_escalation(self) -> None:
        self.proof(astra=True)
        with self.assertRaises(ProtocolError):
            self.m.assign("E", "implementation", ["impl.rs"], ["fix"],
                          role="implementation_escalation", model=ASTRA,
                          implementation_evidence="fixture-Luna-obstruction")

    def test_implementation_escalation_requires_luna_evidence(self) -> None:
        with self.assertRaises(ProtocolError):
            self.m.assign("E", "implementation", ["impl.rs"], ["fix"],
                          role="implementation_escalation", model=ASTRA)
        with self.assertRaises(ProtocolError):
            self.m.assign("E", "implementation", ["impl.rs"], ["fix"],
                          role="implementation_escalation", model=ASTRA,
                          implementation_evidence="unlinked Luna note",
                          implementation_handoff_from="missing",
                          implementation_handoff_receipt="unlinked handoff")

    def test_implementation_escalation_requires_frozen_stopped_luna_handoff(self) -> None:
        self.m.assign("L", "implementation", ["impl.rs"], ["inspect and implement"],
                      role="implementer", model=LUNA, effort="high")
        self.m.launch("L", "fixture-luna", "fixture-launch-L", self.m.session)
        self.m.step("L", "fixture Luna evidence", "exact implementation obstruction")
        self.m.stopped("L", "fixture-luna", "fixture-luna-cessation")
        self.m.freeze("L", "a" * 64, ["fixture-luna"], "fixture-luna-freeze")
        with self.assertRaises(ProtocolError):
            self.m.assign("E-bad", "implementation", ["impl.rs"], ["repair obstruction"],
                          role="implementation_escalation", model=ASTRA,
                          implementation_evidence="different artifact hash",
                          implementation_handoff_from="L",
                          implementation_handoff_receipt="fixture-primary-transfer")
        self.m.assign("E", "implementation", ["impl.rs"], ["repair obstruction"],
                      role="implementation_escalation", model=ASTRA,
                      effort="medium", seconds=300,
                      implementation_evidence="L#artifact:sha256:" + "a" * 64,
                      implementation_handoff_from="L",
                      implementation_handoff_receipt="fixture-primary-transfer")
        self.assertEqual(self.m.leases["impl.rs"], "E")

    def test_astra_assignment_and_seconds_caps_persist_across_restart(self) -> None:
        self.m.assign("A0", "proof", ["proof.md"], ["construct"],
                      model=ASTRA, effort="medium", seconds=300)
        self.m.launch("A0", "A0", "fixture-launch-0", self.m.session)
        self.m.stopped("A0", "A0", "fixture-stop-0")
        self.m.pause(end=True)
        self.m.begin("fixture-session-2")
        with self.assertRaises(ProtocolError):
            self.m.assign("A1", "proof", ["proof.md"], ["construct"],
                          model=ASTRA, effort="medium", seconds=1)
        self.assertEqual(self.m.astra_spent, 300)
        self.assertEqual(self.m.astra_assignments, 1)

    def test_astra_defaults_to_zero_and_rejects_long_packets(self) -> None:
        zero = SprintModel("parent", "fixture", ["x"])
        zero.begin("zero-session")
        with self.assertRaises(ProtocolError):
            zero.assign("A", "proof", ["x"], ["risk"], model=ASTRA,
                        effort="medium", seconds=1)
        with self.assertRaises(ProtocolError):
            SprintModel("parent", "fixture", ["x"], astra_total=300,
                        astra_assignments=1)
        with self.assertRaises(ProtocolError):
            self.m.assign("long", "proof", ["proof.md"], ["s1", "s2", "s3", "s4"],
                          model=ASTRA, effort="medium", seconds=300)
        with self.assertRaises(ProtocolError):
            self.m.assign("over-budget", "proof", ["proof.md"], ["risk"],
                          model=ASTRA, effort="medium", seconds=301)

    def test_astra_stages_and_wall_time_are_finite(self) -> None:
        with self.assertRaises(ProtocolError):
            self.m.assign("too-many", "proof", ["proof.md"], ["step"] * 9)
        self.proof(astra=True)
        with self.assertRaises(ProtocolError):
            self.m.step("P", "evidence", "parent", seconds=1801)
        self.assertEqual(self.m.jobs["P"]["cursor"], 0)
        self.assertEqual(self.m.seconds_spent, 0)

    def test_review_capacity_is_reserved(self) -> None:
        for n, path in enumerate(["proof.md", "impl.rs", "aux.md", "leaf1.md"]):
            self.m.assign(str(n), "verification", [path], ["check"], role="researcher")
        with self.assertRaises(ProtocolError):
            self.m.assign("fifth", "proof", ["leaf2.md"], ["proof"])

    def test_overlapping_and_expanded_leases_rejected(self) -> None:
        self.proof()
        for path in ("proof.md", "not-granted.md", "../escape.md", "*.md"):
            with self.subTest(path=path), self.assertRaises(ProtocolError):
                self.m.assign("conflict", "proof", [path], ["proof"])

    def test_frozen_lease_requires_actual_cessation_before_handoff(self) -> None:
        self.frozen_proof()
        with self.assertRaises(ProtocolError):
            self.m.assign("other", "proof", ["proof.md"], ["proof"])
        self.m.stopped("P", "fixture-producer", "fixture-actual-stop")
        self.m.assign("other", "proof", ["proof.md"], ["proof"])
        self.assertEqual(self.m.leases["proof.md"], "other")

    def test_producer_and_coauthor_cannot_review(self) -> None:
        self.frozen_proof()
        for reviewer in ("fixture-producer", "fixture-coauthor"):
            with self.subTest(reviewer=reviewer), self.assertRaises(ProtocolError):
                self.m.review("P", reviewer, "a" * 64, "CLEAN", "fixture-review")
        self.assertIsNone(self.m.jobs["P"]["review"])

    def test_review_requires_isolation_and_exact_revision(self) -> None:
        self.frozen_proof()
        with self.assertRaises(ProtocolError):
            self.m.review("P", "fresh", "b" * 64, "CLEAN", "fixture-review")
        with self.assertRaises(ProtocolError):
            self.m.review("P", "fresh", "a" * 64, "CLEAN", "fixture-review", isolated=False)

    def test_major_cannot_be_overwritten_by_reassurance_review(self) -> None:
        self.frozen_proof()
        self.m.review("P", "fresh", "a" * 64, "MAJOR", "fixture-major")
        with self.assertRaises(ProtocolError):
            self.m.review("P", "other", "a" * 64, "CLEAN", "fixture-reassurance")
        with self.assertRaises(ProtocolError):
            self.m.integrate("P", "fixture-primary")

    def test_missing_review_blocks_integration(self) -> None:
        self.frozen_proof()
        with self.assertRaises(ProtocolError):
            self.m.integrate("P", "fixture-primary")

    def test_conditional_or_test_success_cannot_close_original_parent(self) -> None:
        self.accepted_proof()
        for kind in ("CONDITIONAL", "TEST_PASS"):
            with self.subTest(kind=kind), self.assertRaises(ProtocolError):
                self.m.close_parent("P", "parent", kind=kind,
                                    original_scope=self.m.contract_hash,
                                    source_receipt="fixture-source", native_receipt="fixture-native",
                                    primary_receipt="fixture-primary")
        self.assertFalse(self.m.closed_gates)

    def test_parent_closure_requires_original_scope_and_both_bridges(self) -> None:
        self.accepted_proof()
        with self.assertRaises(ProtocolError):
            self.m.close_parent("P", "parent", kind="PROOF", original_scope="narrower",
                                source_receipt="fixture-source", native_receipt="fixture-native",
                                primary_receipt="fixture-primary")
        with self.assertRaises(ProtocolError):
            self.m.close_parent("P", "parent", kind="PROOF", original_scope=self.m.contract_hash,
                                source_receipt="", native_receipt="fixture-native",
                                primary_receipt="fixture-primary")

    def test_dependency_invalidation_is_lane_local_and_invalidates_review(self) -> None:
        self.accepted_proof(deps=True)
        self.m.close_parent("P", "parent", kind="PROOF", original_scope=self.m.contract_hash,
                            source_receipt="fixture-source", native_receipt="fixture-native",
                            primary_receipt="fixture-primary")
        self.implementation()
        self.m.invalidate("core", "v2")
        self.assertEqual(self.m.jobs["P"]["status"], "STALE")
        self.assertIsNone(self.m.jobs["P"]["review"])
        self.assertNotIn("parent", self.m.closed_gates)
        self.assertEqual(self.m.jobs["I"]["worker_state"], "RUNNING")

    def test_capacity_failure_has_three_identical_attempts_not_fake_running(self) -> None:
        self.m.assign("P", "proof", ["proof.md"], ["proof"])
        for i in range(3):
            self.m.launch_failed("P", "capacity")
            self.assertNotEqual(self.m.jobs["P"]["worker_state"], "RUNNING")
            self.assertEqual(self.m.jobs["P"]["requested_model"], SOL)
        self.assertEqual(self.m.jobs["P"]["status"], "FAILED")
        with self.assertRaises(ProtocolError):
            self.m.launch_failed("P", "capacity")

    def test_persistent_and_permission_errors_do_not_retry(self) -> None:
        for reason in ("unsupported", "rate", "auth", "permission"):
            m = SprintModel("parent", "fixture", ["x"])
            m.begin("s")
            m.assign("P", "proof", ["x"], ["proof"])
            m.launch_failed("P", reason)
            self.assertEqual(m.jobs["P"]["attempts"], 1)
            self.assertEqual(m.jobs["P"]["status"], "FAILED")

    def test_missing_worker_id_never_establishes_running(self) -> None:
        self.m.assign("P", "proof", ["proof.md"], ["proof"])
        with self.assertRaises(ProtocolError):
            self.m.launch("P", "", "success-but-no-id", self.m.session)
        self.assertEqual(self.m.jobs["P"]["worker_state"], "NOT_STARTED")
        self.assertIn("proof.md", self.m.leases)

    def test_known_model_mismatch_preserves_real_worker_and_quarantines_lease(self) -> None:
        self.m.assign("I", "implementation", ["impl.rs"], ["code"], role="implementer", model=LUNA)
        self.m.launch("I", "actual-wrong-model-worker", "fixture-launch", self.m.session, observed_model=SOL)
        j = self.m.jobs["I"]
        self.assertEqual(j["status"], "ROUTING_MISMATCH")
        self.assertEqual(j["worker_state"], "UNKNOWN")
        self.assertEqual(j["observed_model"], SOL)
        self.assertEqual(j["worker_id"], "actual-wrong-model-worker")
        self.assertEqual(self.m.leases["impl.rs"], "I")
        with self.assertRaises(ProtocolError):
            self.m.launch_failed("I", "unsupported")

    def test_unexpected_observed_astra_consumes_full_grant(self) -> None:
        self.m.assign("P", "proof", ["proof.md"], ["risk"], seconds=300)
        self.m.launch("P", "actual-astra-worker", "fixture-launch",
                      self.m.session, observed_model=ASTRA)
        self.assertEqual(self.m.jobs["P"]["worker_state"], "UNKNOWN")
        self.assertEqual(self.m.jobs["P"]["status"], "ROUTING_MISMATCH")
        self.assertEqual(self.m.astra_spent, 300)
        self.assertEqual(self.m.astra_assignments, 1)

    def test_implementation_cannot_silently_downgrade_to_sol(self) -> None:
        with self.assertRaises(ProtocolError):
            self.m.assign("I", "implementation", ["impl.rs"], ["code"], role="implementer", model=SOL)

    def test_stop_clears_running_but_does_not_invent_stopped_or_free_leases(self) -> None:
        self.proof(astra=True)
        self.implementation()
        before = len(self.m.consultations)
        self.m.pause()
        self.assertTrue(all(j["worker_state"] == "UNKNOWN" for j in self.m.jobs.values()))
        self.assertEqual(len(self.m.leases), 2)
        self.assertEqual(len(self.m.consultations), before)

    def test_session_end_resume_does_not_resurrect_workers(self) -> None:
        self.proof(astra=True)
        self.m.step("P", "lemma", "parent", seconds=12)
        self.m.pause(end=True)
        self.m.begin("fixture-session-2")
        self.assertEqual(self.m.jobs["P"]["worker_state"], "UNKNOWN")
        self.assertEqual(self.m.jobs["P"]["spent"], 12)
        self.assertEqual(self.m.astra_spent, 300)
        with self.assertRaises(ProtocolError):
            self.m.assign("another-astra", "proof", ["aux.md"], ["proof"], model=ASTRA)

    def test_fresh_resume_receipt_continues_same_assignment_without_budget_reset(self) -> None:
        self.proof(astra=True)
        self.m.step("P", "lemma", "parent", seconds=12)
        self.m.pause(end=True)
        self.m.begin("fixture-session-2")
        with self.assertRaises(ProtocolError):
            self.m.resume_worker("P", "fixture-producer", "fixture-launch-P", self.m.session)
        self.m.resume_worker("P", "fixture-producer", "fixture-resume-P", self.m.session)
        self.assertEqual(self.m.jobs["P"]["cursor"], 1)
        self.assertEqual(self.m.jobs["P"]["spent"], 12)
        self.assertEqual(self.m.astra_spent, 300)
        self.m.step("P", "application", "parent reduced further")

    def test_blocked_resume_needs_resolution(self) -> None:
        self.proof()
        self.m.block("P", "missing premise", "fixture-block")
        with self.assertRaises(ProtocolError):
            self.m.resume_worker("P", "fixture-producer", "fixture-resume", self.m.session)
        self.m.resume_worker("P", "fixture-producer", "fixture-resume", self.m.session,
                             unblock_receipt="fixture-established-premise")

    def test_stale_session_cannot_launch_reserved_work(self) -> None:
        self.m.assign("P", "proof", ["proof.md"], ["proof"])
        self.m.pause(end=True)
        self.m.begin("fixture-session-2")
        with self.assertRaises(ProtocolError):
            self.m.launch("P", "worker", "old receipt", "fixture-session-1")
        self.m.cancel_unstarted("P", "fixture-confirmed-never-launched")
        self.assertFalse(self.m.leases)

    def test_unknown_cannot_be_cancelled_as_never_launched(self) -> None:
        self.proof()
        self.m.pause()
        with self.assertRaises(ProtocolError):
            self.m.cancel_unstarted("P", "pretend no launch")

    def test_descendants_must_stop_before_parent_lease_reclamation(self) -> None:
        self.m.assign("C", "proof", ["proof.md"], ["combine"], coordinator=True,
                      leaf_paths=("leaf1.md", "leaf2.md", "leaf3.md"))
        self.m.launch("C", "coordinator", "fixture-launch-C", self.m.session)
        for n in (1, 2):
            self.m.assign(f"L{n}", "proof", [f"leaf{n}.md"], ["lemma"], parent="C")
            self.m.launch(f"L{n}", f"leaf{n}", f"fixture-launch-L{n}", self.m.session)
        with self.assertRaises(ProtocolError):
            self.m.assign("L3", "proof", ["leaf3.md"], ["lemma"], parent="C")
        with self.assertRaises(ProtocolError):
            self.m.stopped("C", "coordinator", "fixture-stop-C")
        self.m.pause(end=True)
        for n in (1, 2):
            self.m.stopped(f"L{n}", f"leaf{n}", f"fixture-stop-L{n}")
        self.m.stopped("C", "coordinator", "fixture-stop-C")
        self.assertFalse(self.m.leases)

    def test_leaf_delegation_requires_explicit_coordinator_authority(self) -> None:
        self.proof()
        with self.assertRaises(ProtocolError):
            self.m.assign("leaf", "proof", ["leaf1.md"], ["lemma"], parent="P")

    def test_handoff_ack_is_idempotent_and_revisions_are_frozen(self) -> None:
        body = {"parent": "parent", "result": "conditional"}
        self.assertTrue(self.m.receive("handoff", 1, body, digest(body)))
        self.assertFalse(self.m.receive("handoff", 1, body, digest(body)))
        changed = {"parent": "parent", "result": "different"}
        with self.assertRaises(ProtocolError):
            self.m.receive("handoff", 1, changed, digest(changed))
        with self.assertRaises(ProtocolError):
            self.m.receive("handoff", 3, changed, digest(changed))
        self.assertTrue(self.m.receive("handoff", 2, changed, digest(changed)))

    def test_contract_mutation_cannot_silently_retarget_parent(self) -> None:
        self.proof()
        self.m.contract["goal"] = "easier theorem"
        with self.assertRaises(ProtocolError):
            self.m.step("P", "lemma", "pretend original parent")

    def test_minor_events_do_not_trigger_dispatch(self) -> None:
        for event in ("LEMMA", "TEST", "COMMIT", "RESULT", "REVIEW_RECEIPT"):
            self.assertFalse(self.m.consult(event))
        self.assertEqual(self.m.consultations, ["START"])
        self.assertTrue(self.m.consult("COUNTEREXAMPLE"))

    def test_unreconciled_legacy_cannot_activate(self) -> None:
        m = SprintModel("parent", "fixture", ["x"], reconciled=False)
        with self.assertRaises(ProtocolError):
            m.begin("fixture-session")

    def test_source_counterexample_resolves_research_but_never_proves_prerequisite(self) -> None:
        self.accepted_proof()
        self.m.close_parent("P", "parent", kind="SOURCE_QUALIFIED_COUNTEREXAMPLE",
                            original_scope=self.m.contract_hash, source_receipt="fixture-source",
                            native_receipt="fixture-native", primary_receipt="fixture-primary")
        self.assertIn("parent", self.m.refuted_gates)
        self.assertNotIn("parent", self.m.closed_gates)
        with self.assertRaises(ProtocolError):
            self.m.assign("I", "implementation", ["impl.rs"], ["cutover"],
                          role="implementer", model=LUNA, production=True, requires=("parent",))

    def test_revoked_proof_invalidates_only_dependent_production(self) -> None:
        self.accepted_proof(deps=True)
        self.m.close_parent("P", "parent", kind="PROOF", original_scope=self.m.contract_hash,
                            source_receipt="fixture-source", native_receipt="fixture-native",
                            primary_receipt="fixture-primary")
        self.m.assign("I", "implementation", ["impl.rs"], ["cutover"],
                      role="implementer", model=LUNA, production=True, requires=("parent",))
        self.m.launch("I", "fixture-I", "fixture-launch-I", self.m.session)
        self.m.assign("independent", "verification", ["aux.md"], ["check"], role="researcher")
        self.m.launch("independent", "fixture-independent", "fixture-launch-independent", self.m.session)
        self.m.invalidate("core", "v2")
        self.assertEqual(self.m.jobs["I"]["status"], "STALE")
        self.assertEqual(self.m.jobs["I"]["worker_state"], "UNKNOWN")
        self.assertEqual(self.m.leases["impl.rs"], "I")
        self.assertEqual(self.m.jobs["independent"]["worker_state"], "RUNNING")
        with self.assertRaises(ProtocolError):
            self.m.step("I", "stale code", "invalid parent")

    def test_mutated_contract_cannot_close_original_gate(self) -> None:
        self.accepted_proof()
        self.m.contract["authority"] = "silently replaced"
        with self.assertRaises(ProtocolError):
            self.m.close_parent("P", "parent", kind="PROOF", original_scope=self.m.contract_hash,
                                source_receipt="fixture-source", native_receipt="fixture-native",
                                primary_receipt="fixture-primary")

    def test_simulation_is_explicit_and_has_no_live_claim(self) -> None:
        lines = simulation()
        self.assertIn("SIMULATION ONLY", lines[0])
        self.assertIn("no automatic RUNNING", lines[-1])
        self.assertEqual(self.m.snapshot()["mode"], "SIMULATION")


class SnapshotValidation(unittest.TestCase):
    def setUp(self) -> None:
        self.s = {"schema_version": 1, "mode": "LIVE", "phase": "ACTIVE", "session": "s1",
                  "workers": [{"id": "actual-worker", "state": "RUNNING", "session": "s1",
                               "receipt": "actual-tool-receipt", "requested_model": ASTRA,
                               "observed_model": "UNKNOWN", "requested_effort": "medium",
                               "observed_effort": "UNKNOWN"}],
                  "leases": [{"path": "proof.md", "owner": "actual-worker", "state": "HELD"}],
                  "pending": [], "legacy_reconciliation": {"required": False}}

    def test_current_live_receipt_structure(self) -> None:
        validate_current(self.s)  # Structure only: not authentication of this fixture.

    def test_running_is_forbidden_after_end_or_in_simulation_or_without_receipt(self) -> None:
        for field, value in (("phase", "ENDED"), ("mode", "SIMULATION"), ("session", "s2")):
            s = copy.deepcopy(self.s)
            s[field] = value
            with self.subTest(field=field), self.assertRaises(ProtocolError):
                validate_current(s)
        del self.s["workers"][0]["receipt"]
        with self.assertRaises(ProtocolError):
            validate_current(self.s)

    def test_unknown_retains_lease_without_running_claim(self) -> None:
        self.s["phase"] = "ENDED"
        self.s["workers"][0]["state"] = "UNKNOWN"
        self.s["leases"][0]["state"] = "QUARANTINED"
        validate_current(self.s)

    def test_lease_conflicts_and_omitted_owner_rejected(self) -> None:
        s = copy.deepcopy(self.s)
        s["leases"].append(copy.deepcopy(s["leases"][0]))
        with self.assertRaises(ProtocolError):
            validate_current(s)
        self.s["leases"][0]["owner"] = "missing"
        with self.assertRaises(ProtocolError):
            validate_current(self.s)

    def test_history_growth_and_legacy_activation_rejected(self) -> None:
        s = copy.deepcopy(self.s)
        s["pending"] = list(range(33))
        with self.assertRaises(ProtocolError):
            validate_current(s)
        self.s["legacy_reconciliation"]["required"] = True
        with self.assertRaises(ProtocolError):
            validate_current(self.s)

    def test_known_model_or_effort_mismatch_is_not_running(self) -> None:
        for key, value in (("observed_model", SOL), ("observed_effort", "low")):
            state = copy.deepcopy(self.s)
            state["workers"][0][key] = value
            with self.subTest(key=key), self.assertRaises(ProtocolError):
                validate_current(state)

    def test_omitted_effort_is_not_unknown(self) -> None:
        del self.s["workers"][0]["observed_effort"]
        with self.assertRaises(ProtocolError):
            validate_current(self.s)

    def test_pending_policy_review_blocks_live_adoption(self) -> None:
        self.s["pending"] = [{"id": "INDEPENDENT-REVIEW", "state": "NOT_RUN"}]
        with self.assertRaises(ProtocolError):
            validate_current(self.s)
        self.s["phase"] = "RECONCILE"
        self.s["workers"][0]["state"] = "UNKNOWN"
        self.s["leases"][0]["state"] = "QUARANTINED"
        validate_current(self.s)

    def test_exact_paths_reject_aliases_and_globs(self) -> None:
        for path in ("", "/abs", "a//b", "./x", "a/../x", "a\\b", "x*", "x?"):
            self.assertFalse(exact_path(path), path)
        self.assertTrue(exact_path("notes/proof.md"))


class AmbitiousDispatcherPolicy(unittest.TestCase):
    """Static contract assertions; no Sol invocation or empirical quality claim."""

    @classmethod
    def setUpClass(cls) -> None:
        root = Path(__file__).resolve().parents[1]
        cls.selector = (root / ".codex/agents/next-action-selector.toml").read_text()
        cls.sprints = (root / "rules/goal-driven-sprints.md").read_text()
        cls.routing = (root / ".agents/skills/yulang-next-action/SKILL.md").read_text()

    def test_one_dispatch_contains_four_expert_questions(self) -> None:
        for key in ("Altitude:", "Depth:", "Range:", "Independent verification:"):
            self.assertIn(key, self.selector)
        for key in ("Altitude", "Depth", "Range", "independent verification"):
            self.assertIn(key, self.routing.lower() if key == "independent verification" else self.routing)
        self.assertIn("same dispatch", self.selector)
        self.assertIn("Only at an actual dispatcher boundary", self.sprints)

    def test_original_parent_and_permission_are_preserved(self) -> None:
        for key in ("unchanged original", "within-contract", "beyond-contract",
                    "Luna", "original quantifiers", "write leases"):
            self.assertIn(key, self.sprints)
        self.assertIn("No speculative goal", self.selector)
        self.assertIn("only luna can approve", self.selector.lower())

    def test_decision_is_about_progress_and_falsifiability(self) -> None:
        for key in ("genuine parent", "critical path", "falsifier", "review seam",
                    "both independent lanes"):
            self.assertIn(key, self.sprints)
        self.assertIn("do not invent alternatives", self.selector.lower())
        self.assertIn("Tests never", self.sprints)

    def test_no_second_planner_or_changed_cadence(self) -> None:
        self.assertIn("This check adds no", self.sprints)
        self.assertIn("no mandatory read, reviewer or per-step consultation", self.sprints)
        self.assertIn("No agent launch/contact", self.selector)
        self.assertIn("An internal lemma, test, ordinary result", self.routing)


if __name__ == "__main__":
    unittest.main()
