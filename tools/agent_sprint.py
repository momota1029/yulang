#!/usr/bin/env python3
"""Offline sprint protocol model and static checker; NEVER starts an agent.

Receipts in this model are test inputs, not authenticated runtime evidence.
The primary must inspect real tools, semantics, dependencies and permissions.
Python 3.11+; standard library only. No network, subprocess or repository writes.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys
import tomllib
from typing import Any

POLICY = "rules/goal-driven-sprints.md"
ASTRA = "gpt-6-astra"
LUNA = "gpt-6-luna"
SOL = "gpt-6.1-sol"
BOUNDARIES = frozenset({"START", "END", "BLOCKER", "COUNTEREXAMPLE",
                        "AUTHORITY", "DEPENDENCY", "LEASE", "RESOURCE",
                        "INTEGRATION", "REPLAN"})
WORKER_STATES = frozenset({"NOT_STARTED", "RUNNING", "WAITING", "BLOCKED",
                           "STOPPED", "UNKNOWN"})
LIMIT_BYTES = 16 * 1024


class ProtocolError(ValueError):
    """A transition would violate the declared coordination contract."""


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ProtocolError(message)


def digest(value: Any) -> str:
    data = json.dumps(value, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=False).encode("utf-8")
    return hashlib.sha256(data).hexdigest()


def exact_path(value: str) -> bool:
    return (isinstance(value, str) and bool(value) and
            not any(c in value for c in "*?[]\\\x00") and
            not PurePosixPath(value).is_absolute() and
            all(p not in {"", ".", ".."} for p in value.split("/")))


def is_astra(job: dict[str, Any]) -> bool:
    # Unobserved requested Astra still reserves the costly-model slot.
    return ASTRA in {job["requested_model"], job["observed_model"]}


class SprintModel:
    """Deterministic SIMULATION only. Mutable operations validate before writing.

    A job is one bounded continuation envelope, not one lemma. Mathematical
    validity is deliberately not decided here. Production/claim acceptance
    needs explicit independent evidence; this model checks only its structure.
    """

    def __init__(self, goal: str, authority: str, paths: list[str], *,
                 agents: int = 6, astra_total: int = 2,
                 wall_seconds: int = 7200, reconciled: bool = True) -> None:
        require(bool(goal) and bool(authority), "fixed goal and authority required")
        require(3 <= agents <= 12 and 1 <= astra_total <= 2, "invalid resource cap")
        require(0 < wall_seconds <= 7200, "invalid sprint wall budget")
        require(all(exact_path(p) for p in paths), "exact repo-relative paths required")
        self.contract = {"goal": goal, "authority": authority, "paths": sorted(set(paths)),
                         "agents": agents, "astra_total": astra_total,
                         "wall_seconds": wall_seconds}
        self.contract_hash = digest(self.contract)
        self.reconciled = reconciled
        self.session: str | None = None
        self.sessions: set[str] = set()
        self.phase = "NOT_STARTED"
        self.jobs: dict[str, dict[str, Any]] = {}
        self.leases: dict[str, str] = {}
        self.dependencies: dict[str, str] = {}
        self.closed_gates: set[str] = set()  # PROVED only; never refuted.
        self.refuted_gates: set[str] = set()
        self.gate_owners: dict[str, str] = {}
        self.astra_spent = 0
        self.seconds_spent = 0
        self.consultations: list[str] = []
        self.intake: dict[tuple[str, int], str] = {}

    def _contract(self) -> None:
        require(digest(self.contract) == self.contract_hash, "contract changed: replan required")

    def consult(self, event: str) -> bool:
        self._contract()
        if event not in BOUNDARIES:
            return False
        self.consultations.append(event)
        return True

    def begin(self, session: str) -> None:
        self._contract()
        require(self.reconciled, "legacy writers/leases need live reconciliation")
        require(self.phase in {"NOT_STARTED", "PAUSED", "ENDED"}, "session already active")
        require(bool(session) and session not in self.sessions, "fresh session ID required")
        self.session = session
        self.sessions.add(session)
        self.phase = "ACTIVE"
        if not self.consultations:
            self.consult("START")
        # Deliberately do NOT resurrect workers or reset resources on resume.

    def _slots(self) -> list[dict[str, Any]]:
        return [j for j in self.jobs.values()
                if j["worker_state"] != "STOPPED" and j["status"] != "FAILED"]

    def assign(self, ident: str, lane: str, paths: list[str], steps: list[str], *,
               role: str = "prover", model: str = SOL, effort: str = "high",
               production: bool = False, requires: tuple[str, ...] = (),
               dependencies: dict[str, str] | None = None,
               seconds: int = 1800, parent: str | None = None,
               implementation_evidence: str | None = None,
               implementation_handoff_from: str | None = None,
               implementation_handoff_receipt: str | None = None,
               coordinator: bool = False, leaf_paths: tuple[str, ...] = ()) -> None:
        self._contract()
        require(self.phase == "ACTIVE", "no active session")
        require(ident not in self.jobs and bool(ident), "assignment ID must be unique")
        require(lane in {"proof", "implementation", "verification"}, "unknown lane")
        require(role in {"prover", "astra_prover", "implementer",
                         "implementation_escalation", "researcher"}, "unknown role")
        require(bool(steps) and len(steps) <= 8 and all(steps), "finite nonempty stage plan required")
        require(0 < seconds <= 1800 and effort in {"low", "medium", "high"}, "invalid assignment budget")
        require(bool(paths) and len(paths) == len(set(paths)), "exact unique leases required")
        require(all(exact_path(p) and p in self.contract["paths"] for p in paths), "lease outside contract")
        require(not any(p in self.leases for p in paths), "lease conflict, including frozen/unknown writer")
        require(len(self._slots()) < self.contract["agents"] - 2, "reserve review/integration capacity")
        require(not production or set(requires) <= self.closed_gates, "open dependent production gate")
        require(not production or lane == "implementation", "production belongs to implementation")
        require(lane != "implementation" or role in {"implementer", "implementation_escalation"}, "invalid implementation role")
        require(role != "implementer" or (lane == "implementation" and model == LUNA and effort == "high"), "Luna/high implementation floor")
        require(role != "astra_prover" or (lane == "proof" and model == ASTRA), "Astra proof role has no production rights")
        require(role != "implementation_escalation" or
                (lane == "implementation" and model == ASTRA and
                 bool(implementation_evidence) and
                 bool(implementation_handoff_receipt) and
                 implementation_handoff_from in self.jobs),
                "Astra implementation needs Luna evidence and an acknowledged handoff")
        if role == "implementation_escalation":
            prior = self.jobs[implementation_handoff_from]
            require(prior["lane"] == "implementation" and prior["role"] == "implementer" and
                    prior["requested_model"] == LUNA and prior["requested_effort"] == "high",
                    "Astra implementation handoff must originate from Luna/high")
            require(prior["worker_state"] == "STOPPED" and bool(prior["stop_receipt"]) and
                    prior["artifact"] is not None and prior["status"] in {"REVIEW", "DONE"},
                    "Luna artifact must be frozen and writer cessation confirmed")
            require(implementation_evidence ==
                    f"{implementation_handoff_from}#artifact:sha256:{prior['artifact']['sha256']}",
                    "Luna evidence must identify the frozen source artifact")
            require(set(paths) <= set(prior["paths"]),
                    "Astra implementation handoff cannot expand the Luna lease")
        require(lane != "implementation" or model in {LUNA, ASTRA}, "no Sol implementation fallback")
        deps = dict(dependencies or {})
        require(all(self.dependencies.get(k) == v for k, v in deps.items()), "stale dependency")
        require(not coordinator or (parent is None and lane == "proof" and bool(leaf_paths)),
                "explicit root proof-coordinator grant required")
        require(all(exact_path(p) and p in self.contract["paths"] and p not in paths
                    for p in leaf_paths), "leaf outputs must be preallocated and disjoint")
        if parent is not None:
            require(parent in self.jobs and self.jobs[parent]["parent"] is None,
                    "only one proof-coordinator level")
            parent_job = self.jobs[parent]
            require(parent_job["coordinator"] and parent_job["lane"] == "proof" and parent_job["worker_state"] == "RUNNING",
                    "live authorized proof coordinator required")
            require(set(paths) <= set(parent_job["leaf_paths"]), "leaf lease not preallocated")
            require(lane in {"proof", "verification"} and role in {"prover", "researcher"},
                    "leaf role outside proof exception")
            require(sum(j["parent"] == parent and j in self._slots()
                        for j in self.jobs.values()) < 2, "at most two active leaves")
        if model == ASTRA:
            require(not any(is_astra(j) for j in self._slots()), "one global Astra slot")
            require(self.astra_spent < self.contract["astra_total"], "Astra sprint budget exhausted")
        job = {"id": ident, "lane": lane, "role": role, "paths": list(paths),
               "steps": list(steps), "cursor": 0, "status": "ASSIGNED",
               "worker_state": "NOT_STARTED", "worker_id": None,
               "requested_model": model, "observed_model": "UNKNOWN",
               "requested_effort": effort, "observed_effort": "UNKNOWN",
               "session": self.session, "receipt": None, "attempts": 0,
               "dependencies": deps, "requires": list(requires),
               "production": production, "seconds": seconds, "spent": 0,
               "evidence": [], "artifact": None, "review": None,
               "parent": parent, "coordinator": coordinator, "leaf_paths": list(leaf_paths),
               "stop_receipt": None, "stale": False}
        self.jobs[ident] = job
        self.leases.update({p: ident for p in paths})
        self.astra_spent += int(model == ASTRA)

    def launch(self, ident: str, worker: str, receipt: str, session: str, *,
               observed_model: str = "UNKNOWN", observed_effort: str = "UNKNOWN") -> None:
        self._contract()
        j = self.jobs[ident]
        require(self.phase == "ACTIVE" and session == self.session == j["session"], "stale session receipt")
        require(j["status"] == "ASSIGNED" and j["attempts"] < 3, "not launchable")
        require(bool(worker) and bool(receipt), "actual worker and receipt required")
        require(not any(x["worker_id"] == worker and x["worker_state"] != "STOPPED"
                        for x in self.jobs.values()), "duplicate live worker")
        mismatch = (observed_model not in {"UNKNOWN", j["requested_model"]} or
                    observed_effort not in {"UNKNOWN", j["requested_effort"]})
        # A returned worker may be alive even on a routing mismatch. Keep its ID,
        # observed model and quarantined lease rather than pretending launch failed.
        j.update(worker_id=worker, receipt=receipt,
                 worker_state="UNKNOWN" if mismatch else "RUNNING",
                 status="ROUTING_MISMATCH" if mismatch else "RUNNING",
                 observed_model=observed_model, observed_effort=observed_effort)
        j["attempts"] += 1

    def resume_worker(self, ident: str, worker: str, receipt: str, session: str, *,
                      unblock_receipt: str | None = None) -> None:
        self._contract()
        j = self.jobs[ident]
        require(self.phase == "ACTIVE" and session == self.session and bool(receipt),
                "fresh current-session resume receipt required")
        require(worker == j["worker_id"] and bool(worker), "actual worker identity required")
        require(j["worker_state"] in {"UNKNOWN", "BLOCKED", "WAITING"} and
                j["status"] not in {"ROUTING_MISMATCH", "STALE"} and not j["stale"],
                "worker is not eligible for same-contract resumption")
        require(j["cursor"] < len(j["steps"]) and j["spent"] < j["seconds"], "assignment already exhausted")
        require(j["status"] != "BLOCKED" or bool(unblock_receipt), "blocker resolution required")
        require(all(self.leases.get(p) == ident for p in j["paths"]), "lease was transferred")
        require(all(self.dependencies.get(k) == v for k, v in j["dependencies"].items()), "stale dependency")
        require(receipt != j["receipt"], "old receipt cannot resurrect a worker")
        j.update(session=session, receipt=receipt, worker_state="RUNNING", status="RUNNING")

    def launch_failed(self, ident: str, reason: str) -> None:
        j = self.jobs[ident]
        require(j["status"] == "ASSIGNED", "not awaiting launch")
        require(reason in {"capacity", "unsupported", "rate", "auth", "permission"}, "unknown failure category")
        j["attempts"] += 1
        if reason != "capacity" or j["attempts"] >= 3:
            j.update(status="FAILED", worker_state="STOPPED")
            for p in j["paths"]:
                self.leases.pop(p)
        # No model switch; another assignment needs its own authorization/quota.

    def cancel_unstarted(self, ident: str, no_launch_receipt: str) -> None:
        j = self.jobs[ident]
        require(j["status"] == "ASSIGNED" and j["worker_id"] is None and bool(no_launch_receipt),
                "positive no-launch evidence required; unknown workers are not unstarted")
        j.update(status="FAILED", worker_state="STOPPED", stop_receipt=no_launch_receipt)
        for p in j["paths"]:
            self.leases.pop(p)

    def step(self, ident: str, evidence: str, parent_effect: str, *, seconds: int = 1) -> None:
        self._contract()
        j = self.jobs[ident]
        require(self.phase == "ACTIVE" and j["worker_state"] == "RUNNING" and not j["stale"], "not running on valid inputs")
        require(j["cursor"] < len(j["steps"]), "all stages already finished")
        require(bool(evidence) and bool(parent_effect), "evidence and parent application/reduced premise required")
        require(seconds >= 0 and j["spent"] + seconds <= j["seconds"] and
                self.seconds_spent + seconds <= self.contract["wall_seconds"], "stop: resource budget reached")
        j["cursor"] += 1
        j["spent"] += seconds
        self.seconds_spent += seconds
        j["evidence"].append({"locator": evidence, "parent_effect": parent_effect})
        # Same job, goal and lease; no dispatcher, commit or closure implied.
        if j["cursor"] == len(j["steps"]):
            j["worker_state"] = "WAITING"
            j["status"] = "RESULT"

    def block(self, ident: str, missing: str, receipt: str) -> None:
        j = self.jobs[ident]
        require(j["worker_state"] == "RUNNING" and bool(missing) and bool(receipt), "blocker evidence required")
        j.update(status="BLOCKED", worker_state="BLOCKED", blocker=missing, receipt=receipt)
        self.consult("BLOCKER")
        # Other lane and its stable dependencies are untouched.

    def freeze(self, ident: str, artifact_hash: str, authors: list[str], receipt: str) -> None:
        j = self.jobs[ident]
        require(j["status"] in {"RESULT", "BLOCKED"} and not j["stale"], "no stable coherent result")
        require(bool(receipt) and re.fullmatch(r"[0-9a-f]{64}", artifact_hash) is not None, "frozen hash and cessation receipt required")
        require(j["worker_id"] in authors and all(authors), "all authors, including producer, required")
        require(not any(x["parent"] == ident and x["worker_state"] != "STOPPED"
                        for x in self.jobs.values()), "freeze all contributing descendants first")
        j.update(status="REVIEW", worker_state="STOPPED" if j["worker_state"] == "STOPPED" else "WAITING",
                 artifact={"sha256": artifact_hash, "authors": sorted(set(authors)),
                           "dependencies": dict(j["dependencies"])}, stop_receipt=receipt)

    def review(self, ident: str, reviewer: str, artifact_hash: str, verdict: str,
               receipt: str, *, isolated: bool = True) -> None:
        j = self.jobs[ident]
        require(j["status"] == "REVIEW" and not j["stale"], "target is not a stable review candidate")
        require(bool(reviewer) and reviewer not in j["artifact"]["authors"] and isolated, "fresh independent reviewer required")
        require(artifact_hash == j["artifact"]["sha256"] and bool(receipt), "review hash/receipt mismatch")
        require(verdict in {"CLEAN", "BLOCKING", "MAJOR", "MINOR"}, "unknown review verdict")
        require(j["review"] is None, "do not overwrite a frozen revision review; repair/adjudicate first")
        j["review"] = {"reviewer": reviewer, "sha256": artifact_hash,
                       "verdict": verdict, "receipt": receipt}

    def integrate(self, ident: str, receipt: str) -> None:
        self._contract()
        j = self.jobs[ident]
        require(j["status"] == "REVIEW" and not j["stale"] and bool(receipt), "stable primary integration receipt required")
        require(j["review"] is not None and j["review"]["verdict"] == "CLEAN", "required independent review not clean")
        require(all(self.dependencies.get(k) == v for k, v in j["dependencies"].items()), "dependency changed since review")
        j.update(status="DONE", integration_receipt=receipt)
        # No automatic parent proof/source/production promotion.

    def close_parent(self, ident: str, gate: str, *, kind: str,
                     original_scope: str, source_receipt: str, native_receipt: str,
                     primary_receipt: str) -> None:
        self._contract()
        j = self.jobs[ident]
        require(j["status"] == "DONE" and j["lane"] == "proof" and not j["stale"], "integrated proof evidence required")
        require(kind in {"PROOF", "SOURCE_QUALIFIED_COUNTEREXAMPLE"}, "tests/conditional lemmas cannot close parent")
        require(original_scope == self.contract_hash and bool(source_receipt) and
                bool(native_receipt) and bool(primary_receipt), "original scope and all independent bridge receipts required")
        require(gate == self.contract["goal"], "cannot close a different original parent")
        if kind == "PROOF":
            require(gate not in self.refuted_gates, "contradictory evidence needs authority adjudication")
            self.closed_gates.add(gate)
        else:
            self.closed_gates.discard(gate)
            self.refuted_gates.add(gate)
            self._invalidate_required_gates()
            self.consult("COUNTEREXAMPLE")
        self.gate_owners[gate] = ident

    def _mark_stale(self, job: dict[str, Any]) -> None:
        job["stale"] = True
        job["review"] = None
        if job["worker_state"] != "STOPPED":
            job["worker_state"] = "UNKNOWN"
        job["status"] = "STALE"
        for gate, owner in self.gate_owners.items():
            if owner == job["id"]:
                self.closed_gates.discard(gate)
                self.refuted_gates.discard(gate)

    def _invalidate_required_gates(self) -> None:
        # A proof prerequisite may be revoked after dependent work was assigned.
        # Propagate only along declared prerequisite edges, never the whole lab.
        changed = True
        while changed:
            changed = False
            for job in self.jobs.values():
                if (not job["stale"] and job["production"] and
                        not set(job["requires"]) <= self.closed_gates):
                    self._mark_stale(job)
                    changed = True

    def invalidate(self, dependency: str, version: str) -> None:
        require(bool(dependency) and bool(version), "dependency version required")
        self.dependencies[dependency] = version
        for j in self.jobs.values():
            if dependency in j["dependencies"] and j["dependencies"][dependency] != version:
                self._mark_stale(j)
        self._invalidate_required_gates()
        self.consult("DEPENDENCY")

    def pause(self, *, end: bool = False) -> None:
        require(self.phase == "ACTIVE", "no active session to stop")
        self.phase = "ENDED" if end else "PAUSED"
        for j in self.jobs.values():
            if j["worker_state"] not in {"STOPPED", "NOT_STARTED"}:
                j["worker_state"] = "UNKNOWN"
            # Unconfirmed paths remain quarantined in self.leases.
        # User STOP never depends on a dispatcher response.

    def stopped(self, ident: str, worker: str, receipt: str) -> None:
        j = self.jobs[ident]
        require(bool(worker) and worker == j["worker_id"] and bool(receipt), "actual cessation acknowledgement required")
        require(not any(x["parent"] == ident and x["worker_state"] != "STOPPED"
                        for x in self.jobs.values()), "a descendant may still write")
        j.update(worker_state="STOPPED", stop_receipt=receipt)
        if j["status"] in {"RUNNING", "ASSIGNED", "ROUTING_MISMATCH"}:
            j["status"] = "CANCELLED"
        for p in j["paths"]:
            if self.leases.get(p) == ident:
                del self.leases[p]

    def receive(self, ident: str, revision: int, payload: Any, claimed_hash: str) -> bool:
        require(bool(ident) and revision > 0, "handoff ID/revision required")
        require(digest(payload) == claimed_hash, "handoff content hash mismatch")
        key = (ident, revision)
        if key in self.intake:
            require(self.intake[key] == claimed_hash, "conflicting same-revision handoff")
            return False
        previous = [r for i, r in self.intake if i == ident]
        require(revision == (max(previous) + 1 if previous else 1), "handoff revision must be sequential")
        self.intake[key] = claimed_hash
        return True

    def snapshot(self) -> dict[str, Any]:
        return copy.deepcopy({"mode": "SIMULATION", "phase": self.phase,
                              "session": self.session, "goal": self.contract["goal"],
                              "contract_hash": self.contract_hash, "jobs": self.jobs,
                              "leases": self.leases, "astra_spent": self.astra_spent,
                              "seconds_spent": self.seconds_spent,
                              "proved_gates": sorted(self.closed_gates),
                              "refuted_gates": sorted(self.refuted_gates)})


def validate_current(data: dict[str, Any]) -> None:
    require(len(json.dumps(data).encode()) <= LIMIT_BYTES, "current state exceeds 16 KiB")
    require(data.get("schema_version") == 1, "unsupported current-state schema")
    require(data.get("mode") in {"UNAVAILABLE", "LIVE", "SIMULATION"}, "explicit runtime mode required")
    require(data.get("phase") in {"NOT_STARTED", "ACTIVE", "PAUSED", "ENDED", "RECONCILE"}, "invalid session phase")
    workers = data.get("workers", [])
    require(isinstance(workers, list) and len(workers) <= 12, "invalid worker inventory")
    require(len(data.get("pending", [])) <= 32, "archive resolved history, never active leases")
    ids: set[str] = set()
    for worker in workers:
        require(worker["state"] in WORKER_STATES, "unknown worker state")
        require(worker["id"] not in ids and bool(worker["id"]), "duplicate/empty worker identity")
        ids.add(worker["id"])
        require(bool(worker.get("requested_model")) and bool(worker.get("observed_model")), "use UNKNOWN, not omitted model facts")
        require(bool(worker.get("requested_effort")) and bool(worker.get("observed_effort")),
                "use UNKNOWN, not omitted effort facts")
        if worker["state"] == "RUNNING":
            require(worker["observed_model"] in {"UNKNOWN", worker["requested_model"]} and
                    worker["observed_effort"] in {"UNKNOWN", worker["requested_effort"]},
                    "known routing mismatch must be quarantined, not RUNNING")
            require(data["mode"] == "LIVE" and data["phase"] == "ACTIVE" and
                    bool(data.get("session")) and worker.get("session") == data.get("session") and bool(worker.get("receipt")),
                    "RUNNING requires current live session and actual receipt")
    owners: set[str] = set()
    for lease in data.get("leases", []):
        require(exact_path(lease["path"]) and lease["path"] not in owners, "duplicate/invalid lease")
        owners.add(lease["path"])
        require(lease["owner"] in ids, "lease owner missing from worker inventory")
        require(lease["state"] in {"HELD", "FROZEN", "QUARANTINED"}, "invalid lease state")
    if any(item.get("id") == "INDEPENDENT-REVIEW" and item.get("state") != "DONE"
           for item in data.get("pending", []) if isinstance(item, dict)):
        require(data["phase"] != "ACTIVE", "pending policy review blocks live adoption")
    if data.get("legacy_reconciliation", {}).get("required"):
        require(data["phase"] != "ACTIVE", "legacy reconciliation must precede activation")


def check_repository(root: Path, *, inventory: dict[str, str] | None = None) -> list[str]:
    """inventory supports a connector-only changed-file snapshot, explicitly.

    Missing immutable files can be checked for existence/SHA in that inventory;
    their contents are NOT parsed or claimed as locally verified.
    """
    config = tomllib.loads((root / ".codex/config.toml").read_text())
    require(config["model"] == LUNA and config["model_reasoning_effort"] == "high", "primary changed")
    agents = config["agents"]
    require(agents["max_concurrent_threads_per_session"] == 12, "global cap drift")
    require(agents["default_subagent_model"] == SOL and
            agents["default_subagent_reasoning_effort"] == "high", "normal child default changed")
    checked = []
    for name, entry in agents.items():
        if not isinstance(entry, dict):
            continue
        path = ".codex/" + entry["config_file"]
        target = root / path
        if not target.exists():
            require(inventory is not None and path in inventory, f"missing role: {path}")
            checked.append(f"{name}: remote inventory only")
            continue
        role = tomllib.loads(target.read_text())
        require(role["name"] == name, f"role registration mismatch: {name}")
        require(bool(role.get("developer_instructions")), f"missing role instructions: {name}")
        if name == "implementer":
            require(role.get("model") == LUNA and role.get("model_reasoning_effort") == "high", "implementation floor drift")
        if name == "astra_prover":
            require(role.get("model") == ASTRA and "model_reasoning_effort" not in role, "Astra override path/pin drift")
        checked.append(f"{name}: parsed")
    require("astra_prover" in agents and "implementation_escalation" in agents, "both Astra roles must share policy")
    entrypoint = root / "AGENTS.md"
    require(entrypoint.is_file(), "missing required repository entrypoint: AGENTS.md")
    active = ["AGENTS.md", "rules/agent-orchestration.md",
              "rules/research-lab.md", "rules/orchestration-budget.md",
              ".codex/agents/prover.toml", ".codex/agents/astra-prover.toml",
              ".codex/agents/implementer.toml", ".codex/agents/next-action-selector.toml",
              ".codex/agents/implementation-escalation.toml"]
    override = root / "AGENTS.override.md"
    if override.exists() or override.is_symlink():
        active.insert(1, "AGENTS.override.md")
    for path in active:
        text = (root / path).read_text()
        require("goal-driven-sprints.md" in text, f"missing active policy route: {path}")
    for name in ("yulang-research-loop", "yulang-next-action", "yulang-sprint"):
        p = root / f".agents/skills/{name}/SKILL.md"
        text = p.read_text()
        require(text.startswith(f"---\nname: {name}\ndescription: ") and "\n---\n" in text,
                f"invalid skill frontmatter: {name}")
        require("every action boundary" not in text, f"legacy cadence: {name}")
        ui = (p.parent / "agents/openai.yaml").read_text()
        require("allow_implicit_invocation: true" in ui and f"${name}" in ui,
                f"skill UI routing missing: {name}")
        require("every action boundary" not in ui, f"legacy UI cadence: {name}")
    state = json.loads((root / "tasks/agent-loop/current.json").read_text())
    validate_current(state)
    require(len((root / "tasks/agent-loop/board.md").read_bytes()) <= 4096, "navigation board grew into history")
    seed = json.loads((root / "tasks/agent-loop/sprints/call-contextual-effects.json").read_text())
    require(seed["status"] == "CANDIDATE" and bool(seed["unresolved_before_activation"]), "seed must not pretend to be executable")
    require(set(seed["lanes"]) == {"proof", "implementation"}, "both seed lanes required")
    require(seed["resources"]["astra_concurrent"] == 1 and seed["resources"]["astra_assignments"] == 2,
            "seed Astra budget drift")
    checked.append("entrypoints, skill metadata, compact state and candidate: checked")
    return checked


def simulation() -> list[str]:
    s = SprintModel("SIMULATION-parent", "fixture-only", ["proof.md", "impl.rs"])
    s.begin("SIMULATION-session-1")
    s.assign("P", "proof", ["proof.md"], ["construct", "apply to parent"],
             role="astra_prover", model=ASTRA, effort="medium")
    s.assign("I", "implementation", ["impl.rs"], ["generate", "propagate", "execute"],
             role="implementer", model=LUNA)
    s.launch("P", "SIMULATION-astra", "SIMULATION-launch-P", s.session)
    s.launch("I", "SIMULATION-luna", "SIMULATION-launch-I", s.session)
    lines = ["SIMULATION ONLY: no agents, compiler execution or real receipts.",
             "Proof RUNNING + implementation RUNNING; effective models UNKNOWN."]
    s.step("P", "fixture lemma", "removes one parent premise")
    s.step("I", "fixture source path", "generation reaches propagation")
    lines.append(f"Internal successors retain {s.contract['goal']}; dispatcher consultations={len(s.consultations)}.")
    s.block("P", "fixture foreign-continuation premise", "SIMULATION-block")
    s.step("I", "fixture propagation", "independent path still advances")
    lines.append("Proof BLOCKED; independent implementation continues.")
    s.pause(end=True)
    lines.append("Session end: unconfirmed workers UNKNOWN; both leases retained.")
    s.begin("SIMULATION-session-2")
    require(all(j["worker_state"] != "RUNNING" for j in s.jobs.values()), "resurrection bug")
    lines.append("Resume: no automatic RUNNING state or reset of Astra budget.")
    return lines


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("check", "simulate"))
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--inventory", type=Path, help="explicit remote SHA inventory for a partial connector snapshot")
    args = parser.parse_args()
    try:
        if args.command == "simulate":
            for line in simulation():
                print(line)
        else:
            inventory = json.loads(args.inventory.read_text()) if args.inventory else None
            for line in check_repository(args.root, inventory=inventory):
                print(line)
            print("STATIC CHECK PASS (not independent review or live execution)")
    except (ProtocolError, OSError, KeyError, TypeError, json.JSONDecodeError,
            tomllib.TOMLDecodeError) as exc:
        print(f"CHECK FAILED: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
