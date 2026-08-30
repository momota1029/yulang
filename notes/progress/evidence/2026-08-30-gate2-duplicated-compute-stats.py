import csv
import math
import random
import statistics
from collections import defaultdict
from pathlib import Path

ROOT = Path("/tmp/yulang-gate2-final.TM8ChV")
META = ROOT / "ordinary/measured/meta.tsv"
SEED = 20260830
RESAMPLES = 100_000
CASES = [
    "indented_ast_1k",
    "indented_ast_10k",
    "indented_direct_1k",
    "indented_direct_10k",
    "braced_ast_1k",
    "braced_ast_10k",
    "braced_direct_1k",
    "braced_direct_10k",
]


def wall_seconds(raw: str) -> float:
    parts = raw.split(":")
    if len(parts) == 2:
        return int(parts[0]) * 60 + float(parts[1])
    if len(parts) == 3:
        return int(parts[0]) * 3600 + int(parts[1]) * 60 + float(parts[2])
    raise ValueError(raw)


with META.open(newline="") as handle:
    rows = list(csv.DictReader(handle, delimiter="\t"))

by_attempt = defaultdict(list)
for row in rows:
    by_attempt[(int(row["round"]), int(row["attempt"]))].append(row)

accepted_attempt = {}
for round_number in range(1, 25):
    valid_attempts = []
    for (candidate_round, attempt), attempt_rows in by_attempt.items():
        if candidate_round != round_number:
            continue
        if len(attempt_rows) == 16 and all(row["valid"] == "1" for row in attempt_rows):
            valid_attempts.append(attempt)
    if len(valid_attempts) != 1:
        raise RuntimeError(f"round {round_number}: accepted attempts {valid_attempts}")
    accepted_attempt[round_number] = valid_attempts[0]

accepted_rows = [
    row
    for row in rows
    if int(row["attempt"]) == accepted_attempt[int(row["round"])]
]

pair_rows = []
values = defaultdict(lambda: {"BC": [], "CB": []})
for case_id in CASES:
    for round_number in range(1, 25):
        selected = [
            row
            for row in accepted_rows
            if row["case"] == case_id and int(row["round"]) == round_number
        ]
        if len(selected) != 2:
            raise RuntimeError(f"{case_id} round {round_number}: {len(selected)} rows")
        subjects = {row["subject"]: row for row in selected}
        baseline = subjects["baseline"]
        candidate = subjects["candidate"]
        stratum = "BC" if round_number % 2 else "CB"
        expected_pair = ("baseline", "candidate") if stratum == "BC" else ("candidate", "baseline")
        actual_pair = tuple(row["subject"] for row in sorted(selected, key=lambda row: int(row["pair_order"])))
        if actual_pair != expected_pair:
            raise RuntimeError(f"{case_id} round {round_number}: pair order {actual_pair}")
        baseline_wall = wall_seconds(baseline["wall_raw"])
        candidate_wall = wall_seconds(candidate["wall_raw"])
        baseline_rss = int(baseline["rss_kb"])
        candidate_rss = int(candidate["rss_kb"])
        wall_log_ratio = math.log(candidate_wall / baseline_wall)
        rss_difference = candidate_rss - baseline_rss
        values[case_id][stratum].append((wall_log_ratio, rss_difference))
        pair_rows.append(
            {
                "case": case_id,
                "round": round_number,
                "attempt": accepted_attempt[round_number],
                "stratum": stratum,
                "baseline_wall_s": f"{baseline_wall:.2f}",
                "candidate_wall_s": f"{candidate_wall:.2f}",
                "wall_log_ratio": f"{wall_log_ratio:.12f}",
                "baseline_rss_kb": baseline_rss,
                "candidate_rss_kb": candidate_rss,
                "rss_difference_kb": rss_difference,
                "baseline_raw": baseline["raw_file"],
                "candidate_raw": candidate["raw_file"],
            }
        )

with (ROOT / "ordinary/measured/accepted_pairs.tsv").open("w", newline="") as handle:
    writer = csv.DictWriter(handle, fieldnames=pair_rows[0].keys(), delimiter="\t")
    writer.writeheader()
    writer.writerows(pair_rows)

rng = random.Random(SEED)
summaries = []
for case_id in CASES:
    bc_wall = [value[0] for value in values[case_id]["BC"]]
    cb_wall = [value[0] for value in values[case_id]["CB"]]
    bc_rss = [value[1] for value in values[case_id]["BC"]]
    cb_rss = [value[1] for value in values[case_id]["CB"]]
    if not (len(bc_wall) == len(cb_wall) == len(bc_rss) == len(cb_rss) == 12):
        raise RuntimeError(f"{case_id}: stratum cardinality")
    median_bc_wall = statistics.median(bc_wall)
    median_cb_wall = statistics.median(cb_wall)
    wall_effect = (median_bc_wall + median_cb_wall) / 2
    median_bc_rss = statistics.median(bc_rss)
    median_cb_rss = statistics.median(cb_rss)
    rss_effect = (median_bc_rss + median_cb_rss) / 2
    boot_wall = []
    boot_rss = []
    for _ in range(RESAMPLES):
        sample_bc_indices = [rng.randrange(12) for _ in range(12)]
        sample_cb_indices = [rng.randrange(12) for _ in range(12)]
        boot_wall.append(
            (
                statistics.median(bc_wall[index] for index in sample_bc_indices)
                + statistics.median(cb_wall[index] for index in sample_cb_indices)
            )
            / 2
        )
        boot_rss.append(
            (
                statistics.median(bc_rss[index] for index in sample_bc_indices)
                + statistics.median(cb_rss[index] for index in sample_cb_indices)
            )
            / 2
        )
    boot_wall.sort()
    boot_rss.sort()
    lower_index = int(0.05 * RESAMPLES)
    wall_lower = boot_wall[lower_index]
    rss_lower = boot_rss[lower_index]
    summaries.append(
        {
            "case": case_id,
            "median_BC_wall_log_ratio": f"{median_bc_wall:.12f}",
            "median_CB_wall_log_ratio": f"{median_cb_wall:.12f}",
            "wall_effect_log_ratio": f"{wall_effect:.12f}",
            "wall_effect_percent": f"{math.expm1(wall_effect) * 100:.6f}",
            "wall_one_sided_95_lower": f"{wall_lower:.12f}",
            "wall_lower_percent": f"{math.expm1(wall_lower) * 100:.6f}",
            "median_BC_rss_difference_kb": f"{median_bc_rss:.1f}",
            "median_CB_rss_difference_kb": f"{median_cb_rss:.1f}",
            "rss_effect_kb": f"{rss_effect:.1f}",
            "rss_one_sided_95_lower_kb": f"{rss_lower:.1f}",
            "wall_rollback": str(wall_lower > 0).lower(),
            "rss_rollback": str(rss_lower > 0).lower(),
        }
    )

with (ROOT / "ordinary/measured/statistics.tsv").open("w", newline="") as handle:
    writer = csv.DictWriter(handle, fieldnames=summaries[0].keys(), delimiter="\t")
    writer.writeheader()
    writer.writerows(summaries)

with (ROOT / "ordinary/measured/statistics_method.txt").open("w") as handle:
    handle.write(
        "seed=20260830\n"
        "prng=Python random.Random (MT19937)\n"
        "resamples=100000\n"
        "strata=12 BC odd rounds, 12 CB even rounds\n"
        "effect=(median(BC)+median(CB))/2\n"
        "lower_bound=sorted bootstrap replicate at zero-based index 5000 (empirical 5th percentile)\n"
    )

print("accepted_attempts", accepted_attempt)
for summary in summaries:
    print(summary)
