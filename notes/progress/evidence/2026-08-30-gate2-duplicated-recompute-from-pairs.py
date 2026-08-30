import csv
import math
import random
import statistics
import sys
from collections import defaultdict
from pathlib import Path


EVIDENCE_DIR = Path(__file__).resolve().parent
PAIRS = EVIDENCE_DIR / "2026-08-30-gate2-duplicated-accepted-pairs.tsv"
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


with PAIRS.open(newline="") as handle:
    rows = list(csv.DictReader(handle, delimiter="\t"))

values = defaultdict(lambda: {"BC": [], "CB": []})
for row in rows:
    values[row["case"]][row["stratum"]].append(
        (float(row["wall_log_ratio"]), int(row["rss_difference_kb"]))
    )

rng = random.Random(SEED)
fieldnames = [
    "case",
    "wall_effect_percent",
    "wall_lower_percent_index_4999",
    "wall_lower_percent_index_5000",
    "rss_effect_kb",
    "rss_lower_kb_index_4999",
    "rss_lower_kb_index_5000",
]
writer = csv.DictWriter(sys.stdout, fieldnames=fieldnames, delimiter="\t")
writer.writeheader()

for case_id in CASES:
    bc_wall = [value[0] for value in values[case_id]["BC"]]
    cb_wall = [value[0] for value in values[case_id]["CB"]]
    bc_rss = [value[1] for value in values[case_id]["BC"]]
    cb_rss = [value[1] for value in values[case_id]["CB"]]
    if not (len(bc_wall) == len(cb_wall) == len(bc_rss) == len(cb_rss) == 12):
        raise RuntimeError(f"{case_id}: stratum cardinality")

    wall_effect = (statistics.median(bc_wall) + statistics.median(cb_wall)) / 2
    rss_effect = (statistics.median(bc_rss) + statistics.median(cb_rss)) / 2
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
    writer.writerow(
        {
            "case": case_id,
            "wall_effect_percent": f"{math.expm1(wall_effect) * 100:.6f}",
            "wall_lower_percent_index_4999": f"{math.expm1(boot_wall[4999]) * 100:.6f}",
            "wall_lower_percent_index_5000": f"{math.expm1(boot_wall[5000]) * 100:.6f}",
            "rss_effect_kb": f"{rss_effect:.1f}",
            "rss_lower_kb_index_4999": f"{boot_rss[4999]:.1f}",
            "rss_lower_kb_index_5000": f"{boot_rss[5000]:.1f}",
        }
    )
