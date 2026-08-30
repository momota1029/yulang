#!/usr/bin/env bash
set -u

root=/tmp/yulang-gate2-final.TM8ChV
baseline="$root/baseline/target/debug/deps/yu_syntax-cda0f60d5589725d"
candidate=/home/momot/rust/yulang/target/debug/deps/yu_syntax-cda0f60d5589725d
test_name=grammar::expression::tests::gate2_statement_sequence_performance_harness
phase=${1:?phase must be warmup or measured}
mkdir -p "$root/ordinary/$phase/raw" "$root/ordinary/$phase/invalid"
meta="$root/ordinary/$phase/meta.tsv"
anomalies="$root/ordinary/$phase/anomalies.log"

if [[ ! -e "$meta" ]]; then
    printf 'timestamp\tphase\tround\tattempt\tcase\tcase_order\tsubject\tpair_order\titems\trepeats\twall_raw\trss_kb\texit\taffinity\tvalid\traw_file\tcommand\n' >"$meta"
fi

cases=(
    indented_ast_1k
    indented_ast_10k
    indented_direct_1k
    indented_direct_10k
    braced_ast_1k
    braced_ast_10k
    braced_direct_1k
    braced_direct_10k
)

contention_snapshot() {
    ps -eo pid=,ppid=,comm=,args= | awk '
        $3 == "cargo" || $3 == "rustc" || $3 ~ /^yu_syntax/ { print }
    '
}

run_one() {
    local round=$1 attempt=$2 case_id=$3 case_order=$4 subject=$5 pair_order=$6
    local path size items repeats binary timestamp raw affinity exit_status wall rss valid command
    path=${case_id%_*}
    size=${case_id##*_}
    if [[ "$size" == 1k ]]; then
        items=1000
        repeats=50
    else
        items=10000
        repeats=8
    fi
    binary=$baseline
    if [[ "$subject" == candidate ]]; then
        binary=$candidate
    fi
    timestamp=$(date --iso-8601=ns)
    raw="$root/ordinary/$phase/raw/${phase}_r$(printf '%02d' "$round")_a${attempt}_o$(printf '%02d' "$case_order")_${case_id}_${subject}.raw"
    if [[ "$phase" == measured ]]; then
        printf -v command 'taskset -c 10 /usr/bin/time -v env YULANG_GATE2_SEQUENCE_CASE=%q YULANG_GATE2_SEQUENCE_ITEMS=%q YULANG_GATE2_SEQUENCE_REPEATS=%q %q --ignored --exact %q --nocapture' "$path" "$items" "$repeats" "$binary" "$test_name"
    else
        printf -v command 'taskset -c 10 env YULANG_GATE2_SEQUENCE_CASE=%q YULANG_GATE2_SEQUENCE_ITEMS=%q YULANG_GATE2_SEQUENCE_REPEATS=%q %q --ignored --exact %q --nocapture' "$path" "$items" "$repeats" "$binary" "$test_name"
    fi
    {
        printf 'timestamp=%s\n' "$timestamp"
        printf 'phase=%s round=%s attempt=%s case=%s case_order=%s subject=%s pair_order=%s\n' "$phase" "$round" "$attempt" "$case_id" "$case_order" "$subject" "$pair_order"
        printf 'command=%s\n' "$command"
        printf '%s\n' '--- raw output ---'
    } >"$raw"

    local before
    before=$(contention_snapshot)
    if [[ -n "$before" ]]; then
        printf '%s pre-run contention round=%s attempt=%s case=%s subject=%s\n%s\n' "$(date --iso-8601=ns)" "$round" "$attempt" "$case_id" "$subject" "$before" >>"$anomalies"
        return 2
    fi

    if [[ "$phase" == measured ]]; then
        (
            exec taskset -c 10 /usr/bin/time -v env \
                YULANG_GATE2_SEQUENCE_CASE="$path" \
                YULANG_GATE2_SEQUENCE_ITEMS="$items" \
                YULANG_GATE2_SEQUENCE_REPEATS="$repeats" \
                "$binary" --ignored --exact "$test_name" --nocapture
        ) >>"$raw" 2>&1 &
    else
        (
            exec taskset -c 10 env \
                YULANG_GATE2_SEQUENCE_CASE="$path" \
                YULANG_GATE2_SEQUENCE_ITEMS="$items" \
                YULANG_GATE2_SEQUENCE_REPEATS="$repeats" \
                "$binary" --ignored --exact "$test_name" --nocapture
        ) >>"$raw" 2>&1 &
    fi
    local runner=$!
    affinity=unobserved
    for _ in $(seq 1 100); do
        if [[ -r "/proc/$runner/status" ]]; then
            affinity=$(awk '/^Cpus_allowed_list:/ { print $2 }' "/proc/$runner/status")
            if [[ "$affinity" == 10 ]]; then
                break
            fi
        else
            break
        fi
    done

    local contention_file="$raw.contention"
    (
        while kill -0 "$runner" 2>/dev/null; do
            ps -eo pid=,ppid=,comm=,args= | awk -v runner="$runner" '
                ($3 == "cargo" || $3 == "rustc") { print; next }
                $3 ~ /^yu_syntax/ && $1 != runner && $2 != runner { print }
            '
            sleep 0.05
        done
    ) >"$contention_file" &
    local monitor=$!

    wait "$runner"
    exit_status=$?
    wait "$monitor" 2>/dev/null || true

    wall=NA
    rss=NA
    if [[ "$phase" == measured ]]; then
        wall=$(sed -n 's/^[[:space:]]*Elapsed (wall clock) time (h:mm:ss or m:ss): //p' "$raw" | tail -1)
        rss=$(sed -n 's/^[[:space:]]*Maximum resident set size (kbytes): //p' "$raw" | tail -1)
    fi
    valid=1
    if [[ "$exit_status" -ne 0 || "$affinity" != 10 ]]; then
        valid=0
    fi
    if ! rg -q 'test result: ok\. 1 passed; 0 failed' "$raw"; then
        valid=0
    fi
    if [[ "$phase" == measured && ( -z "$wall" || "$wall" == NA || -z "$rss" || "$rss" == NA ) ]]; then
        valid=0
    fi
    if [[ -s "$contention_file" ]]; then
        valid=0
        printf '%s in-run contention round=%s attempt=%s case=%s subject=%s\n' "$(date --iso-8601=ns)" "$round" "$attempt" "$case_id" "$subject" >>"$anomalies"
        sed 's/^/  /' "$contention_file" >>"$anomalies"
    fi
    rm -f "$contention_file"

    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$timestamp" "$phase" "$round" "$attempt" "$case_id" "$case_order" "$subject" "$pair_order" \
        "$items" "$repeats" "$wall" "$rss" "$exit_status" "$affinity" "$valid" "$raw" "$command" >>"$meta"
    [[ "$valid" == 1 ]]
}

if [[ "$phase" == warmup ]]; then
    first_round=1
    final_round=2
else
    first_round=1
    final_round=24
fi

round=$first_round
invalid_count=0
while (( round <= final_round )); do
    attempt=1
    while true; do
        round_valid=1
        if (( round % 2 == 1 )); then
            case_indices=(0 1 2 3 4 5 6 7)
            subjects=(baseline candidate)
        else
            case_indices=(7 6 5 4 3 2 1 0)
            subjects=(candidate baseline)
        fi
        order=0
        for case_index in "${case_indices[@]}"; do
            ((order+=1))
            pair_order=0
            for subject in "${subjects[@]}"; do
                ((pair_order+=1))
                if ! run_one "$round" "$attempt" "${cases[$case_index]}" "$order" "$subject" "$pair_order"; then
                    round_valid=0
                    break 2
                fi
            done
            sleep 5
        done
        if [[ "$round_valid" == 1 ]]; then
            printf '%s phase=%s completed_round=%s invalid_count=%s\n' "$(date --iso-8601=seconds)" "$phase" "$round" "$invalid_count" | tee -a "$root/ordinary/$phase/progress.log"
            break
        fi
        ((invalid_count+=1))
        printf '%s phase=%s invalidated_round=%s attempt=%s invalid_count=%s\n' "$(date --iso-8601=seconds)" "$phase" "$round" "$attempt" "$invalid_count" | tee -a "$root/ordinary/$phase/progress.log"
        ((attempt+=1))
        sleep 5
    done
    ((round+=1))
done

printf '%s phase=%s complete invalid_count=%s\n' "$(date --iso-8601=seconds)" "$phase" "$invalid_count" | tee -a "$root/ordinary/$phase/progress.log"
