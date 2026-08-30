#!/usr/bin/env bash
set -u

root=/tmp/yulang-gate2-final.TM8ChV
binary=/home/momot/rust/yulang/target/debug/deps/yu_syntax-cda0f60d5589725d
out="$root/candidate_samples"
mkdir -p "$out/raw"
meta="$out/meta.tsv"
anomalies="$out/anomalies.log"
printf 'timestamp\tfamily\tcase\titems\trepeats\tsample\tattempt\twall_raw\trss_kb\texit\taffinity\tvalid\traw_file\tcommand\n' >"$meta"

companion_cases=(
    indented_ast
    indented_direct
    braced_ast
    braced_direct
    indented_ast_comment_stress
    indented_direct_comment_stress
    braced_ast_comment_stress
    braced_direct_comment_stress
)

contention_snapshot() {
    ps -eo pid=,ppid=,comm=,args= | awk '
        $3 == "cargo" || $3 == "rustc" || $3 ~ /^yu_syntax/ { print }
    '
}

run_sample() {
    local family=$1 case_id=$2 items=$3 repeats=$4 sample=$5 attempt=$6
    local test_name case_var items_var repeats_var timestamp raw command before runner affinity monitor contention_file exit_status wall rss valid
    if [[ "$family" == companion ]]; then
        test_name=grammar::declaration::companion::tests::gate2_statement_only_companion_performance_harness
        case_var=YULANG_GATE2_COMPANION_CASE
        items_var=YULANG_GATE2_COMPANION_ITEMS
        repeats_var=YULANG_GATE2_COMPANION_REPEATS
    else
        test_name=grammar::expression::tests::gate2_statement_sequence_performance_harness
        case_var=YULANG_GATE2_SEQUENCE_CASE
        items_var=YULANG_GATE2_SEQUENCE_ITEMS
        repeats_var=YULANG_GATE2_SEQUENCE_REPEATS
    fi
    timestamp=$(date --iso-8601=ns)
    raw="$out/raw/${family}_${case_id}_${items}_s${sample}_a${attempt}.raw"
    printf -v command 'taskset -c 10 /usr/bin/time -v env %s=%q %s=%q %s=%q %q --ignored --exact %q --nocapture' "$case_var" "$case_id" "$items_var" "$items" "$repeats_var" "$repeats" "$binary" "$test_name"
    {
        printf 'timestamp=%s\n' "$timestamp"
        printf 'family=%s case=%s items=%s repeats=%s sample=%s attempt=%s\n' "$family" "$case_id" "$items" "$repeats" "$sample" "$attempt"
        printf 'command=%s\n' "$command"
        printf '%s\n' '--- raw output ---'
    } >"$raw"

    before=$(contention_snapshot)
    if [[ -n "$before" ]]; then
        printf '%s pre-run contention family=%s case=%s items=%s sample=%s attempt=%s\n%s\n' "$(date --iso-8601=ns)" "$family" "$case_id" "$items" "$sample" "$attempt" "$before" >>"$anomalies"
        return 2
    fi

    (
        exec taskset -c 10 /usr/bin/time -v env \
            "$case_var=$case_id" "$items_var=$items" "$repeats_var=$repeats" \
            "$binary" --ignored --exact "$test_name" --nocapture
    ) >>"$raw" 2>&1 &
    runner=$!
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

    contention_file="$raw.contention"
    (
        while kill -0 "$runner" 2>/dev/null; do
            ps -eo pid=,ppid=,comm=,args= | awk -v runner="$runner" '
                ($3 == "cargo" || $3 == "rustc") { print; next }
                $3 ~ /^yu_syntax/ && $1 != runner && $2 != runner { print }
            '
            sleep 0.05
        done
    ) >"$contention_file" &
    monitor=$!
    wait "$runner"
    exit_status=$?
    wait "$monitor" 2>/dev/null || true

    wall=$(sed -n 's/^[[:space:]]*Elapsed (wall clock) time (h:mm:ss or m:ss): //p' "$raw" | tail -1)
    rss=$(sed -n 's/^[[:space:]]*Maximum resident set size (kbytes): //p' "$raw" | tail -1)
    valid=1
    if [[ "$exit_status" -ne 0 || "$affinity" != 10 || -z "$wall" || -z "$rss" ]]; then
        valid=0
    fi
    if ! rg -q 'test result: ok\. 1 passed; 0 failed' "$raw"; then
        valid=0
    fi
    if [[ -s "$contention_file" ]]; then
        valid=0
        printf '%s in-run contention family=%s case=%s items=%s sample=%s attempt=%s\n' "$(date --iso-8601=ns)" "$family" "$case_id" "$items" "$sample" "$attempt" >>"$anomalies"
        sed 's/^/  /' "$contention_file" >>"$anomalies"
    fi
    rm -f "$contention_file"
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$timestamp" "$family" "$case_id" "$items" "$repeats" "$sample" "$attempt" "$wall" "$rss" "$exit_status" "$affinity" "$valid" "$raw" "$command" >>"$meta"
    [[ "$valid" == 1 ]]
}

for family in companion ordinary; do
    if [[ "$family" == companion ]]; then
        active_cases=("${companion_cases[@]}")
    else
        active_cases=(indented_direct_comment_stress)
    fi
    for case_id in "${active_cases[@]}"; do
        for items in 1000 10000; do
            if [[ "$items" == 1000 ]]; then repeats=50; else repeats=8; fi
            for sample in 1 2 3; do
                attempt=1
                while ! run_sample "$family" "$case_id" "$items" "$repeats" "$sample" "$attempt"; do
                    printf '%s invalid family=%s case=%s items=%s sample=%s attempt=%s\n' "$(date --iso-8601=seconds)" "$family" "$case_id" "$items" "$sample" "$attempt" | tee -a "$out/progress.log"
                    ((attempt+=1))
                    sleep 5
                done
                printf '%s complete family=%s case=%s items=%s sample=%s\n' "$(date --iso-8601=seconds)" "$family" "$case_id" "$items" "$sample" | tee -a "$out/progress.log"
                sleep 5
            done
        done
    done
done

printf '%s candidate_samples_complete\n' "$(date --iso-8601=seconds)" | tee -a "$out/progress.log"
