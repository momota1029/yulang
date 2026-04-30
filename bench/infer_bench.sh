#!/usr/bin/env bash
set -euo pipefail

main() {
    local repeat=1
    local -a cases=()

    while (($# > 0)); do
        case "$1" in
            --repeat)
                if (($# < 2)); then
                    echo "missing value for --repeat" >&2
                    exit 2
                fi
                repeat="$2"
                shift 2
                ;;
            --help|-h)
                print_usage
                exit 0
                ;;
            --)
                shift
                while (($# > 0)); do
                    cases+=("$1")
                    shift
                done
                ;;
            -*)
                echo "unknown option: $1" >&2
                print_usage >&2
                exit 2
                ;;
            *)
                cases+=("$1")
                shift
                ;;
        esac
    done

    if ((${#cases[@]} == 0)); then
        cases=(
            bench/infer_simple.yu
            bench/chain_1000.yu
        )
    fi

    printf "%-22s %8s %10s %10s %10s %10s %10s\n" \
        "case" "real(s)" "finalize" "commit" "compact" "subst" "constrain"

    local case_path
    for case_path in "${cases[@]}"; do
        run_case "$repeat" "$case_path"
        echo
    done
}

run_case() {
    local repeat="$1"
    local case_path="$2"
    local out_file time_file
    out_file="$(mktemp)"
    time_file="$(mktemp)"

    /usr/bin/time -p -o "$time_file" \
        cargo run -p yulang --release -- \
        --infer --infer-phase-timings --profile-repeat "$repeat" "$case_path" \
        >"$out_file" 2>&1

    local real finalize commit compact subst constrain
    real="$(metric_from_time real "$time_file")"
    finalize="$(phase_metric finalize "$out_file")"
    commit="$(phase_metric commit_ready "$out_file")"
    compact="$(phase_metric compact "$out_file")"
    subst="$(phase_metric instantiate_subst_body "$out_file")"
    constrain="$(phase_metric instantiate_constrain "$out_file")"

    printf "%-22s %8s %10s %10s %10s %10s %10s\n" \
        "$case_path" "$real" "$finalize" "$commit" "$compact" "$subst" "$constrain"

    rm -f "$out_file" "$time_file"
}

phase_metric() {
    local name="$1"
    local path="$2"
    local line
    line="$(grep -E "^[[:space:]]+${name}:" "$path" | head -n 1 || true)"
    if [[ -z "$line" ]]; then
        echo "-"
        return
    fi
    echo "$line" | sed -E "s/^[[:space:]]+${name}:[[:space:]]+([^[:space:]]+).*/\1/"
}

metric_from_time() {
    local name="$1"
    local path="$2"
    awk -v key="$name" '$1 == key { print $2 }' "$path"
}

print_usage() {
    cat <<'EOF'
usage: bench/infer_bench.sh [--repeat N] [case.yu ...]

If no cases are given, runs a small mixed suite:
  bench/infer_simple.yu
  bench/chain_1000.yu
EOF
}

main "$@"
