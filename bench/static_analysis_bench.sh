#!/usr/bin/env bash
set -euo pipefail

main() {
    local repeat=1
    local release=1
    local run_vm=1
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
            --debug)
                release=0
                shift
                ;;
            --infer-only)
                run_vm=0
                shift
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
            examples/showcase.yu
            examples/06_undet_once.yu
            examples/07_junction.yu
            examples/10_effect_handler.yu
            examples/13_console.yu
        )
    fi

    print_header

    local case_path
    for case_path in "${cases[@]}"; do
        run_case "$repeat" "$release" "$run_vm" "$case_path"
    done
}

run_case() {
    local repeat="$1"
    local release="$2"
    local run_vm="$3"
    local case_path="$4"
    local out_file time_file
    out_file="$(mktemp)"
    time_file="$(mktemp)"

    local -a cargo_args=(run -p yulang)
    if [[ "$release" == "1" ]]; then
        cargo_args+=(--release)
    fi
    cargo_args+=(--)
    cargo_args+=(--infer-phase-timings)
    if [[ "$run_vm" == "1" ]]; then
        cargo_args+=(--runtime-phase-timings)
    fi
    cargo_args+=(--profile-repeat "$repeat")
    if [[ "$run_vm" == "1" ]]; then
        cargo_args+=(run "$case_path")
    else
        cargo_args+=(check "$case_path")
    fi

    if ! env RUSTC_WRAPPER="${RUSTC_WRAPPER:-}" RUST_MIN_STACK="${RUST_MIN_STACK:-67108864}" \
        /usr/bin/time -p -o "$time_file" cargo "${cargo_args[@]}" >"$out_file" 2>&1
    then
        print_failed_row "$case_path"
        tail -n 20 "$out_file" >&2
        rm -f "$out_file" "$time_file"
        return
    fi

    local real lower finalize render runtime_lower mono vm_compile vm_eval static_ms specs
    local std_lower entry_lower resolve_path apply_suffix act_bind lower_block root_rewrite intern_body
    real="$(metric_from_time real "$time_file")"
    lower="$(phase_metric "lower" "$out_file")"
    finalize="$(phase_metric "finalize" "$out_file")"
    render="$(phase_metric "render" "$out_file")"
    runtime_lower="$(phase_metric "runtime_lower" "$out_file")"
    mono="$(phase_metric "monomorphize" "$out_file")"
    vm_compile="$(phase_metric "vm_compile" "$out_file")"
    vm_eval="$(phase_metric "vm_eval" "$out_file")"
    static_ms="$(sum_ms "$lower" "$finalize" "$render" "$runtime_lower" "$mono" "$vm_compile")"
    specs="$(mono_specializations "$out_file")"
    std_lower="$(group_metric "std" "lower_roots" "$out_file")"
    entry_lower="$(group_metric "entry" "lower_roots" "$out_file")"
    resolve_path="$(phase_metric "detail.resolve_path_expr" "$out_file")"
    apply_suffix="$(phase_metric "detail.apply_suffix" "$out_file")"
    act_bind="$(phase_metric "detail.lower_act_body_bindings" "$out_file")"
    lower_block="$(phase_metric "detail.lower_expr_atom_block" "$out_file")"
    root_rewrite="$(mono_timing_metric "root-rewrite" "$out_file")"
    intern_body="$(mono_timing_metric "intern-rewrite-body" "$out_file")"

    printf "%-30s %8s %8s %8s %8s %8s %8s %8s %8s %8s %7s %8s %8s %8s %8s %8s %8s %8s %8s\n" \
        "$case_path" "$real" "$lower" "$finalize" "$render" \
        "$runtime_lower" "$mono" "$vm_compile" "$vm_eval" "$static_ms" "$specs" \
        "$std_lower" "$entry_lower" "$resolve_path" "$apply_suffix" "$act_bind" \
        "$lower_block" "$root_rewrite" "$intern_body"

    rm -f "$out_file" "$time_file"
}

print_header() {
    printf "%-30s %8s %8s %8s %8s %8s %8s %8s %8s %8s %7s %8s %8s %8s %8s %8s %8s %8s %8s\n" \
        "case" "real" "lower" "final" "render" "rt_low" "mono" "vm_c" "vm_e" \
        "static" "specs" "std_low" "ent_low" "resolve" "suffix" "act_bind" \
        "block" "root_rw" "intern"
}

print_failed_row() {
    local case_path="$1"
    printf "%-30s %8s %8s %8s %8s %8s %8s %8s %8s %8s %7s %8s %8s %8s %8s %8s %8s %8s %8s\n" \
        "$case_path" "FAILED" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-" "-"
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

group_metric() {
    local group="$1"
    local name="$2"
    local path="$3"
    local line
    line="$(grep -E "^[[:space:]]+${group}:" "$path" | head -n 1 || true)"
    if [[ -z "$line" || "$line" != *"$name="* ]]; then
        echo "-"
        return
    fi
    echo "$line" | sed -E "s/.*${name}=([^[:space:]]+).*/\1/"
}

mono_timing_metric() {
    local name="$1"
    local path="$2"
    local line
    line="$(grep -E "^[[:space:]]+timings:" "$path" | head -n 1 || true)"
    if [[ -z "$line" || "$line" != *"$name="* ]]; then
        echo "-"
        return
    fi
    echo "$line" | sed -E "s/.*${name}=([^,]+).*/\1/"
}

sum_ms() {
    awk '
        function to_ms(value, number) {
            if (value == "-") return 0
            number = value + 0
            if (value ~ /ns$/) return number / 1000000
            if (value ~ /us$/) return number / 1000
            if (value ~ /ms$/) return number
            if (value ~ /s$/) return number * 1000
            return number
        }
        {
            total = 0
            for (i = 1; i <= NF; i++) total += to_ms($i)
            printf "%.3fms", total
        }
    ' <<<"$*"
}

mono_specializations() {
    local path="$1"
    local line
    line="$(grep -E "^[[:space:]]+mono_passes:" "$path" | head -n 1 || true)"
    if [[ -z "$line" ]]; then
        echo "-"
        return
    fi
    echo "$line" | sed -E "s/.*specializations: ([0-9]+).*/\1/"
}

print_usage() {
    cat <<'EOF'
usage: bench/static_analysis_bench.sh [--repeat N] [--debug] [--infer-only] [case.yu ...]

Runs representative Yulang programs through:
  cargo run -p yulang --release -- \
    --infer-phase-timings --runtime-phase-timings run

Use --infer-only for cases that are useful to typecheck but not safe to run.

Columns:
  real    wall clock from /usr/bin/time
  lower   source collect/parse/lower/infer timing
  final   compact/finalize timing
  render  infer result rendering timing
  rt_low  Core IR -> runtime IR lowering
  mono    principal elaboration / monomorphize
  vm_c    VM compile
  vm_e    VM eval
  static  lower + final + render + rt_low + mono + vm_c
  specs   monomorphize specializations
  std_low std source lower_roots time
  ent_low entry source lower_roots time
  resolve detail.resolve_path_expr cumulative time
  suffix  detail.apply_suffix cumulative time
  act_bind detail.lower_act_body_bindings cumulative time
  block   detail.lower_expr_atom_block cumulative time
  root_rw principal-elaborate root-rewrite timing
  intern  principal-elaborate intern-rewrite-body timing
EOF
}

main "$@"
