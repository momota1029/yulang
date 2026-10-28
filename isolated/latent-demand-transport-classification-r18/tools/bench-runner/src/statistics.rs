use std::collections::BTreeMap;

use crate::report::{
    AggregateGroup, AggregateWallTime, Aggregates, Availability, DistributionSummary,
    WorkloadResult,
};

pub fn summarize(values: &[u64]) -> DistributionSummary {
    assert!(!values.is_empty(), "summary requires at least one sample");
    let mut sorted = values.to_vec();
    sorted.sort_unstable();
    let median = median_u64(&sorted);
    let mut deviations: Vec<_> = sorted
        .iter()
        .map(|value| ((*value as f64) - median).abs())
        .collect();
    deviations.sort_by(f64::total_cmp);
    let p95_index = ((sorted.len() as f64 * 0.95).ceil() as usize)
        .saturating_sub(1)
        .min(sorted.len() - 1);

    DistributionSummary {
        sample_count: sorted.len(),
        min: sorted[0],
        median,
        mad: median_f64(&deviations),
        p95: sorted[p95_index],
        max: *sorted.last().expect("nonempty values"),
    }
}

pub fn summarize_available(
    values: impl IntoIterator<Item = Option<u64>>,
) -> Availability<DistributionSummary> {
    let values: Option<Vec<_>> = values.into_iter().collect();
    match values {
        Some(values) if !values.is_empty() => Availability::available(summarize(&values)),
        _ => Availability::unavailable("resource usage is unavailable on this platform"),
    }
}

pub fn aggregate(results: &[WorkloadResult]) -> Aggregates {
    let medians: Vec<_> = results
        .iter()
        .map(|result| result.summary.wall_time_ns.median)
        .collect();
    let mut categories: BTreeMap<String, Vec<f64>> = BTreeMap::new();
    let mut subsets: BTreeMap<String, Vec<f64>> = BTreeMap::new();
    for result in results {
        categories
            .entry(result.category.clone())
            .or_default()
            .push(result.summary.wall_time_ns.median);
        for subset in &result.subsets {
            subsets
                .entry(subset.clone())
                .or_default()
                .push(result.summary.wall_time_ns.median);
        }
    }

    Aggregates {
        workload_count: results.len(),
        wall_time: AggregateWallTime {
            median_of_workload_medians_ns: median_f64_sorted_copy(&medians),
            geometric_mean_of_workload_medians_ns: geometric_mean(&medians),
        },
        categories: aggregate_groups(categories),
        subsets: aggregate_groups(subsets),
    }
}

fn aggregate_groups(groups: BTreeMap<String, Vec<f64>>) -> BTreeMap<String, AggregateGroup> {
    groups
        .into_iter()
        .map(|(name, values)| {
            (
                name,
                AggregateGroup {
                    workload_count: values.len(),
                    geometric_mean_of_medians_ns: geometric_mean(&values),
                },
            )
        })
        .collect()
}

fn geometric_mean(values: &[f64]) -> f64 {
    if values.is_empty() || values.iter().any(|value| *value <= 0.0) {
        return 0.0;
    }
    (values.iter().map(|value| value.ln()).sum::<f64>() / values.len() as f64).exp()
}

fn median_u64(sorted: &[u64]) -> f64 {
    let midpoint = sorted.len() / 2;
    if sorted.len() % 2 == 0 {
        (sorted[midpoint - 1] as f64 + sorted[midpoint] as f64) / 2.0
    } else {
        sorted[midpoint] as f64
    }
}

fn median_f64(sorted: &[f64]) -> f64 {
    let midpoint = sorted.len() / 2;
    if sorted.len() % 2 == 0 {
        (sorted[midpoint - 1] + sorted[midpoint]) / 2.0
    } else {
        sorted[midpoint]
    }
}

fn median_f64_sorted_copy(values: &[f64]) -> f64 {
    if values.is_empty() {
        return 0.0;
    }
    let mut sorted = values.to_vec();
    sorted.sort_by(f64::total_cmp);
    median_f64(&sorted)
}

#[cfg(test)]
mod tests {
    use super::summarize;

    #[test]
    fn summary_uses_nearest_rank_p95_and_median_absolute_deviation() {
        let summary = summarize(&[1, 2, 3, 4, 100]);
        assert_eq!(summary.median, 3.0);
        assert_eq!(summary.mad, 1.0);
        assert_eq!(summary.p95, 100);
    }
}
