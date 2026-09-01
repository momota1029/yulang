# Gate 10 public companion measurement — raw artifacts

This file preserves the direct stdout and `/usr/bin/time -v` output for every
invocation attempted in the Gate 10 candidate-only measurement.  Each stderr
capture was empty (SHA-256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`).
The commands, candidate identity, protocol, classification, and summaries are
recorded in the paired measurement report.

## Invalid pre-sample 1 — contention detected

During this in-flight launch, the Gate 10 prebuild's `cargo test -p yu-syntax
--locked --no-run` and its `rustc --crate-name yu_syntax` child were observed.
The launch was interrupted and excluded.  Its stdout did not contain a kernel
marker.

```text
running 1 test
test tests::gate10_public_production_companion_performance_harness ...
```

```text
Command terminated by signal 2
	Command being timed: "timeout --foreground 60s taskset -c 10 target/debug/deps/yu_syntax-bcf5c27414ab47ba --exact tests::gate10_public_production_companion_performance_harness --ignored --nocapture --test-threads=1"
	User time (seconds): 40.33
	System time (seconds): 0.15
	Percent of CPU this job got: 100%
	Elapsed (wall clock) time (h:mm:ss or m:ss): 0:40.38
	Average shared text size (kbytes): 0
	Average unshared data size (kbytes): 0
	Average stack size (kbytes): 0
	Average total size (kbytes): 0
	Maximum resident set size (kbytes): 14632
	Average resident set size (kbytes): 0
	Major (requiring I/O) page faults: 2
	Minor (reclaiming a frame) page faults: 2112
	Voluntary context switches: 8
	Involuntary context switches: 72
	Swaps: 0
	File system inputs: 80
	File system outputs: 8
	Socket messages sent: 0
	Socket messages received: 0
	Signals delivered: 0
	Page size (bytes): 4096
	Exit status: 0
```

## Invalid pre-sample 2 — initial timeout too short

```text
running 1 test
test tests::gate10_public_production_companion_performance_harness ...
```

```text
Command exited with non-zero status 124
	Command being timed: "timeout --foreground 60s taskset -c 10 target/debug/deps/yu_syntax-67577d316539ca9e --exact tests::gate10_public_production_companion_performance_harness --ignored --nocapture --test-threads=1"
	User time (seconds): 61.00
	System time (seconds): 0.24
	Percent of CPU this job got: 99%
	Elapsed (wall clock) time (h:mm:ss or m:ss): 1:01.40
	Average shared text size (kbytes): 0
	Average unshared data size (kbytes): 0
	Average stack size (kbytes): 0
	Average total size (kbytes): 0
	Maximum resident set size (kbytes): 18208
	Average resident set size (kbytes): 0
	Major (requiring I/O) page faults: 0
	Minor (reclaiming a frame) page faults: 3311
	Voluntary context switches: 6
	Involuntary context switches: 217
	Swaps: 0
	File system inputs: 0
	File system outputs: 8
	Socket messages sent: 0
	Socket messages received: 0
	Signals delivered: 0
	Page size (bytes): 4096
	Exit status: 124
```

## Accepted warm-up

```text
running 1 test
test tests::gate10_public_production_companion_performance_harness ... GATE10_PUBLIC_PRODUCTION_COMPANION_KERNEL_SECONDS=81.566441980
ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 579 filtered out; finished in 82.28s
```

```text
	Command being timed: "target/debug/deps/yu_syntax-67577d316539ca9e --exact tests::gate10_public_production_companion_performance_harness --ignored --nocapture --test-threads=1"
	User time (seconds): 84.69
	System time (seconds): 0.24
	Percent of CPU this job got: 100%
	Elapsed (wall clock) time (h:mm:ss or m:ss): 1:24.37
	Average shared text size (kbytes): 0
	Average unshared data size (kbytes): 0
	Average stack size (kbytes): 0
	Average total size (kbytes): 0
	Maximum resident set size (kbytes): 24356
	Average resident set size (kbytes): 0
	Major (requiring I/O) page faults: 95
	Minor (reclaiming a frame) page faults: 7497
	Voluntary context switches: 73
	Involuntary context switches: 124
	Swaps: 0
	File system inputs: 16296
	File system outputs: 16
	Socket messages sent: 0
	Socket messages received: 0
	Signals delivered: 0
	Page size (bytes): 4096
	Exit status: 0
```

## Accepted measured sample 1

```text
running 1 test
test tests::gate10_public_production_companion_performance_harness ... GATE10_PUBLIC_PRODUCTION_COMPANION_KERNEL_SECONDS=84.642035955
ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 579 filtered out; finished in 85.22s
```

```text
	Command being timed: "target/debug/deps/yu_syntax-67577d316539ca9e --exact tests::gate10_public_production_companion_performance_harness --ignored --nocapture --test-threads=1"
	User time (seconds): 88.21
	System time (seconds): 0.12
	Percent of CPU this job got: 99%
	Elapsed (wall clock) time (h:mm:ss or m:ss): 1:28.75
	Average shared text size (kbytes): 0
	Average unshared data size (kbytes): 0
	Average stack size (kbytes): 0
	Average total size (kbytes): 0
	Maximum resident set size (kbytes): 24484
	Average resident set size (kbytes): 0
	Major (requiring I/O) page faults: 0
	Minor (reclaiming a frame) faults: 7556
	Voluntary context switches: 2
	Involuntary context switches: 117
	Swaps: 0
	File system inputs: 0
	File system outputs: 16
	Socket messages sent: 0
	Socket messages received: 0
	Signals delivered: 0
	Page size (bytes): 4096
	Exit status: 0
```

## Accepted measured sample 2

```text
running 1 test
test tests::gate10_public_production_companion_performance_harness ... GATE10_PUBLIC_PRODUCTION_COMPANION_KERNEL_SECONDS=89.266634450
ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 579 filtered out; finished in 89.82s
```

```text
	Command being timed: "target/debug/deps/yu_syntax-67577d316539ca9e --exact tests::gate10_public_production_companion_performance_harness --ignored --nocapture --test-threads=1"
	User time (seconds): 92.97
	System time (seconds): 0.18
	Percent of CPU this job got: 99%
	Elapsed (wall clock) time (h:mm:ss or m:ss): 1:33.42
	Average shared text size (kbytes): 0
	Average unshared data size (kbytes): 0
	Average stack size (kbytes): 0
	Average total size (kbytes): 0
	Maximum resident set size (kbytes): 24356
	Average resident set size (kbytes): 0
	Major (requiring I/O) page faults: 0
	Minor (reclaiming a frame) faults: 7555
	Voluntary context switches: 2
	Involuntary context switches: 144
	Swaps: 0
	File system inputs: 0
	File system outputs: 16
	Socket messages sent: 0
	Socket messages received: 0
	Signals delivered: 0
	Page size (bytes): 4096
	Exit status: 0
```

## Accepted measured sample 3

```text
running 1 test
test tests::gate10_public_production_companion_performance_harness ... GATE10_PUBLIC_PRODUCTION_COMPANION_KERNEL_SECONDS=86.740094588
ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 579 filtered out; finished in 87.23s
```

```text
	Command being timed: "target/debug/deps/yu_syntax-67577d316539ca9e --exact tests::gate10_public_production_companion_performance_harness --ignored --nocapture --test-threads=1"
	User time (seconds): 90.39
	System time (seconds): 0.11
	Percent of CPU this job got: 99%
	Elapsed (wall clock) time (h:mm:ss or m:ss): 1:30.86
	Average shared text size (kbytes): 0
	Average unshared data size (kbytes): 0
	Average stack size (kbytes): 0
	Average total size (kbytes): 0
	Maximum resident set size (kbytes): 24484
	Average resident set size (kbytes): 0
	Major (requiring I/O) page faults: 0
	Minor (reclaiming a frame) faults: 7556
	Voluntary context switches: 2
	Involuntary context switches: 129
	Swaps: 0
	File system inputs: 0
	File system outputs: 16
	Socket messages sent: 0
	Socket messages received: 0
	Signals delivered: 0
	Page size (bytes): 4096
	Exit status: 0
```
