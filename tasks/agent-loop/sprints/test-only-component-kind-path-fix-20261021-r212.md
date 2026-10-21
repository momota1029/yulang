# Sprint R212 — Test-only ComponentKind path repair

Status: ACTIVE, primary-only bounded compile repair.

## Goal

Repair the R211 test-only visibility error using the compiler-identified public `yu_types::ComponentKind` path, then run the already-authorized read-only source-owner alias and mapped-bound query once. No inference behavior changes.

## Exact scope

Read the R211 note and contract, and R210 note. Edit only this contract, `crates/yu-solver/src/shadow_apply/local_source_observation.rs` (test-only type path), `notes/theory/2026-10-21-r212-source-owner-alias-readback.md`, and current.json. No production changes or frozen R183 edits; no subagents.

## Validation

One targeted Cargo process maximum under `target/r212-source-owner-alias/`; no retry. The query reads exact representatives for Effect(10)/Effect(31), retained Capture bounds/snapshots and the existing route inputs. Remove scratch at closeout.
