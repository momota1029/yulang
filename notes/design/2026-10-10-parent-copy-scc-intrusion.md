# Parent-copy SCC intrusion: current user decision

Status: Authoritative within the operation explicitly selected below
Scope: extrusion parent retention and same-SCC parent/copy equality in the successor
Approved-by: user, directly in the working conversation
Approved-at: current conversation; exact message timestamp unavailable
Baseline: `7334dcfdb6f9d57eff04f02fb575fbba1ef1b414`
Supersedes: earlier unselected-operation assumptions only; no full cutover approval
Mechanism review: implementation packet under bounded architect review

## Direct decision

The user clarified that intrusion is the operation used to process SCCs, then
defined it directly:

> extrusionではfreshな変数がfreshでない変数を参照したときにコピーを行うわけですが，このとき親を覚えておきます．そしてSCC内にこの変数同士が入った場合，型変数を親に戻します（正確には親とイコールになります）．これがintrusionです．

After the primary restated parent/copy retention and equality, the user instructed:

> では入れてください

This is direct implementation authorization, not a pending answer-board handoff.
Do not demand another approval for this already selected operation.

## Selected operation and compiler responsibility

Retain the actual parent when extrusion creates a copy. When that copy and its
parent enter the same SCC, equate the type variable with its parent. Equality
must affect actual solving and later use, not just an observation or printed
name. Parent provenance is recorded at creation, not reconstructed from IDs,
levels or matching endpoints.

The implementation must connect this operation to actual successor SCC
processing. Merely leaving recursive internal uses rejected, or adding unused
parent metadata, does not satisfy the requested implementation.

Value/effect kind, polarity-specific copies, bounds, lexical levels, shared
captures, fresh-use independence and transactional state remain concrete
correctness responsibilities. The bounded mechanism review resolves data
structures and integration against those requirements; it does not replace the
user's operation with a different one to simplify a proof.

## Retained boundary

The full inference/F5 replacement objective remains active. Complete Call,
effects/protection and source/public correspondence retain their contracts.
This decision does not by itself prove soundness, principality, recursive
acceptance or target-branch replacement. Frozen `main` remains untouched; the
current implementation branch is `research/simple-sub-intrusion`.
